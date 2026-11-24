"""Emit one exact, relaxed nine-leaf formula subproblem. Does not run a solver."""
import argparse
import json
from functools import lru_cache
from pathlib import Path
from tempfile import TemporaryDirectory
import runpy

other = runpy.run_path(str(Path(__file__).with_name('graph1343-shard13-cuts.py')))
EDGES, MIS = other['EDGES'], other['MAX_INDEPENDENT']
LEAF = ('leaf', ())
COUNTS = (18,16,17,15,16,17,17,17,19,19,19)


@lru_cache(None)
def shapes(n):
    if n == 1:
        return (LEAF,)
    result = set()
    for left_size in range(1, n // 2 + 1):
        for a in shapes(left_size):
            for b in shapes(n-left_size):
                for op in ('and', 'or'):
                    children = sorted([v for t in (a,b) for v in (t[1] if t[0]==op else (t,))])
                    # Two sibling OR leaves are one OR leaf on all retained
                    # rows and would contradict the eight-color bound.
                    if op == 'or' and children.count(LEAF) > 1:
                        continue
                    result.add((op,tuple(children)))
    return tuple(sorted(result))


def clause_count(tree):
    op, children = tree
    if op == 'leaf':
        return 1
    counts = [clause_count(t) for t in children]
    if op == 'and':
        return sum(counts)
    n = 1
    for child in counts:
        n *= child
    return n


def has_cherry(tree):
    op, children = tree
    return ((op=='and' and children.count(LEAF)>=2)
            or any(has_cherry(t) for t in children))


def row_data(center, domain):
    pos = [1<<a | 1<<b for a,b in EDGES if center not in (a,b)]
    labels = [u for u in range(11) if domain == 'original' or u != center]
    if domain == 'original':
        neg = MIS
    else:
        neg = [bits for bits in range(1<<11) if not bits>>center&1
               and not other['positive'](bits)
               and all(bits>>u&1 or other['positive'](bits|1<<u) for u in labels)]
        assert len(neg) == COUNTS[center]
    return labels, pos, neg


def cnf(center, tree, domain='original', leaf_vars=None):
    clauses = []
    next_var = 1
    labels, pos, neg = row_data(center,domain)
    rows = pos + neg
    positives = len(pos)

    def new():
        nonlocal next_var
        v=next_var
        next_var+=1
        return v

    def equiv(z, op, inputs):
        if op == 'or':
            clauses.append([-z]+inputs)
            clauses.extend([[z,-v] for v in inputs])
        else:
            clauses.append([z]+[-v for v in inputs])
            clauses.extend([[-z,v] for v in inputs])

    def node(t):
        op, children=t
        if op == 'leaf':
            selectors=[new() for _ in labels]
            if leaf_vars is not None:
                leaf_vars.append(list(zip(labels,selectors)))
            result=[]
            for row in rows:
                z=new()
                equiv(z,'or',[v for j,v in zip(labels,selectors) if row>>j&1])
                result.append(z)
            return result
        inputs=[node(child) for child in children]
        result=[]
        for values in zip(*inputs):
            z=new()
            equiv(z,op,list(values))
            result.append(z)
        return result

    result=node(tree)
    clauses.extend([[z] if j<positives else [-z] for j,z in enumerate(result)])
    return next_var-1,clauses


def decode(path, center, domain, index, tree):
    leaves = []
    n, clauses = cnf(center,tree,domain,leaves)
    values = {}
    for line in path.read_text().splitlines():
        fields = line.split()
        if not fields or fields[0] != 'v':
            continue
        for token in fields[1:]:
            lit = int(token)
            if lit:
                var, value = abs(lit), lit > 0
                if not 1 <= var <= n or (var in values and values[var] != value):
                    raise ValueError(f'inconsistent model variable {var}')
                values[var] = value
    if len(values) != n:
        raise ValueError('expected a full DIMACS model with v-prefixed assignment lines')
    if any(not any(values[abs(lit)] == (lit>0) for lit in clause) for clause in clauses):
        raise ValueError('assignment violates the generated CNF')
    selected = iter([[u for u,var in pins if values[var]] for pins in leaves])

    def instantiate(t):
        op,children = t
        if op=='leaf':
            return ('support',next(selected))
        return (op,[instantiate(child) for child in children])

    witness=instantiate(tree)
    def evaluate(t,bits):
        op,a=t
        if op=='support':
            return any(bits>>u&1 for u in a)
        combine=all if op=='and' else any
        return combine(evaluate(child,bits) for child in a)

    _,pos,neg=row_data(center,domain)
    if not all(evaluate(witness,bits) for bits in pos) or any(evaluate(witness,bits) for bits in neg):
        raise ValueError('decoded formula failed the selected frontier')
    for bits in range(1<<11):
        if not bits>>center&1 and evaluate(witness,bits)!=other['positive'](bits):
            raise ValueError(f'decoded formula failed the induced graph on row {bits}')
    return {'center':center,'domain':domain,'shape_index':index,
            'positive_frontier':len(pos),'negative_frontier':len(neg),
            'verified_induced_inputs':1024,'formula':witness}


def self_test(center):
    edges=[e for e in EDGES if center not in e]
    tree=('or',tuple(('and',(LEAF,LEAF)) for edge in edges))
    for domain in ('original','induced'):
        labels,pos,neg=row_data(center,domain)
        rows=pos+neg
        intended=iter(u for edge in edges for u in edge)
        assignment=[]

        def evaluate_control(t):
            op,children=t
            if op=='leaf':
                u=next(intended)
                assignment.extend(v==u for v in labels)
                out=[bool(bits>>u&1) for bits in rows]
            else:
                child_values=[evaluate_control(child) for child in children]
                combine=all if op=='and' else any
                out=[combine(bits) for bits in zip(*child_values)]
            assignment.extend(out)
            return out

        evaluate_control(tree)
        n,clauses=cnf(center,tree,domain)
        assert len(assignment)==n
        lits=[i if value else -i for i,value in enumerate(assignment,1)]
        with TemporaryDirectory() as directory:
            control=Path(directory)/'known-formula.model'
            control.write_text('v '+' '.join(str(lit) for lit in lits)+' 0\n')
            result=decode(control,center,domain,-1,tree)
            assert result['verified_induced_inputs']==1024
        print(f'{domain}: known formula validates {len(clauses)} clauses, '
              f'{len(pos)} positive and {len(neg)} negative frontier rows, and 1024 induced inputs')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--center', type=int, required=True, choices=range(11))
    parser.add_argument('--index', type=int)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--domain',choices=['original','induced'],default='original')
    parser.add_argument('--model',type=Path,help='verify and decode a full DIMACS SAT solver model')
    parser.add_argument('--self-test',action='store_true')
    args=parser.parse_args()
    if args.self_test:
        self_test(args.center)
        return
    eligible=[s for s in shapes(9) if has_cherry(s) and clause_count(s)>=COUNTS[args.center]]
    if args.index is None:
        print(f'center {args.center}: {len(eligible)} zero-based shapes')
        return
    if not 0<=args.index<len(eligible) or (args.output is None)==(args.model is None):
        parser.error('choose an eligible shape index and exactly one of --output or --model')
    if args.model:
        print(json.dumps(decode(args.model,args.center,args.domain,args.index,eligible[args.index])))
        return
    n,cs=cnf(args.center,eligible[args.index],args.domain)
    # Exclusive creation protects any existing witness or certificate file.
    with args.output.open('x',encoding='ascii') as out:
        out.write(f'p cnf {n} {len(cs)}\n')
        for c in cs:
            out.write(' '.join(map(str,c))+' 0\n')
    print(f'center {args.center}, shape {args.index}: {n} variables, {len(cs)} clauses')


if __name__=='__main__':
    main()
