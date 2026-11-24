"""Position-defined shards of the November 23 public table, L-meta-1343/1342.

A dirty AND is true on some independent set. By monotonicity, checking every
maximal independent set is equivalent. Pin order can be normalized because both
operators commute. No sorting between gates, liveness assumptions, or mandatory
second dirty gate are used. Add nullary ORs after a short circuit, leaving its
output unchanged. This preserves the position of the first dirty AND.
"""
import argparse
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess

POINTS = 11
EDGES = ((0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7),
         (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9))
EDGE_ROWS = tuple((1 << a) | (1 << b) for a, b in EDGES)


def edge_value(bits):
    return any(bits & edge == edge for edge in EDGE_ROWS)


def maximal_independent(bits):
    return not edge_value(bits) and all(
        bits & (1 << p) or edge_value(bits | (1 << p)) for p in range(POINTS))


def run_cadical(path, binary, timeout, proof):
    # External CaDiCaL emits a DRAT certificate when a proof pathname is given.
    cmd = [binary, '-q']
    if timeout:
        cmd += ['-t', str(timeout)]
    cmd.append(str(path))
    if proof:
        if proof.exists():
            raise ValueError('proof path already exists')
        cmd.append(str(proof))
    try:
        proc = subprocess.run(cmd, text=True, capture_output=True,
                              timeout=timeout + 15 if timeout else None)
    except subprocess.TimeoutExpired:
        return 'UNKNOWN', []
    lines = proc.stdout.splitlines()
    status = [line.strip() for line in lines if line.startswith('s ')]
    if proc.returncode == 10 and status == ['s SATISFIABLE']:
        return 'SAT', [int(tok) for line in lines if line.startswith('v ') for tok in line.split()[1:] if tok != '0']
    if proc.returncode == 20 and status == ['s UNSATISFIABLE']:
        return 'UNSAT', []
    if proc.returncode in (0, 124) and status in ([], ['s UNKNOWN'], ['s INDETERMINATE']):
        return 'UNKNOWN', []
    raise RuntimeError(f'CaDiCaL exit {proc.returncode}, status {status}: {proc.stderr[-500:]}')





class FixedPosition:
    def new(self):
        self.nvars += 1
        return self.nvars

    def add(self, *lits):
        if self.true not in lits:
            self.clauses.append([lit for lit in lits if lit != -self.true])

    def one_hot(self, size):
        # prefix[i] means that a choice with index <= i was made.
        choices = [self.new() for _ in range(size)]
        prefixes = [choices[0]]
        for choice in choices[1:]:
            prev, here = prefixes[-1], self.new()
            self.add(-prev, here)
            self.add(-choice, here)
            self.add(-prev, -choice)
            self.add(-here, prev, choice)
            prefixes.append(here)
        self.add(prefixes[-1])
        return choices, prefixes

    def mux(self, selections, values, out):
        for sel, value in zip(selections, values):
            self.add(-sel, -out, value)
            self.add(-sel, out, -value)

    def dimacs(self, path):
        with path.open('w', encoding='ascii') as f:
            f.write(f'p cnf {self.nvars} {len(self.clauses)}\n')
            for clause in self.clauses:
                f.write(' '.join(map(str, clause)) + ' 0\n')


    def __init__(self, position, size):
        self.input_order = list(range(POINTS))
        self.nvars, self.clauses, self.gate_data = 0, [], []
        self.true = self.new()
        self.clauses.append([self.true])
        self.bad, self.omit = 11+size, 12+size
        self.position = position
        negatives = [i for i in range(2048) if maximal_independent(i)]
        # Before the first dirty AND, every AND evaluates to false on every
        # independent set. Each OR-only portion on such an input therefore
        # evaluates to the disjunction of its singleton evaluations.
        singletons = [1 << p for p in range(11)]
        rows = list(EDGE_ROWS) + negatives + singletons
        start_single = len(EDGE_ROWS) + len(negatives)
        values = [[self.true if bits & (1<<p) else -self.true for p in self.input_order]
                  for bits in rows]
        for j in range(size):
            kind = self.new()
            wires = list(range(11+j)) + [self.bad,self.omit]
            left, lp = self.one_hot(len(wires))
            right, rp = self.one_hot(len(wires))
            for l, r in zip(lp,rp):
                self.add(-r,l)
            self.gate_data.append((kind,wires,left,right))
            negative_bits = []
            singleton_pins = []
            for i, current in enumerate(values):
                a,b,c = self.new(),self.new(),self.new()
                available = current + [-self.true,kind]
                self.mux(left,available,a)
                self.mux(right,available,b)
                self.add(-kind,-c,a)
                self.add(-kind,-c,b)
                self.add(-kind,c,-a,-b)
                self.add(kind,c,-a)
                self.add(kind,c,-b)
                self.add(kind,-c,a,b)
                current.append(c)
                if i >= start_single:
                    singleton_pins.append((a,b))
                if len(EDGE_ROWS) <= i < start_single:
                    negative_bits.append(c)
            if j < position:
                sg = [values[i][-1] for i in range(start_single,len(rows))]
                for mask,big in zip(negatives,negative_bits):
                    elements = [v for u,v in enumerate(sg) if mask & (1<<u)]
                    self.add(-big,*elements)
                    for v in elements:
                        self.add(-v,big)
                for u,(au,_) in enumerate(singleton_pins):
                    for v,(_,bv) in enumerate(singleton_pins):
                        if not edge_value((1<<u)|(1<<v)):
                            self.add(-kind,-au,-bv)
                for c in negative_bits:
                    self.add(-kind,-c)
            if j == position:
                self.add(kind)
                self.add(*negative_bits)
        self.outputs = list(range(11+size)) + [self.bad]
        self.output_sel, _ = self.one_hot(len(self.outputs))
        for i,current in enumerate(values):
            for sel, value in zip(self.output_sel,current+[-self.true]):
                self.add(-sel,value if i < len(EDGE_ROWS) else -value)

    def pin(self,circuit):
        if len(self.gate_data) != len(circuit['gates']):
            raise ValueError('wrong calibration size')
        for (kind,ws,left,right), gate in zip(self.gate_data,circuit['gates']):
            self.add(kind if gate['op']=='and' else -kind)
            pins = sorted(gate['inputs']+[self.omit]*(2-len(gate['inputs'])))
            self.add(left[ws.index(pins[0])])
            self.add(right[ws.index(pins[1])])
        self.add(self.output_sel[self.outputs.index(circuit['output'])])

    def replay(self,model):
        true = set(model)
        def select(flags,wires):
            chosen = [w for f,w in zip(flags,wires) if f in true]
            if len(chosen)!=1:
                raise ValueError('incomplete SAT assignment')
            return chosen[0]
        circuit = {'gates':[], 'output':select(self.output_sel,self.outputs)}
        for kind,ws,left,right in self.gate_data:
            if (kind in true) == (-kind in true):
                raise ValueError('incomplete operation')
            pins = [select(left,ws),select(right,ws)]
            circuit['gates'].append({'op':'and' if kind in true else 'or',
                                     'inputs':[p for p in pins if p!=self.omit]})
        dirty = set()
        for x in range(2048):
            vals = [bool(x & (1<<i)) for i in range(11)]
            target = any(vals[a] and vals[b] for a,b in EDGES)
            for j,gate in enumerate(circuit['gates']):
                args=[vals[p] if p<len(vals) else False for p in gate['inputs']]
                bit = all(args) if gate['op']=='and' else any(args)
                vals.append(bit)
                if bit and not target and gate['op']=='and':
                    dirty.add(j)
            out = circuit['output']
            if (vals[out] if out<len(vals) else False)!=target:
                raise ValueError('wrong truth table')
        if not dirty or min(dirty)!=self.position:
            raise ValueError('wrong position')
        return circuit, sorted(dirty)


def example(clean, position):
    gs = clean['gates']
    def renamed(p):
        return p + 2 if p >= 11+position else p
    before = gs[:position]
    new = [{'op':'and','inputs':[0,1]}, {'op':'and','inputs':[0,2]}]
    after = [{'op':g['op'],'inputs':[renamed(p) for p in g['inputs']]} for g in gs[position:]]
    return {'gates': before+new+after,'output':renamed(clean['output'])}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--position',type=int,choices=range(19),required=True)
    p.add_argument('--cadical',required=True)
    p.add_argument('--control',type=Path)
    p.add_argument('--bad-position',action='store_true')
    p.add_argument('--timeout',type=int,default=300)
    p.add_argument('--proof',type=Path)
    p.add_argument('--cnf',type=Path)
    p.add_argument('--witness',type=Path)
    a=p.parse_args()
    c = example(json.loads(a.control.read_text()),a.position+int(a.bad_position)) if a.control else None
    enc=FixedPosition(a.position,len(c['gates']) if c else 21)
    if c:
        enc.pin(c)
    with TemporaryDirectory() as td:
        cnf=a.cnf or Path(td)/'search.cnf'
        enc.dimacs(cnf)
        print('position',a.position,'vars',enc.nvars,'clauses',len(enc.clauses),flush=True)
        result,model=run_cadical(cnf,a.cadical,a.timeout,a.proof)
        print(result,flush=True)
        if c and result!=('UNSAT' if a.bad_position else 'SAT'):
            raise ValueError('calibration failed')
        if result=='SAT':
            decoded,dirty=enc.replay(model)
            print('full truth table verified; dirty positions',dirty)
            if a.witness:
                a.witness.write_text(json.dumps(decoded)+'\n')
            elif not c:
                print(json.dumps(decoded))
if __name__=='__main__':
    main()
