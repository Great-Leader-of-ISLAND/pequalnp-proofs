#!/usr/bin/env python3
"""Exact search for L-meta-670 (Petersen graph minus one vertex).
No fixed first gate. All nine inputs, 12 edges and all three gate types are
available. Every SAT candidate is evaluated independently on all 512 rows.

Raw mode: BAD represents any forward or out-of-range read (always false).
OMIT drops a pin; on a nullary gate AND is true, OR false, NOT true. The
second pin of a NOT is ignored by Lean and is dropped before encoding.
The two pins of an AND or OR can be sorted. Repetitions, constants, dangling
gates and arbitrary output indices are allowed. Append unused nullary ORs to
reach 15 gates without changing the output. Every model is a real circuit.

Normal mode: propagate constants and bypass copies, repeated pins and double
negations. Discard gates outside the output cone. This graph function is
nonconstant and is not a literal. Insert any needed unused NOT(x0) padding
before the genuine cone to reach 15. All other nonfinal gates have a user.
Choose each ready genuine gate by least (max operand,min operand); a newly
ready gate reads the just-issued index, so these keys never decrease. A NOT
has key (pin,pin); binary gates have two distinct ascending operands.

Optional graph symmetry in normal mode: among all relabellings by graph
automorphisms and valid sorted schedules choose one minimizing the first
genuine gate's key. Its key must be least in its orbit: otherwise relabel to
reduce it and reschedule; the original first gate remains ready, so the new
first key can only decrease. Padding can be dropped and reinserted. This
retains every orbit of circuits and does not choose a single gate operation
or pair type. --no-symmetry disables the orbit restriction.

A CEGAR step adds fresh counterexample rows. SAT means a full 512-row
witness; independently checked DRAT on any row subset proves exhaustion of
the encoded size bound. Only standard Python is needed with external CaDiCaL."""
import argparse
import json
import math
from pathlib import Path
import re
import subprocess
import time

N, K = 9, 15
EDGES = ((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
         (3,8),(5,7),(6,8),(8,5))
MASKS = tuple((1 << a) | (1 << b) for a,b in EDGES)


def target(row):
    return any(row & mask == mask for mask in MASKS)


def automorphisms():
    neighbors = [set() for _ in range(N)]
    for a,b in EDGES:
        neighbors[a].add(b)
        neighbors[b].add(a)
    images, result = [], []
    def extend():
        v = len(images)
        if v == N:
            result.append(tuple(images))
            return
        for q in range(N):
            if q in images or len(neighbors[v]) != len(neighbors[q]):
                continue
            if all((i in neighbors[v]) == (p in neighbors[q]) for i,p in enumerate(images)):
                images.append(q)
                extend()
                images.pop()
    extend()
    return result


def counterexamples(circuit, bound=K):
    """Independent scalar replay of official Lean semantics on every input."""
    gs, out = circuit['gates'], circuit['output']
    if not isinstance(gs,list) or not 0 <= len(gs) <= bound or type(out) is not int or out < 0:
        raise ValueError('invalid size/output')
    for g in gs:
        if g['op'] not in ('and','or','not') or not isinstance(g['inputs'],list) or len(g['inputs']) > 2:
            raise ValueError('invalid gate op/arity')
        if any(type(p) is not int or p < 0 for p in g['inputs']):
            raise ValueError('invalid wire index')
    bad = []
    for row in range(1 << N):
        values = [bool(row & (1 << v)) for v in range(N)]
        expected = any(values[a] and values[b] for a,b in EDGES)
        for g in gs:
            pins = [values[p] if p < len(values) else False for p in g['inputs']]
            op = g['op']
            values.append(all(pins) if op == 'and' else any(pins) if op == 'or'
                          else not (pins[0] if pins else False))
        if (values[out] if out < len(values) else False) != expected:
            bad.append(row)
    return bad


class Encoding:
    def __init__(self, mode, bound=K, symmetry=True):
        self.bad, self.omit = N+bound, N+bound+1
        perms = automorphisms() if symmetry and mode == 'normal' else []
        rejected = [(a,b) for a in range(N) for b in range(a,N)
                    if any((max(p[a],p[b]),min(p[a],p[b])) < (b,a) for p in perms)]
        self.mode, self.top, self.clauses, self.rows = mode, 0, [], []
        self.t = self.var()
        self.clauses.append([self.t])
        self.gs, self.dummies = [], []
        uses = [[] for _ in range(N+bound)]
        last_key = None
        for j in range(bound):
            and_, or_, not_ = [self.var() for _ in range(3)]
            self.add(and_,or_,not_)
            self.add(-and_,-or_); self.add(-and_,-not_); self.add(-or_,-not_)
            earlier = list(range(N+j))
            ls = earlier + ([self.bad,self.omit] if mode == 'raw' else [])
            rs = earlier + ([self.bad,self.omit] if mode == 'raw' else [self.omit])
            left, lp = self.one_hot(len(ls)); right, rp = self.one_hot(len(rs))
            self.add(-not_,right[-1])
            if mode == 'raw':
                for a,b in zip(lp,rp):
                    self.add(-b,a)
            else:
                self.add(not_,-right[-1])
                self.add(-right[0])
                for i in range(1,len(earlier)):
                    self.add(-right[i],lp[i-1])
                # A binary's maximum pin is right; a NOT's is left.
                high_le = []
                for a,b in zip(lp,rp[:len(earlier)]):
                    h = self.var()
                    self.select_value(not_,a,b,h)
                    high_le.append(h)
                if last_key is not None:
                    ph,pl = last_key
                    for i,prev in enumerate(ph):
                        self.add(-high_le[i],prev)
                    # Equal maxima imply nondecreasing minima. Encode equality
                    # via 'strictly greater somewhere' across prefix indicators.
                    strict = []
                    for hi,prev in zip(high_le,ph):
                        z=self.var(); strict.append(z)
                        self.add(-z,prev); self.add(-z,-hi); self.add(z,-prev,hi)
                    bigger = self.var()
                    self.add(-bigger,*strict)
                    for z in strict: self.add(-z,bigger)
                    for i,prev in enumerate(pl):
                        self.add(bigger,-lp[i],prev)
                last_key = (high_le,lp)
                dummy = self.var()
                if self.dummies:
                    self.add(-dummy,self.dummies[-1])
                # If this is the first genuine gate, permit every operation
                # but select only the least input-key in its automorphism orbit.
                guard = [dummy] + ([-self.dummies[-1]] if self.dummies else [])
                for a,b in rejected:
                    if a==b: self.add(*guard,-not_,-left[a])
                    else: self.add(*guard,-left[a],-right[b])
                self.dummies.append(dummy)
                self.add(-dummy,not_); self.add(-dummy,left[0])
                if j == bound-1: self.add(-dummy)
                for source,a,b in zip(earlier,left,right):
                    uses[source].extend((a,b))
                    if N <= source:
                        forbidden = self.dummies[source-N]
                        self.add(-forbidden,-a); self.add(-forbidden,-b)
            self.gs.append(((and_,or_,not_),ls,rs,left,right))
        if mode == 'normal':
            for v in range(N): self.add(*uses[v])
            for j in range(bound-1): self.add(self.dummies[j],*uses[N+j])
            self.outs, self.osel = [N+bound-1], [self.t]
        else:
            self.outs = list(range(N+bound))+[self.bad]
            self.osel,_ = self.one_hot(len(self.outs))

    def var(self):
        self.top += 1
        return self.top

    def add(self,*lits):
        if self.t not in lits:
            self.clauses.append([v for v in lits if v != -self.t])

    def one_hot(self,n):
        choices = [self.var() for _ in range(n)]
        ps = [choices[0]]
        for x in choices[1:]:
            a,h = ps[-1],self.var()
            self.add(-a,h); self.add(-x,h); self.add(-a,-x); self.add(-h,a,x)
            ps.append(h)
        self.add(ps[-1])
        return choices,ps

    def select_value(self,s,a,b,z):
        self.add(-s,-a,z); self.add(-s,a,-z); self.add(s,-b,z); self.add(s,b,-z)

    def mux(self,selectors,values):
        z = self.var()
        for s,v in zip(selectors,values):
            self.add(-s,-v,z); self.add(-s,v,-z)
        return z

    def add_row(self,row):
        if type(row) is not int or not 0 <= row < 1<<N or row in self.rows:
            raise ValueError('invalid or repeated refinement row')
        self.rows.append(row)
        vs = [self.t if row & (1<<i) else -self.t for i in range(N)]
        for (a,o,n),ls,rs,left,right in self.gs:
            def val(i):
                return -self.t if i == self.bad else a if i == self.omit else vs[i]
            x = self.mux(left,[val(i) for i in ls])
            y = self.mux(right,[val(i) for i in rs])
            z = self.var()
            self.add(-a,-z,x); self.add(-a,-z,y); self.add(-a,z,-x,-y)
            self.add(-o,z,-x); self.add(-o,z,-y); self.add(-o,-z,x,y)
            self.add(-n,-z,-x); self.add(-n,z,x)
            vs.append(z)
        wanted = target(row)
        for s,p in zip(self.osel,self.outs):
            v = vs[p] if p < len(vs) else -self.t
            self.add(-s,v if wanted else -v)

    def decode(self,model):
        positive = set(model)
        def pick(sel,items):
            hits = [x for x,s in zip(items,sel) if s in positive]
            if len(hits)!=1: raise ValueError('incomplete SAT model')
            return hits[0]
        gs=[]
        for ops,ls,rs,left,right in self.gs:
            ps=[pick(left,ls),pick(right,rs)]
            gs.append({'op':pick(ops,('and','or','not')),'inputs':[p for p in ps if p != self.omit]})
        return {'gates':gs,'output':pick(self.osel,self.outs)}

    def dimacs(self,path):
        with path.open('w',encoding='ascii') as f:
            f.write(f'p cnf {self.top} {len(self.clauses)}\n')
            f.writelines(' '.join(map(str,c))+' 0\n' for c in self.clauses)


def seed_rows(kind):
    if kind == 'full':
        return list(range(1<<N))
    if kind == 'tiny':
        return [0,(1<<N)-1] + list(MASKS[:3])
    negatives = [r for r in range(1<<N) if not target(r) and
                 all(r&(1<<i) or target(r|(1<<i)) for i in range(N))]
    return sorted({0,(1<<N)-1,*MASKS,*negatives,*(1<<i for i in range(N))})


def budget(end):
    if end is None: return None
    left = end-time.monotonic()
    if left <= 0: raise TimeoutError
    return left


def run_cadical(binary,cnf,proof,seconds,proof_enabled):
    cmd=[binary,'-q']
    if seconds is not None:
        cmd+=['-t',str(max(1,math.ceil(seconds)))]
    cmd.append(str(cnf))
    if proof_enabled: cmd.append(str(proof))
    try:
        proc=subprocess.run(cmd,capture_output=True,text=True,timeout=seconds)
    except subprocess.TimeoutExpired:
        return 'UNKNOWN', []
    lines=proc.stdout.splitlines()
    status=[line.strip() for line in lines if line.startswith('s ')]
    if proc.returncode==10 and status==['s SATISFIABLE']:
        return 'SAT',[int(v) for line in lines if line.startswith('v ') for v in line.split()[1:] if v!='0']
    if proc.returncode==20 and status==['s UNSATISFIABLE']:
        return 'UNSAT',[]
    if proc.returncode in (0,124) and status in ([],['s UNKNOWN'],['s INDETERMINATE']):
        return 'UNKNOWN',[]
    raise RuntimeError(f'unrecognized CaDiCaL return/status {proc.returncode} {status}: {proc.stderr[-400:]}')


def verify_proof(checker,cnf,proof,seconds,log):
    if not proof.is_file() or not proof.stat().st_size: return False
    with log.open('w') as f:
        try:
            rc=subprocess.run([checker,str(cnf),str(proof)],stdout=f,stderr=subprocess.STDOUT,
                              timeout=seconds).returncode
        except subprocess.TimeoutExpired:
            return False
    if rc!=0: return False
    with log.open(errors='replace') as f:
        return any(re.search(r'^s VERIFIED\s*$',line.rstrip('\r\n')) for line in f)


def refine(bad,batch):
    # Evenly spaced elements of the ordered mismatch set; all are fresh.
    count=min(len(bad),batch)
    return [bad[(i*len(bad))//count] for i in range(count)]


def run(args):
    out=args.directory
    out.mkdir(parents=True,exist_ok=True)
    # Unique directory per invocation keeps CNF, rows and final proof associated.
    if any(out.iterdir()): raise ValueError('use an empty --directory')
    enc=Encoding(args.mode,symmetry=not args.no_symmetry)
    for row in seed_rows(args.seed): enc.add_row(row)
    cnf=out/'current.cnf'; proof=out/'final.drat'; rows=out/'rows.json'
    end=time.monotonic()+args.timeout if args.timeout else None
    sat=None
    if args.pysat and not args.encode_only:
        from pysat.solvers import Solver
        sat=Solver(name=args.pysat)
    inserted=0
    try:
        for round_no in range(1,(1<<N)+2):
            left=budget(end)
            rows.write_text(json.dumps({'gap':'L-meta-670','mode':args.mode,'symmetry':(args.mode=='normal' and not args.no_symmetry),'rows':enc.rows})+'\n')
            print(f'round={round_no} mode={args.mode} rows={len(enc.rows)} vars={enc.top} clauses={len(enc.clauses)}',flush=True)
            if sat is None or args.encode_only:
                enc.dimacs(cnf)
            if args.encode_only:
                print('ENCODED'); return
            # A wall-clock budget is supported by external CaDiCaL. An in-process
            # incremental backend is only used when the user selected unlimited time.
            if sat:
                for clause in enc.clauses[inserted:]: sat.add_clause(clause)
                inserted=len(enc.clauses)
                verdict=sat.solve()
                status,model=(('SAT',sat.get_model()) if verdict is True else
                              ('UNSAT',[]) if verdict is False else ('UNKNOWN',[]))
            else:
                status,model=run_cadical(args.cadical,cnf,proof,budget(end),bool(args.checker))
            if status=='UNKNOWN':
                print('UNKNOWN');return
            if status=='UNSAT':
                if sat is not None: enc.dimacs(cnf)
                if not args.checker:
                    print('UNSAT_REPORTED_UNCHECKED');return
                if sat is not None:
                    proved,_=run_cadical(args.cadical,cnf,proof,budget(end),True)
                    if proved!='UNSAT':
                        print('UNKNOWN: no fresh certificate');return
                if verify_proof(args.checker,cnf,proof,budget(end),out/'proof-check.log'):
                    print('EXHAUSTED: independently verified UNSAT for unrestricted L-meta-670 encoding');return
                print('UNSAT_REPORTED_UNCHECKED');return
            if proof.exists():  # SAT trace from this invocation's own fresh directory.
                proof.unlink()
            circuit=enc.decode(model)
            bad=counterexamples(circuit)
            if set(enc.rows).intersection(bad):
                raise ValueError('decoded model fails an encoded row; no result')
            if not bad:
                (out/'witness.json').write_text(json.dumps(circuit,separators=(',',':'))+'\n')
                print('SAT: verified on all 512 rows; witness.json');return
            for row in refine(bad,args.batch): enc.add_row(row)
    except TimeoutError:
        print('UNKNOWN: time budget expired')
    finally:
        if sat is not None: sat.delete()



def cover_control():
    # Independent factorization. Each neighbor list belongs to one star only.
    stars = ((0,(1,4,5)), (1,(2,6)), (3,(2,4,8)), (7,(2,5)), (8,(6,5)))
    gates = []
    def gate(op,a,b):
        gates.append((op,(a,b)))
        return N+len(gates)-1
    def union(pins):
        v=pins[0]
        for q in pins[1:]: v=gate('or',v,q)
        return v
    final=union([gate('and',c,union(pins)) for c,pins in stars])
    # Find a labelled, scheduled control admitted by the normal representation.
    schedules=[]
    for perm in automorphisms():
        remap=dict(enumerate(perm))
        pending=dict(enumerate(gates,N))
        ordered=[]
        while pending:
            hi,lo,w,op=min((max(remap[a],remap[b]),min(remap[a],remap[b]),w,op)
                           for w,(op,(a,b)) in pending.items() if a in remap and b in remap)
            remap[w]=N+len(ordered)
            ordered.append((op,(lo,hi)))
            del pending[w]
        schedules.append(((ordered[0][1][1],ordered[0][1][0]),ordered,remap[final]))
    _,ordered,out=min(schedules)
    return {'gates':[{'op':op,'inputs':list(pins)} for op,pins in ordered],'output':out}


def check_control_encoding(mode,control):
    # Fix structure, propagate its unique auxiliary values, then check every
    # row clause under a full explicit assignment. Drop completed row clauses
    # to keep this optional test below a few MB.
    enc=Encoding(mode,bound=16)
    fixed={enc.t}
    def put(var,bit):
        assert (-var if bit else var) not in fixed
        fixed.add(var if bit else -var)
    for dummy in enc.dummies: put(dummy,False)
    for (ops,ls,rs,left,right),gate in zip(enc.gs,control['gates']):
        a,b=gate['inputs']
        for op,name in zip(ops,('and','or','not')): put(op,gate['op']==name)
        for sel,w in zip(left,ls): put(sel,w==a)
        for sel,w in zip(right,rs): put(sel,w==b)
    for sel,w in zip(enc.osel,enc.outs): put(sel,w==control['output'])
    todo=enc.clauses
    while todo:
        previous=len(fixed)
        next_pass=[]
        for clause in todo:
            if any(v in fixed for v in clause): continue
            unit=[v for v in clause if -v not in fixed]
            assert unit
            if len(unit)==1: put(abs(unit[0]),unit[0]>0)
            else: next_pass.append(unit)
        assert not next_pass or len(fixed)>previous
        todo=next_pass
    assert enc.decode(fixed)==control
    enc.clauses=[]
    for row in range(1<<N):
        start=enc.top
        enc.add_row(row)
        vals=[bool(row & (1<<v)) for v in range(N)]
        assigned=set(fixed)
        for j,gate in enumerate(control['gates']):
            a,b=(vals[p] for p in gate['inputs'])
            val=a and b if gate['op']=='and' else a or b
            vals.append(val)
            for k,bit in enumerate((a,b,val),start+3*j+1):
                assigned.add(k if bit else -k)
        assert vals[control['output']]==target(row)
        assert all(any(v in assigned for v in clause) for clause in enc.clauses)
        enc.clauses.clear()


def self_test():
    c=cover_control()
    assert len(c['gates'])==16 and not counterexamples(c,16)
    assert sum(target(r) for r in range(1<<N))==454
    for mode in ('normal','raw'):
        check_control_encoding(mode,c)
        print(f'{mode}: size-16 control, 512 rows (454 positive, 58 negative), all CNF clauses satisfied')
    print('The size-15 question was not solved by this test.')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--mode',choices=('normal','raw'),default='normal')
    ap.add_argument('--no-symmetry',action='store_true',help='keep every primary-input labelling')
    ap.add_argument('--seed',choices=('frontier','tiny','full'),default='frontier')
    ap.add_argument('--batch',type=int,default=8)
    ap.add_argument('--directory',type=Path)
    ap.add_argument('--self-test',action='store_true',help='check a size-16 positive control; run no solver')
    ap.add_argument('--encode-only',action='store_true')
    ap.add_argument('--cadical',default='cadical',help='external proof-producing solver')
    ap.add_argument('--checker',help='independent drat-trim executable')
    ap.add_argument('--pysat',help='optional in-process incremental solver, e.g. cadical195')
    ap.add_argument('--timeout',type=int,default=0,help='total wall seconds; 0 = unlimited')
    a=ap.parse_args()
    if a.batch<=0 or a.timeout<0 or (a.pysat and a.timeout):
        ap.error('batch must be positive; finite timeouts use the external solver')
    if a.self_test:
        self_test()
        return
    if a.directory is None: ap.error('--directory is required for encoding/search')
    run(a)


if __name__=='__main__': main()
