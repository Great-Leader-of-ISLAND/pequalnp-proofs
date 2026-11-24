#!/usr/bin/env python3
"""Petersen L-meta-651, shard 1: first gate OR of the endpoints of an edge.
The explicit graph automorphism enumeration verifies transitivity on all 15
unordered edges, including spokes. Thus it suffices to retain OR(x0,x1)
as the first wire, even when it is dead. Raw suffix mode covers omitted and
bad pins, duplicates, dangling gates and all output indices. Normal mode
simplifies constants and aliases, pads only after wire 10, then orders
ready genuine gates by their two input indices. Both x0 and x1 remain
necessary independently of their OR (fix the other to one, and toggle the
first with an exclusive compatible neighbor). The script conservatively
requires suffix uses only of x2,...,x9. A shard exhaustion must come with
an independently replayed DRAT certificate. No restricted or timed-out
result establishes the global statement.
"""
import argparse
import json
import math
from pathlib import Path
import re
import subprocess
import time

N, K = 10, 19
BAD, OMIT = N + K, N + K + 1
EDGES = ((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
         (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5))
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


def check_symmetry():
    expected={tuple(sorted(edge)) for edge in EDGES}
    autos=automorphisms()
    assert len(autos)==120
    assert {tuple(sorted((p[0],p[1]))) for p in autos}==expected


def counterexamples(circuit, bound=K):
    """Independent scalar replay of official Lean semantics on every input."""
    gs, out = circuit['gates'], circuit['output']
    if not isinstance(gs,list) or not 1 <= len(gs) <= bound or type(out) is not int or out < 0:
        raise ValueError('invalid size/output')
    for g in gs:
        if g['op'] not in ('and','or','not') or not isinstance(g['inputs'],list) or len(g['inputs']) > 2:
            raise ValueError('invalid gate op/arity')
        if any(type(p) is not int or p < 0 for p in g['inputs']):
            raise ValueError('invalid wire index')
    if gs[0]['op'] != 'or' or frozenset(gs[0]['inputs']) not in {frozenset(e) for e in EDGES}:
        raise ValueError('first gate is outside shard 1')
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
    def __init__(self, mode):
        self.mode, self.top, self.clauses, self.rows = mode, 0, [], []
        self.t = self.var()
        self.clauses.append([self.t])
        self.gs, self.dummies = [], []
        uses = [[] for _ in range(N+K)]
        last_key = None
        for j in range(1, K):
            and_, or_, not_ = [self.var() for _ in range(3)]
            self.add(and_,or_,not_)
            self.add(-and_,-or_); self.add(-and_,-not_); self.add(-or_,-not_)
            earlier = list(range(N+j))
            ls = earlier + ([BAD,OMIT] if mode == 'raw' else [])
            rs = earlier + ([BAD,OMIT] if mode == 'raw' else [OMIT])
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
                self.dummies.append(dummy)
                self.add(-dummy,not_); self.add(-dummy,left[0])
                if j == K-1: self.add(-dummy)
                for source,a,b in zip(earlier,left,right):
                    uses[source].extend((a,b))
                    if N < source:
                        forbidden = self.dummies[source-N-1]
                        self.add(-forbidden,-a); self.add(-forbidden,-b)
            self.gs.append(((and_,or_,not_),ls,rs,left,right))
        if mode == 'normal':
            for v in range(2,N): self.add(*uses[v])
            for j in range(1,K-1): self.add(self.dummies[j-1],*uses[N+j])
            self.outs, self.osel = [N+K-1], [self.t]
        else:
            self.outs = list(range(N+K))+[BAD]
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
        vs.append(self.t if row & 3 else -self.t)
        for (a,o,n),ls,rs,left,right in self.gs:
            def val(i):
                return -self.t if i == BAD else a if i == OMIT else vs[i]
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
        gs=[{'op':'or','inputs':[0,1]}]
        for ops,ls,rs,left,right in self.gs:
            ps=[pick(left,ls),pick(right,rs)]
            gs.append({'op':pick(ops,('and','or','not')),'inputs':[p for p in ps if p != OMIT]})
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
    check_symmetry()
    out=args.directory
    out.mkdir(parents=True,exist_ok=True)
    # Unique directory per invocation keeps CNF, rows and final proof associated.
    if any(out.iterdir()): raise ValueError('use an empty --directory')
    enc=Encoding(args.mode)
    for row in seed_rows(args.seed): enc.add_row(row)
    cnf=out/'current.cnf'; proof=out/'final.drat'; rows=out/'rows.json'
    end=time.monotonic()+args.timeout if args.timeout else None
    sat=None
    if args.pysat and not args.encode_only:
        from pysat.solvers import Solver
        sat=Solver(name=args.pysat)
    inserted=0
    try:
        for round_no in range(1,1026):
            left=budget(end)
            rows.write_text(json.dumps({'shard':1,'mode':args.mode,'rows':enc.rows})+'\n')
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
                    print('EXHAUSTED: independently verified UNSAT for shard 1');return
                print('UNSAT_REPORTED_UNCHECKED');return
            if proof.exists():  # SAT trace from this invocation's own fresh directory.
                proof.unlink()
            circuit=enc.decode(model)
            bad=counterexamples(circuit)
            if set(enc.rows).intersection(bad):
                raise ValueError('decoded model fails an encoded row; no result')
            if not bad:
                (out/'witness.json').write_text(json.dumps(circuit,separators=(',',':'))+'\n')
                print('SAT: verified on all 1024 rows; witness.json');return
            for row in refine(bad,args.batch): enc.add_row(row)
    except TimeoutError:
        print('UNKNOWN: time budget expired')
    finally:
        if sat is not None: sat.delete()


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--mode',choices=('normal','raw'),default='normal')
    ap.add_argument('--seed',choices=('frontier','tiny','full'),default='frontier')
    ap.add_argument('--batch',type=int,default=8)
    ap.add_argument('--directory',type=Path,required=True)
    ap.add_argument('--encode-only',action='store_true')
    ap.add_argument('--cadical',default='cadical',help='external proof-producing solver')
    ap.add_argument('--checker',help='independent drat-trim executable')
    ap.add_argument('--pysat',help='optional in-process incremental solver, e.g. cadical195')
    ap.add_argument('--timeout',type=int,default=0,help='total wall seconds; 0 = unlimited')
    a=ap.parse_args()
    if a.batch<=0 or a.timeout<0 or (a.pysat and a.timeout):
        ap.error('batch must be positive; finite timeouts use the external solver')
    run(a)


if __name__=='__main__': main()
