"""Exact synthesis for small induced graphs, arbitrary free AND and counted binary OR."""
import argparse,subprocess,tempfile
from itertools import combinations
from pathlib import Path
def graph(name):
    if name=='square':return 4,[(0,2),(0,3),(1,2),(1,3)]
    if name=='cycle6':return 6,[(0,3),(1,3),(1,4),(2,4),(2,5),(0,5)]
    if name=='path5':return 5,[(0,1),(1,2),(2,3),(3,4)]
    if name=='star5':return 6,[(0,i) for i in range(1,6)]
    raise ValueError(name)
class CNF:
    def __init__(self):self.n=1;self.clauses=[(1,)]
    def var(self):self.n+=1;return self.n
    def add(self,*xs):
        if 1 in xs:return
        xs=set(xs)-{-1}
        if any(-a in xs for a in xs):return
        self.clauses.append(tuple(sorted(xs)))
    def AND(self,items):
        s=set(items)-{1}
        if -1 in s or any(-x in s for x in s):return -1
        if not s:return 1
        if len(s)==1:return s.pop()
        v=self.var()
        for a in s:self.add(-v,a)
        self.add(v,*(-a for a in s))
        return v
    def OR(self,items):return -self.AND(-x for x in items)
def encoding(n,edges,k):
    hit=lambda r:any((r>>a)&(r>>b)&1 for a,b in edges)
    rows=sorted({(1<<a)|(1<<b) for a,b in edges}|{r for r in range(1<<n) if not hit(r) and all(hit(r|1<<j) for j in range(n) if not r>>j&1)})
    f=CNF();xs=[[1 if r>>j&1 else -1 for j in range(n)]+[-1] for r in rows];gates=[]
    def pins():
        sels=[f.var() for _ in xs[0]]
        # A selected false wire is permitted, as in the posted free-AND rule language.
        outs=[f.AND(f.OR((-s,v)) for s,v in zip(sels,w)) for w in xs]
        return sels,outs
    for _ in range(k):
        a,av=pins();b,bv=pins();gates.append((a,b))
        for w,u,v in zip(xs,av,bv):w.append(f.OR((u,v)))
    o,ov=pins()
    for r,v in zip(rows,ov):f.add(v if hit(r) else -v)
    return f,gates,o,hit,rows
def run(name,k,seconds,solver):
    n,es=graph(name);f,gs,out,target,rows=encoding(n,es,k)
    with tempfile.TemporaryDirectory() as td:
        path=Path(td)/'instance.cnf'
        with path.open('w') as z:
            z.write(f'p cnf {f.n} {len(f.clauses)}\n')
            for row in f.clauses:z.write(' '.join(map(str,row))+' 0\n')
        try:r=subprocess.run([solver,'-q',str(path)],timeout=seconds,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        except subprocess.TimeoutExpired:
            print('OR_SYNTH',name,'budget',k,'UNKNOWN_TIMEOUT',seconds,'seconds',flush=True);return
        if r.returncode==20:
            print('OR_SYNTH',name,'budget',k,'UNSAT',f.n,'variables',len(rows),'extremal assignments',flush=True);return
        if r.returncode!=10:raise RuntimeError((r.returncode,r.stdout[:250]))
        positive={int(a) for l in r.stdout.splitlines() if l.startswith('v ') for a in l[2:].split() if int(a)>0}
        def idx(s):return [i for i,b in enumerate(s) if b in positive]
        rules=[(idx(a),idx(b)) for a,b in gs];output=idx(out)
        for r in range(1<<n):
            vals=[bool(r>>i&1) for i in range(n)]+[False]
            for a,b in rules:vals.append(all(vals[i] for i in a) or all(vals[i] for i in b))
            assert all(vals[i] for i in output)==target(r)
        print('OR_SYNTH',name,'budget',k,'SAT_ALL_INPUTS',rules,output,flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('solver');p.add_argument('case');p.add_argument('budget',type=int);p.add_argument('--seconds',type=int,default=25);a=p.parse_args()
    run(a.case,a.budget,a.seconds,a.solver)
