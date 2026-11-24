"""Search the irredundant one-negative residual on its 29 determining rows."""
import runpy, sys
from pathlib import Path
import petersen670 as ref
first=runpy.run_path(str(Path(__file__).with_name('signed2683-control.py')))
rows=first['cofactor_frontier']()

def structural_control():
    # A Shannon expansion has a genuinely negative literal that is needed on a cofactor.
    # Normalize semantic coincidences only on the proved complete suite of rows.
    allrows=(1<<len(rows))-1
    vals=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(9)]
    gates=[]
    def place(op,a,b=None):
        v=allrows^vals[a] if b is None else (vals[a]&vals[b] if op=='and' else vals[a]|vals[b])
        if v in vals: return vals.index(v)
        assert v!=0 and v!=allrows
        i=len(vals);vals.append(v);gates.append({'op':op,'inputs':[a] if b is None else [a,b]});return i
    inv=place('not',0)
    def either(xs):
        root=xs[0]
        for x in xs[1:]: root=place('or',root,x)
        return root
    base=either([place('and',i,j) for i,j in ref.EDGES if i!=0 and j!=0])
    high=either([base,1,4,5])
    out=place('or',place('and',inv,base),place('and',0,high))
    live=set(); todo=[out]
    while todo:
        wire=todo.pop()
        if wire<9 or wire in live:continue
        live.add(wire);todo.extend(gates[wire-9]['inputs'])
    mapped={i:i for i in range(9)};ordered=[]
    while live:
        key,j=min((tuple(sorted((mapped[a] for a in gates[j-9]['inputs']),reverse=True)),j) for j in live if all(a in mapped for a in gates[j-9]['inputs']))
        mapped[j]=9+len(ordered);ordered.append({'op':gates[j-9]['op'],'inputs':sorted(key)});live.remove(j)
    return {'gates':ordered,'output':mapped[out]}

class Table(ref.Encoding):
    def __init__(self,bound):
        super().__init__('normal',bound=bound,symmetry=False)
        self.values=[[] for _ in range(9+bound)]
        for row in rows:
            wires=[self.t if (row>>i)&1 else -self.t for i in range(9)]
            for (a,o,n),ls,rs,left,right in self.gs:
                def val(i):
                    if i==self.omit:return a
                    return wires[i]
                x=self.mux(left,[val(i) for i in ls]);y=self.mux(right,[val(i) for i in rs]);z=self.var()
                self.add(-a,-z,x);self.add(-a,-z,y);self.add(-a,z,-x,-y)
                self.add(-o,z,-x);self.add(-o,z,-y);self.add(-o,-z,x,y)
                self.add(-n,-z,-x);self.add(-n,z,x)
                wires.append(z)
            self.add(wires[-1] if ref.target(row) else -wires[-1])
            for col,lit in zip(self.values,wires):col.append(lit)
        for dummy in self.dummies:self.add(-dummy)
        ops,ls,rs,left,right=self.gs[0]
        self.add(ops[2]);self.add(left[ls.index(0)])
        for ops,*_ in self.gs[1:]:self.add(-ops[2])
        _,ls,rs,left,right=self.gs[-1]
        for raw in range(10): self.add(-left[ls.index(raw)]);self.add(-right[rs.index(raw)])
        for j in range(10,9+bound):
            self.add(*self.values[j]);self.add(*[-a for a in self.values[j]])
            for i in range(j):
                differences=[]
                for a,b in zip(self.values[i],self.values[j]):
                    d=self.var();self.add(-d,a,b);self.add(-d,-a,-b)
                    differences.append(d)
                self.add(*differences)
def check(solver,folder):
    folder.mkdir(exist_ok=False)
    ctrl=structural_control()
    assert not ref.counterexamples(ctrl,len(ctrl['gates']))
    for pinned in (True,False):
        bound=len(ctrl['gates']) if pinned else 15
        m=Table(bound)
        if pinned:
            for (ops,ls,rs,left,right),g in zip(m.gs,ctrl['gates']):
                a,*extra=g['inputs'];b=extra[0] if extra else m.omit
                m.add(ops[('and','or','not').index(g['op'])]);m.add(left[ls.index(a)]);m.add(right[rs.index(b)])
        cnf=folder/('control.cnf' if pinned else 'residual.cnf');m.dimacs(cnf)
        print('pinned',pinned,'gates',bound,'variables',m.top,'clauses',len(m.clauses),flush=True)
        verdict,model=ref.run_cadical(solver,cnf,folder/'solver.proof',30 if pinned else 180,False)
        print(verdict,flush=True)
        if pinned:assert verdict=='SAT'
        if verdict=='SAT':
            c=m.decode(model);assert not ref.counterexamples(c,bound);print('all 512 replayed',c,flush=True)
        if verdict=='UNSAT':
            verdict,_=ref.run_cadical(solver,cnf,folder/'solver.proof',180,True)
            print('DRAT check', verdict=='UNSAT' and ref.verify_proof(sys.argv[2],cnf,folder/'solver.proof',100,folder/'check.log'),flush=True)
if __name__=='__main__': check(sys.argv[1],Path(sys.argv[3]))
