"""Monotone extreme-row tests for a 45-gate circuit with a masked observation."""
import sys,time,random,json
from itertools import combinations_with_replacement

N=25
P=[1,3,4,5,6,7,9,10,11]
L=range(12,25)
E=[(p,l) for p in P for l in L if (p+l+2)%13 in (0,1,3,9)]
Q=(13,15,21)
qmask=sum(1<<a for a in Q)
emask=[(1<<a)|(1<<b) for a,b in E]
def true_f(row):return any(row&e==e for e in emask)
def max_false(allowed_lines):
    rows=set()
    for m in range(512):
        points={p for i,p in enumerate(P) if m>>i&1}
        lines={l for l in allowed_lines if all((p,l) not in E for p in points)}
        fixed={p for p in P if all((p,l) not in E for l in lines)}
        if fixed==points: rows.add(sum(1<<a for a in points|lines|{0,2,8}))
    return rows
neg=max_false(set(L)); obsneg=max_false(set(L)-set(Q))
rows=sorted(set(emask)|neg|obsneg|{1<<l for l in Q})
X=[sum(1<<i for i,r in enumerate(rows) if r>>j&1) for j in range(N)]
required=lambda yes,no:(sum(1<<rows.index(r) for r in yes),sum(1<<rows.index(r) for r in no))
fa,fb=required(emask,neg)
ga,gb=required([1<<l for l in Q],obsneg)
def agrees(val,a,b):return val&a==a and val&b==0
def template(rng):
    gs=[]
    def gate(op,a,b):
        gs.append((op,a,b));return N+len(gs)-1
    def join(ys):
        ys=list(ys)
        while len(ys)>1:
            a,b=rng.sample(range(len(ys)),2);p,q=ys[a],ys[b]
            ys=[v for j,v in enumerate(ys) if j not in (a,b)]+[gate('or',p,q)]
        return ys[0]
    obs=join(Q); centers=P[:];rng.shuffle(centers)
    o=join([gate('and',p,join([l for q,l in E if q==p])) for p in centers])
    return gs,o,obs
def evaluate(gs):
    w=X[:]
    for op,a,b in gs:w.append(w[a]&w[b] if op=='and' else w[a]|w[b])
    return w
def single():
    runs=0
    for seed in range(16):
        base,o,v=template(random.Random(seed));w=evaluate(base)
        assert len(base)==46 and agrees(w[o],fa,fb) and agrees(w[v],ga,gb)
        for i in range(len(base)):
            for alias in range(N+i):
                def remap(a):return alias if a==N+i else a-int(a>N+i)
                gs=[(op,remap(a),remap(b)) for j,(op,a,b) in enumerate(base) if i!=j]
                allw=evaluate(gs);runs+=1
                roots=[j for j in range(N+len(gs)) if agrees(allw[j],fa,fb)]
                obs=next((j for j,z in enumerate(allw) if agrees(z,ga,gb)),None)
                if roots and obs is not None:print('FULL WITNESS',json.dumps([gs,roots[0],obs]));return
    print('inputs tested',len(rows),'positive edges',len(E),'max negative',len(neg),'max avoiding observation',len(obsneg),'templates 16; exhaustive single bypasses',runs,'no 45-gate candidate')
if __name__=='__main__':single()
