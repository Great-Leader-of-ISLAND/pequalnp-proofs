"""Automorphisms of the actual 14-input incidence graph and raw observation-set orbits."""
from pathlib import Path
from itertools import permutations
from functools import lru_cache
import runpy
D=runpy.run_path(str(Path(__file__).with_name('3004-one-bank-slice.py')))
E,N,F,n,size,bits=D['E'],D['N'],D['F'],D['n'],D['size'],D['bits']
adj=[0]*n
for e in E:
    a,b=bits(e);adj[a]|=1<<b;adj[b]|=1<<a
def perms():
    out=[]
    for dual in [False,True]:
        side=range(7,14) if dual else range(7)
        other=range(7) if dual else range(7,14)
        byhood={adj[v]:v for v in other}
        for p in permutations(side):
            lv=[]
            for l in range(7,14):
                aim=sum(1<<p[i] for i in bits(adj[l]))
                if aim not in byhood:break
                lv.append(byhood[aim])
            if len(lv)==7:out.append(tuple(p)+tuple(lv))
    assert len(out)==336
    return out
def orbit(r,g):return {sum(1<<p[i] for i in bits(r)) for p in g}
@lru_cache(None)
def masks():
    covered=set();out=[];g=perms()
    for r in range(1<<n):
        if r in covered:continue
        o=orbit(r,g);covered.update(o)
        B=F^r;ni=[i for i,c in enumerate(N) if B&c==B];ei=[i for i,e in enumerate(E) if e&r==e]
        if not ni or not ei:continue
        out.append((r,len(o),ei,ni))
    return out
if __name__=='__main__':
 for k in [13,14,15]:
    print('gate count',k)
    for r,m,ei,ni in masks():
        if size(r)>25-k:continue
        nmask=sum(1<<i for i in ni)
        required=[e for e in E if e&(F^r)]
        lb=D['bank_leaves'](required,((1<<len(N))-1)^nmask)
        if lb<=k+1:print(r,m,'size',size(r),'min',lb,'free edge/neg',len(ei),len(ni))
