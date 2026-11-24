"""Lower-bound a formula bank using inputs where a single Boolean port is forced."""
from collections import Counter
from functools import lru_cache
from pathlib import Path
import runpy
D=runpy.run_path(str(Path(__file__).with_name('3004-or-bank-rank.py')))
E,N,F,n=D['edges'],D['cols'],D['full'],D['n']
bits,matching=D['bits'],D['matching']
def size(x):return bin(x).count('1')
@lru_cache(None)
def columns(required,forbidden):
    return sum(1<<i for i,c in enumerate(N) if c&required==required and not c&forbidden)
def bank_leaves(es,neg):
    adj=[0]*n
    for e in es:
        a,b=bits(e);adj[a]|=1<<b;adj[b]|=1<<a
    base=[bool(neg&columns(adj[i],1<<i)) for i in range(n)]
    good=[]
    for e in es:
        a,b=bits(e)
        if (size(adj[a])==1 and not base[a]) or (size(adj[b])==1 and not base[b]):continue
        if neg&columns((adj[a]|adj[b])&~e,e):good.append(e)
    dg=[0]*n
    for e in good:
        for i in bits(e):dg[i]+=1
    forced=0
    for i in range(n):
        essential=any(neg&columns(1<<j,1<<i) for j in bits(adj[i]))
        if (dg[i]==0 and essential) or (dg[i]<size(adj[i]) and base[i]):forced|=1<<i
    return len(good)+size(forced)+matching(good,F^forced)
def summary():
    bounds={}
    for R in range(1<<n):
        B=F^R
        allowedNeg=sum(1<<i for i,c in enumerate(N) if c&B==B)
        if not allowedNeg or not any(e&R==e for e in E):continue
        essential=[e for e in E if e&B]
        needNeg=((1<<len(N))-1)^allowedNeg
        bounds[R]=bank_leaves(essential,needNeg)
    for k in range(5,27):
        small=[(R,z) for R,z in bounds.items() if size(R)<=25-k]
        unresolved=[(R,z) for R,z in small if z<=k+1]
        print('bank gates',k,'eligible observed sets',len(small),'remaining',len(unresolved),
              'min bank leaves',min((z for _,z in small),default=None),'examples',unresolved[:2])
if __name__=='__main__':summary()
