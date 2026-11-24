"""All possible negative-row sets for the bank when each ordinary input occurs once."""
import runpy
from pathlib import Path
from functools import lru_cache
O=runpy.run_path(str(Path(__file__).with_name('3004-bank-orbits.py')))
E,N,F,bits=O['E'],O['N'],O['F'],O['bits']
@lru_cache(None)
def generate():
    cols=set()
    for U in range(F+1):
        es=[e for e in E if e&U==e]
        ns=[i for i,c in enumerate(N) if not c&~U and all(e&c for e in es)]
        t=sum(1<<i for i in ns)
        v=t
        while v:
            carried=0
            for i in bits(v):carried|=N[i]
            if carried==U:cols.add(v)
            v=(v-1)&t
    index={c:i for i,c in enumerate(N)}
    maps=[tuple(index[sum(1<<g[v] for v in bits(c))] for c in N) for g in O['perms']()]
    reps=[];rem=cols.copy()
    while rem:
        c=min(rem);reps.append(c)
        orb={sum(1<<p[j] for j in bits(c)) for p in maps}
        assert orb<=cols
        rem-=orb
    return len(cols),tuple(reps)
if __name__=='__main__':
    total,reps=generate();print('distinct negative families',total,'automorphism orbits',len(reps),'representatives',reps)
