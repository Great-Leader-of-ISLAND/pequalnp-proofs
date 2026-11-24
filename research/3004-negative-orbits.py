"""Candidate bank-positive independent-row families using a bounded set of repeated raw labels."""
from itertools import combinations
from functools import lru_cache
from pathlib import Path
import runpy
w=Path(__file__).resolve().parent
O=runpy.run_path(str(w/'3004-bank-orbits.py'));marks=runpy.run_path(str(w/'3004-suffix-rectangles.py'))['marks_possible']
E,N,F,bits,size=O['E'],O['N'],O['F'],O['bits'],O['size'];P=(1<<len(E))-1
def image(mask,p):return sum(1<<p[i] for i in bits(mask))
@lru_cache(None)
def group():
    index={c:i for i,c in enumerate(N)}
    return [(tuple(g),tuple(index[image(c,g)] for c in N)) for g in O['perms']()]
def nonzero_subsets(t):
    v=t
    while v:
        yield v
        v=(v-1)&t
@lru_cache(None)
def possible(R,nm,budget):
    G=[(g,p) for g,p in group() if image(R,g)==R]
    slots=budget-size(R);known=set();reps=[]
    def include(x):
        if x in known:return
        orb={image(x,p) for g,p in G};known.update(orb);reps.append(x)
    if size(nm)<=13:
        for x in nonzero_subsets(nm):
            if x not in known and marks(P,x,R,budget):include(x)
        return tuple(reps)
    assert R==F
    already=set()
    for rep in combinations(range(14),slots):
        D=sum(1<<j for j in rep)
        if D in already:continue
        already.update(image(D,g) for g,p in G)
        es=[e for e in E if not e&D]
        for U in range(1,F+1):
            inside=[e for e in es if e&U==e]
            t=sum(1<<j for j,c in enumerate(N) if not c&~U and all(e&c for e in inside))
            for x in nonzero_subsets(t):
                if x in known:continue
                u=0
                for j in bits(x):u|=N[j]
                if u==U:include(x)
    return tuple(reps)
if __name__=='__main__':
    for k in (11,10,9):
        reps=possible(F,(1<<len(N))-1,25-k)
        print(k,len(reps),flush=True)
