"""Exact BFS of small AND/OR programs with one free complemented literal.
A reached pool stores every available distinct truth table. No renumbering
of states or symmetry quotient is used. Constants do not shorten positive
gate programs, since any binary use of a constant can be simplified."""
from itertools import combinations
def enumerate_costs(n,depth,negated):
    N=1<<(1<<n)
    xs=tuple(sum(1<<r for r in range(1<<n) if r>>i&1) for i in range(n))
    raw=frozenset(xs+((N-1-xs[0],) if negated else ()))
    frontier={raw};best={f:0 for f in raw};best.update({0:0,N-1:0})
    counts=[]
    for d in range(1,depth+1):
        after=set()
        for pool in frontier:
            for a,b in combinations(pool,2):
                for f in (a&b,a|b):
                    if f in pool:continue
                    best.setdefault(f,d)
                    if d!=depth:after.add(pool|{f})
        counts.append((d,len(frontier),len(best)))
        frontier=after
    return best,counts
def monotone(f,n):
    return all(not (f>>r&1) or all(f>>(r|1<<i)&1 for i in range(n)) for r in range(1<<n))
for n,d in [(2,4),(3,6),(4,5)]:
    pos,h=enumerate_costs(n,d,False);both,k=enumerate_costs(n,d,True)
    gains=[(f,c,pos.get(f)) for f,c in both.items() if monotone(f,n) and c<pos.get(f,d+1)]
    print(n,d,'positive',h,'with complement',k,'strict gains',gains[:20],flush=True)
