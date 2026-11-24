"""One sound monotone conjunction of small disjunctions, completed by stars.

Only seeks positive witnesses in this bounded class. Includes sharing binary
disjunctions between clauses and star-gate preparations. Every candidate
formula has a use of OR(0,1).
"""
from functools import lru_cache
from itertools import combinations, product

def bits(s):
    return bin(s).count("1")

E=((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),
   (4,9),(5,7),(7,9),(9,6),(6,8),(8,5))
EM=[(1<<a)|(1<<b) for a,b in E]
FULL=(1<<15)-1
Z=3
NEI=[sum(1<<(b if a==i else a) for a,b in E if i in (a,b)) for i in range(10)]
IND=[s for s in range(1024) if all(s&m!=m for m in EM)]
MAXI=[s for s in IND if all(s|(1<<i) not in IND for i in range(10) if not(s>>i&1))]
assert len(MAXI)==15
MASK=[s for s in range(1,1024) if bits(s)<=3]
HITIND={s:sum(1<<i for i,t in enumerate(MAXI) if t&s) for s in MASK}
HITEDGE={s:sum(1<<i for i,t in enumerate(EM) if t&s) for s in MASK}
PAIRS={s:tuple(s^(1<<i) for i in range(10) if s>>i&1) for s in MASK if bits(s)==3}
VC=sorted((bits(m),sum(1<<i for i,t in enumerate(EM) if t&m)) for m in range(1024))
@lru_cache(None)
def tau(r):
    return next(k for k,s in VC if r&s==r)

def subsets(m):
    s=m
    while s:
        yield s
        s=(s-1)&m

STARS=[(i,s,sum(1<<j for j,t in enumerate(EM) if (1<<i)&t and s&t))
       for i,n in enumerate(NEI) for s in subsets(n)]
REL=frozenset(s for _,s,_ in STARS if bits(s)>=2)
def prep(s,free):
    if bits(s)==1 or s in free: return 0
    if bits(s)==3 and any(p in free for p in PAIRS[s]): return 1
    return bits(s)-1

@lru_cache(None)
def rebates(free):
    return sum(max(bits(s)-1-prep(s,free) for s in subsets(n)) for n in NEI)

@lru_cache(None)
def complete(r,free):
    if not r: return 0,()
    e=r&-r
    possibles=[]
    for i,s,m in STARS:
        if not (e&m): continue
        c,plan=complete(r&~m,free)
        possibles.append((2+prep(s,free)+c,((i,s),)+plan))
    return min(possibles)

def search():
    n=0; npre=0; dynamic=0; best=100; best_case=None
    # Bound each disjunction by three variables; allow one to three further
    # clauses. For four clauses, the three non-designated clauses have size <=2.
    for root in MASK:
        if root&Z!=Z: continue
        for k in (1,2,3):
            others=[s for s in MASK if s!=root and (k<3 or bits(s)<=2)]
            for rest in combinations(others,k):
                clauses=(root,)+rest
                if any(a&b in (a,b) for a,b in combinations(clauses,2)): continue
                neg=HITIND[root]; pos=HITEDGE[root]
                for s in rest: neg &= HITIND[s]; pos &= HITEDGE[s]
                if neg or not pos: continue
                n+=1; r=FULL^pos
                splits=[(Z,) if s==root else PAIRS[s] for s in clauses if bits(s)==3]
                fixed=frozenset(c for c in clauses if bits(c)>1) | {Z}
                for ps in product(*splits):
                    free=fixed.union(ps); k0=len(free)+k
                    # Every distinct nonsingleton OR wire is charged once;
                    # clauses are combined by k AND operations.
                    f=frozenset(free&REL); npre+=1
                    lb=k0+bits(r)+tau(r)-rebates(f)
                    if lb>20 or lb>=best: continue
                    dynamic+=1; c,stars=complete(r,f); total=k0+c
                    if total<best: best=total; best_case=(clauses,free,stars)
    print('sound clause lists',n,'shared preparations',npre,'exact completions',dynamic)
    print('witness at or below 20',best_case if best<=20 else None)
    print('best cost among dynamically completed cases',best if best_case else None)
if __name__=='__main__': search()
