"""Find root gate types contradicted by smaller cofactors, with no unbounded search."""
from itertools import combinations,product
from time import monotonic
from theta1924front import F,PERMS
from theta1924cofactors import run,dense_values

def minor(old,fn):
    ids=set(range(7))-set(old)
    f=0
    for r in range(1<<len(ids)):
        w=sum((r>>j&1)<<i for j,i in enumerate(sorted(ids)))
        for i in old:w|=fn(i,w)<<i
        f|=(F>>w&1)<<r
    tab,active=dense_values(f,len(ids))
    return tab^(((1<<(1<<len(active)))-1) if tab&1 else 0),len(active)
def lower(tab,n,cap):
    if not tab:return 0
    k=max(0,n-1)
    while k<cap and not run(tab,n,k):k+=1
    return k
if __name__=='__main__':
    cache={};start=monotonic()
    for a,b in combinations(range(7),2):
        orb=min(tuple(sorted((pm[a],pm[b]))) for pm in PERMS)
        if orb in cache:continue
        cache[orb]=True
        costs=[]
        for x,y in product(range(2),repeat=2):
            f,n=minor((a,b),lambda i,w:x if i==a else y)
            costs.append(lower(f,n,8))
        print('pair',a,b,'00/01/10/11',costs,flush=True)
    print('seconds',monotonic()-start)
