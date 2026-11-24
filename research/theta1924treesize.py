"""Count expansions in an unmemoized tree through exact recurrence on its DAG."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from time import monotonic
from theta1924front import X,F,ALL,ALLPAIRS
from theta1924free import separated

@lru_cache(maxsize=140000)
def summarize(k,ws):
    assert F not in ws
    nodes=1
    fans=0
    first=Counter()
    for a,b in combinations(ws,2):
        rest=tuple(w for w in ws if w not in (a,b))
        base=0
        for w in rest:base|=separated(w)
        for z in (a&b,a|b,a&(ALL^b),b&(ALL^a)):
            if not z or z in ws:continue
            entered=base|separated(z)
            for keep in ((),(a,),(b,),(a,b)):
                if len(rest)+len(keep)+1>k:continue
                covered=entered
                for w in keep:covered|=separated(w)
                if covered!=ALLPAIRS:continue
                child=tuple(sorted((*rest,z,*keep)))
                d,f=summarize(k-1,child)
                nodes+=d
                fans+=1+f
                if k==10:first[(a,b,z)]+=d
    if k==10:
        print('per first gate (unordered) min max mean',min(first.values()),max(first.values()),sum(first.values())/len(first))
        print('frontier quartiles',sorted(first.values())[::10])
    return nodes,fans
if __name__=='__main__':
    t=monotonic()
    print('total nodes, transitions',summarize(10,tuple(sorted(X))))
    print('unique',summarize.cache_info(),'seconds',monotonic()-t)
