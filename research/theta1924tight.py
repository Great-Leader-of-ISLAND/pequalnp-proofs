"""Screen theta gates which would necessarily disappear on one of four tight signed minors."""
from functools import lru_cache
from itertools import combinations
from time import monotonic
from theta1924front import PERMS,X,ALL,ALLPAIRS,F
from theta1924free import separated

EDGES=tuple(sorted({tuple(sorted((s[0],s[3]))) for s in PERMS}))
MASKS=tuple(X[p]^X[q] for p,q in EDGES)

def signs(w):return tuple(min(w&m,(ALL^w)&m) for m in MASKS)
ROOT=tuple({0,*(signs(x)[i] for x in X)} for i in range(len(MASKS)))

def run():
    expanded=accepted=rejected=0;start=monotonic()
    tracked=lru_cache(maxsize=60000)(signs)
    @lru_cache(maxsize=160000)
    def check(k,ws):
        nonlocal expanded,accepted,rejected
        expanded+=1
        assert F not in ws
        occupied=[root|{tracked(w)[i] for w in ws} for i,root in enumerate(ROOT)]
        subtotal=1
        for a,b in combinations(ws,2):
            rest=tuple(w for w in ws if w not in (a,b))
            base=0
            for w in rest:base|=separated(w)
            for z in (a&b,a|b,a&(ALL^b),b&(ALL^a)):
                if not z or z in ws:continue
                key=tracked(z)
                if any(t in s for t,s in zip(key,occupied)):
                    rejected+=1
                    continue
                accepted+=1
                sep=base|separated(z)
                for keep in ((),(a,),(b,),(a,b)):
                    if len(rest)+len(keep)+1>k:continue
                    c=sep
                    for w in keep:c|=separated(w)
                    if c==ALLPAIRS:subtotal+=check(k-1,tuple(sorted((*rest,z,*keep))))
        return subtotal
    print('tight minors',EDGES,'unfolded',check(10,tuple(sorted(X))),'distinct',expanded,
          'candidate outputs excluded',rejected,'survived',accepted,'seconds',monotonic()-start)
if __name__=='__main__':run()
