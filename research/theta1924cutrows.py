"""Select a sufficient subfamily of separating row pairs using exact full-state traversal.

The dynamic mask acquires an explicit set bit of each new disjoint obstruction.
Its randomized / min-distance priority does not affect the actual certificate:
run a separate full search on the resulting projected rows to verify the verdict.
"""
from itertools import combinations
from pathlib import Path
import argparse
import time
from theta1924front import X, F, ALL, ALLPAIRS, POS, NEG
from theta1924free import separated

def pick():
    seen=set()
    one_step=[0]*8
    for i,p in enumerate(POS):
        for j,n in enumerate(NEG):
            one_step[(p^n).bit_count()] |= 1<<(i*len(NEG)+j)
    required=0
    learned=0
    rej=0
    def go(k,live):
        nonlocal required,learned,rej
        key=(k,live)
        if key in seen:return
        seen.add(key)
        assert F not in live
        for a,b in combinations(live,2):
            rest=tuple(w for w in live if w not in (a,b))
            before=0
            for w in rest:before|=separated(w)
            for z in (a&b,a|b,a&(ALL^b),b&(ALL^a)):
                if z==0 or z in live:continue
                avail=before|separated(z)
                for keep in ((),(a,),(b,),(a,b)):
                    if len(rest)+1+len(keep)>k:continue
                    cov=avail
                    for w in keep:cov|=separated(w)
                    miss=ALLPAIRS^cov
                    if not miss:
                        go(k-1,tuple(sorted((*rest,z,*keep))))
                    else:
                        rej+=1
                        if miss & (miss-1)==0:required|=miss
                        if (required|learned)&miss:continue
                        for sub in one_step:
                            hit=miss&sub
                            if hit:
                                learned|=hit&-hit
                                break
    go(10,tuple(sorted(X)))
    return required,learned,len(seen),rej

if __name__=='__main__':
    start=time.monotonic()
    req,soft,n,r=pick()
    print('singletons',req.bit_count(),'plus greedy', (req|soft).bit_count(),'states',n,'failures',r,'seconds',time.monotonic()-start,flush=True)
    print('required',hex(req),flush=True)
    print('chosen',hex(req|soft),flush=True)
