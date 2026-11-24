"""Free-inverter search directly on distinct live signal values (no topology hypotheses)."""
import argparse
import functools
import itertools
import json
import time
from theta1924front import ALL, ALLPAIRS, X, F, cuts, TimedOut
from theta1924free import separated


def compatible(live):
    # With no future fanout, every live signal occurs once in the expression.
    # In an NNF expression there must be a single orientation per leaf making
    # the target monotone in all the literal columns on the specified rows.
    dirs=[cuts(v) for v in live]
    diff=[a|b for a,b in dirs]
    suffix=[0]*(len(live)+1)
    for i in range(len(live)-1,-1,-1):
        suffix[i]=suffix[i+1]|diff[i]
    if suffix[0]!=ALLPAIRS:return False
    prefix=covered=0
    choices=[]
    for i,(a,b) in enumerate(dirs):
        unique=ALLPAIRS^(prefix|suffix[i+1])
        prefix|=diff[i]
        g,h=bool(a&unique),bool(b&unique)
        if g and h:return False
        if g:covered|=a
        elif h:covered|=b
        else:choices.append((a,b))
    if covered==ALLPAIRS:return True
    def extend(i,v):
        if v==ALLPAIRS:return True
        if i==len(choices):return False
        a,b=choices[i]
        return extend(i+1,v|a) or extend(i+1,v|b)
    return extend(0,covered)


def run(budget,seconds,memo,first=None,leaf_check=True):
    wall=time.monotonic()
    count=0
    path=[]
    found=None
    @functools.lru_cache(maxsize=memo)
    def go(k,live):
        nonlocal count,found
        count+=1
        if count%128==0 and time.monotonic()-wall>seconds:raise TimedOut
        if F in live:
            found=list(path)
            return True
        if not k or len(live)>k+1:return False
        if leaf_check and len(live)==k+1 and not compatible(live):return False
        for a,b in itertools.combinations(live,2):
            if first is not None and not path and {a,b}!={X[first[0]],X[first[1]]}:continue
            rest=set(live)-{a,b}
            base=0
            for w in rest:base|=separated(w)
            for op,z in enumerate((a&b,a|b,a&(ALL^b),b&(ALL^a))):
                if z==0 or z in live:continue
                entered=base|separated(z)
                keep_sets=((),(a,),(b,),(a,b))
                for keep in keep_sets:
                    if len(rest)+1+len(keep)>k:continue
                    cover=entered
                    for w in keep:cover|=separated(w)
                    if cover!=ALLPAIRS:continue
                    nxt=tuple(sorted((*rest,z,*keep)))
                    path.append((op,hex(a),hex(b),hex(z)))
                    if go(k-1,nxt):return True
                    path.pop()
        return False
    try:
        result='WITNESS' if go(budget,tuple(sorted(X))) else 'EXHAUSTED'
    except TimedOut:
        result='UNKNOWN'
    print(json.dumps(dict(budget=budget,status=result,nodes=count,seconds=round(time.monotonic()-wall,3),
                          cache=go.cache_info().currsize,path=found)),flush=True)
    go.cache_clear()


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--size',type=int,default=10)
    p.add_argument('--seconds',type=float,default=10)
    p.add_argument('--memo',type=int,default=120000)
    p.add_argument('--first',type=int,nargs=2)
    p.add_argument('--no-leaf-check',action='store_true')
    a=p.parse_args()
    run(a.size,a.seconds,a.memo,a.first,not a.no_leaf_check)
