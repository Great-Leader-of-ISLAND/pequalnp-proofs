"""Generic bounded enumeration for ordinary AND/OR gates with free complementation.

Use predicted raw multiplicities and a separately budgeted pool of extra
internal uses. All gates represent their polarity that is zero on the empty row.
"""
import argparse
import functools
import itertools
import json
import time
from theta1924front import X,F,ALL,ALLPAIRS,SENS,PERMS,cuts,TimedOut
from theta1924 import evaluate,target,control


@functools.lru_cache(maxsize=90000)
def separated(x):
    a,b=cuts(x)
    return a|b


def configurations(size,syms=True):
    excess=size-6
    for extra in range(excess+1):
        for positions in itertools.combinations_with_replacement(range(7),extra):
            count=tuple(1+positions.count(x) for x in range(7))
            if sum(x>1 for x in count)<2:continue
            if syms and min(tuple(count[p[i]] for i in range(7)) for p in PERMS)!=count:
                continue
            yield count,excess-extra


def solve(size,mult,extra,max_seconds,planted=None,order=True):
    start=time.monotonic()
    nodes=0
    path=[]
    bits=list(X)
    witness=None

    def dfs(live,raw_left,budget,prior_key):
        nonlocal nodes,witness
        nodes+=1
        if nodes%256==0 and time.monotonic()-start>=max_seconds:raise TimedOut
        i=len(path)
        if len(live)>size+1-i:return False
        for a,b in itertools.combinations(live,2):
            if planted and (a,b)!=planted[i][:2]:continue
            if order and (b,a)<prior_key:continue
            if b<7 and (mult[a]==1 or mult[b]==1):continue
            if i==size-1 and (len(live)!=2 or budget or any(raw_left[x]>1 for x in (a,b) if x<7)):
                continue
            l,r=bits[a],bits[b]
            remaining=list(raw_left)
            for v in (a,b):
                if v<7:remaining[v]-=1
            base=[w for w in live if w not in (a,b) or (w<7 and remaining[w]>0)]
            internal=[w for w in (a,b) if w>=7]
            for op,z in enumerate((l&r,l|r,l&(ALL^r),r&(ALL^l))):
                if planted and op!=planted[i][2]:continue
                if i==size-1:
                    if z==F:
                        witness=path+[(a,b,op)]
                        return True
                    continue
                if z in (0,F) or z in bits:continue
                bad=False
                for w in (a,b):
                    if w>=7 or mult[w]!=1:continue
                    low,high=SENS[w]
                    if not((not z&low and z&high==high) or (z&low==low and not z&high)):
                        bad=True
                        break
                if bad:continue
                path.append((a,b,op))
                bits.append(z)
                for k in range(min(budget,len(internal))+1):
                    for keep in itertools.combinations(internal,k):
                        nxt=tuple(sorted(base+list(keep)+[7+i]))
                        if len(nxt)>size-i:continue
                        cov=0
                        for w in nxt:cov|=separated(bits[w])
                        if cov!=ALLPAIRS:continue
                        if dfs(nxt,remaining,budget-k,(b,a)):return True
                path.pop()
                bits.pop()
        return False
    try:
        status='WITNESS' if dfs(tuple(range(7)),mult,extra,(-1,-1)) else 'EXHAUSTED'
    except TimedOut:
        status='UNKNOWN'
    if witness:
        assert len(witness)==size
        assert all(evaluate(witness,row)==target(row) for row in range(128))
    return dict(status=status,nodes=nodes,seconds=round(time.monotonic()-start,4),circuit=witness)


def controls():
    g=[(2,3,1),(2,4,1),(3,4,0),(5,6,0),(5,7,1),(6,8,1),(9,10,1),(0,11,0),
       (1,12,0),(14,15,1),(13,16,1)]
    for candidate in (g,g[:-1]+[(13,16,3),(13,17,1)]):
        n=len(candidate)
        mult=tuple(sum(v in (a,b) for a,b,op in candidate) for v in range(7))
        extra=n-6-sum(x-1 for x in mult)
        d=solve(n,mult,extra,2,planted=candidate)
        assert d['status']=='WITNESS'
        print(json.dumps(d),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--seconds',type=float,default=2)
    p.add_argument('--size',type=int,default=10)
    p.add_argument('--bucket',type=int)
    p.add_argument('--control',action='store_true')
    p.add_argument('--unsorted',action='store_true')
    p.add_argument('--no-sym',action='store_true')
    a=p.parse_args()
    if a.control:
        controls()
        raise SystemExit
    for idx,(mult,extra) in enumerate(configurations(a.size,not a.no_sym)):
        if a.bucket is None or idx==a.bucket:
            result=solve(a.size,mult,extra,a.seconds,order=not a.unsorted)
            print(json.dumps(dict(idx=idx,size=a.size,mult=mult,internal_extra=extra,**result)),flush=True)
