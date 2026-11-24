"""Enumerate signed-size-ten theta topologies with their one ordinary NOT.

Completeness relies on the fanout and formula arguments in theta1924-research.md.
The program prints UNKNOWN on a budget exhaustion; only EXHAUSTED closes a bucket.
"""
import argparse
import functools
import itertools
import json
import time
from theta1924 import EDGES, target

V = range(7)
N = 128
ALL = (1<<N)-1
X = tuple(sum(1<<r for r in range(N) if r & (1<<i)) for i in V)
F = sum(1<<r for r in range(N) if target(r))
POS = [r for r in range(N) if target(r)]
NEG = [r for r in range(N) if not target(r)]
NW = len(NEG)
LOW = (1<<NW)-1
STRIPE = sum(1<<(i*NW) for i in range(len(POS)))
ALLPAIRS = STRIPE*LOW
SENS = []
for x in V:
    lo = sum(1<<r for r in NEG if not r&(1<<x) and target(r|(1<<x)))
    SENS.append((lo,lo<<(1<<x)))
PERMS = ((0,1,2,3,4,5,6),(0,1,2,5,6,3,4),(1,0,2,4,3,6,5),(1,0,2,6,5,4,3))


def tables(vals):
    ans=[]
    for off in range(0,128,8):
        row=[0]
        for j in range(8):
            v=vals.get(off+j,0)
            row.extend([x|v for x in row])
        ans.append(row)
    return ans


TP=tables({r:1<<(i*NW) for i,r in enumerate(POS)})
TN=tables({r:1<<i for i,r in enumerate(NEG)})


@functools.lru_cache(maxsize=90000)
def cuts(sig):
    p=n=0
    for plus,minus in zip(TP,TN):
        v=sig&255
        sig>>=8
        p|=plus[v]
        n|=minus[v]
    return p*(LOW^n),(STRIPE^p)*n


def can_finish(live, neg, bits):
    fwd=rev=0
    for i in live:
        u,v=cuts(bits[i])
        fwd|=u
        if neg is None: rev|=v
        if neg==i: fwd|=v
    if fwd==ALLPAIRS:
        return True
    if neg is not None or fwd|rev!=ALLPAIRS:
        return False
    # One future inversion must reverse every order-violating pair. The
    # monotone signal feeding it must be 0 on those p, 1 on those n.
    missing=ALLPAIRS^fwd
    required_n=required_p=0
    si=1
    while missing:
        part=missing&LOW
        if part:
            required_n|=part
            required_p|=si
        missing>>=NW
        si<<=NW
    return not (ALLPAIRS^rev) & (required_p*required_n)


def options():
    def eligible(d):
        rest=set(V)-set(d)
        edges=[set(e) for e in EDGES if set(e)<=rest]
        return not edges or bool(set.intersection(*edges))
    for k in (1,2):
        for d in itertools.combinations(V,4-k):
            orbit=[tuple(sorted(perm[i] for i in d)) for perm in PERMS]
            if min(orbit)!=d or (k==1 and not eligible(d)):
                continue
            yield k,d


class TimedOut(Exception):
    pass


def solve(k,d,seconds,planted=None):
    size=len(planted) if planted else 10
    start=time.monotonic()
    count=0
    early=None
    bits=list(X)
    path=[]
    firstpairs=set()
    group=[perm for perm in PERMS if tuple(sorted(perm[i] for i in d))==d]
    for a,b in itertools.combinations(d,2):
        orbit=[tuple(sorted((perm[a],perm[b]))) for perm in group]
        if (b,a)==min((y,x) for x,y in orbit):
            firstpairs.add((a,b))

    def visit(live,raw_left,spent,neg,last_key,primaries):
        nonlocal count,early
        count+=1
        if count%256==0 and time.monotonic()-start>seconds:
            raise TimedOut
        i=len(path)
        if len(live)>size+1-i: return False
        for a,b in itertools.combinations(live,2):
            key=(b,a)
            if planted and (a,b)!=planted[i][1:3]:continue
            if key<last_key or (not i and not planted and (a,b) not in firstpairs):
                continue
            raw=b<7
            if raw and (a not in d or b not in d or (a,b) in primaries or
                        (not planted and len(primaries)>=3-k)):
                continue
            if i==size-1 and (len(live)!=2 or any(raw_left[x]>1 for x in (a,b) if x<7)
                         or len(spent)!=k):
                continue
            left=bits[a]
            right=bits[b]
            inversions=[None]
            for v in (a,b):
                if (neg is None or neg==v) and (v>=7 or v in d):
                    inversions.append(v)
            rest_raw=list(raw_left)
            for v in (a,b):
                if v<7:rest_raw[v]-=1
            base=[w for w in live if w not in (a,b) or (w<7 and rest_raw[w]>0)]
            saveable=[w for w in (a,b) if w>=7 and w not in spent]
            for flip in inversions:
                l = ALL^left if flip==a else left
                r = ALL^right if flip==b else right
                neg2 = flip if flip is not None else neg
                for op,z in (('and',l&r),('or',l|r)):
                    if planted and (op,a,b,flip)!=planted[i]:continue
                    if i==size-1:
                        if z==F:
                            early=path+[(op,a,b,flip)]
                            return True
                        continue
                    if z in (0,ALL,F) or z in bits or (ALL^z) in bits:
                        continue
                    bad=False
                    for w in (a,b):
                        if w<7 and w not in d:
                            low,high=SENS[w]
                            if z&low or z&high!=high:
                                bad=True
                                break
                    if bad:continue
                    bits.append(z)
                    path.append((op,a,b,flip))
                    for ns in range(min(k-len(spent),len(saveable))+1):
                        for saved in itertools.combinations(saveable,ns):
                            next_live=tuple(sorted(base+list(saved)+[7+i]))
                            if len(next_live)>size-i or not can_finish(next_live,neg2,bits):
                                continue
                            if visit(next_live,rest_raw,spent|frozenset(saved),neg2,key,
                                     primaries|{(a,b)} if raw else primaries):
                                return True
                    path.pop()
                    bits.pop()
        return False

    try:
        found=visit(tuple(V),[1+(i in d) for i in V],frozenset(),None,(-1,-1),frozenset())
        status='WITNESS' if found else 'EXHAUSTED'
    except TimedOut:
        status='UNKNOWN'
    if early:
        assert len({f for _,_,_,f in early if f is not None})<=1
        for row in range(128):
            vals=[bool(row & (1<<i)) for i in V]
            for op,a,b,flip in early:
                left=vals[a]^(flip==a)
                right=vals[b]^(flip==b)
                vals.append((left and right) if op=='and' else (left or right))
            assert vals[-1]==target(row)
    print(json.dumps({'shared':k,'repeated':d,'status':status,'visited':count,
                      'seconds':round(time.monotonic()-start,3),'circuit':early}),flush=True)
    return status


def controls():
    raw=[('or',2,3),('or',2,4),('and',3,4),('and',5,6),('or',5,7),
         ('or',6,8),('or',9,10),('and',0,11),('and',1,12),('or',14,15),('or',13,16)]
    formula=[(op,a,b,None) for op,a,b in raw]
    assert solve(0,(2,3,4,5,6),10,formula)=='WITNESS'
    signed=formula[:-1]+[('and',13,16,13),('or',13,17,None)]
    assert solve(1,(2,3,4,5,6),10,signed)=='WITNESS'


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--seconds',type=float,default=15)
    p.add_argument('--bucket',type=int)
    p.add_argument('--list',action='store_true')
    p.add_argument('--control',action='store_true')
    a=p.parse_args()
    if a.control:
        controls()
        raise SystemExit
    for i,(k,d) in enumerate(options()):
        if a.list:
            print(i,k,d)
        elif a.bucket is None or i==a.bucket:
            solve(k,d,a.seconds)
