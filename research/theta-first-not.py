#!/usr/bin/env python3
"""Exact bounded seven-vertex theta first-inverter frontier search (L-meta-1940).
Separate searches for numbers of further NOTs and for retaining/dropping x.
Positive controls replay a planted optimum11 monotone circuit with one idle
inverter prepended at cost12. Every discovered witness is replayed on all rows.
"""
import argparse, functools, itertools, json, time

E=((0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1))
def target(s): return any(s>>a&1 and s>>b&1 for a,b in E)
U=(1<<128)-1
X=tuple(sum(1<<s for s in range(128) if s>>i&1) for i in range(7))
F=sum(1<<s for s in range(128) if target(s))
POS=[s for s in range(128) if target(s)]
NEG=[s for s in range(128) if not target(s)]
W=len(NEG)
LOW=(1<<W)-1
STRIPES=sum(1<<(i*W) for i in range(len(POS)))
PAIR=STRIPES*LOW
def byte_table(basis):
    ts=[]
    for k in range(16):
        t=[0]
        for i in range(8):
            value=basis.get(k*8+i,0); t += [s|value for s in t]
        ts.append(t)
    return ts
TP=byte_table({s:1<<(i*W) for i,s in enumerate(POS)})
TN=byte_table({s:1<<i for i,s in enumerate(NEG)})
@functools.lru_cache(maxsize=100000)
def cuts(z):
    p=n=0
    for a,b in zip(TP,TN):
        k=z&255; z>>=8; p|=a[k]; n|=b[k]
    return p*(LOW^n), (STRIPES^p)*n

def admissible(ws,k,t):
    if len(ws)+t>k+1 or not 0<=t<=k: return False
    fwd=rev=0
    for w in ws:
        u,v=cuts(w); fwd|=u
        if t:rev|=v
    if not t:return fwd==PAIR
    if fwd|rev!=PAIR:return False
    if t>1 or fwd==PAIR:return True
    # To repair every order violation p<=n, the input to the only remaining
    # NOT has to be 0 on all such p and 1 on all such n. It is monotone in the
    # current frontier. Hence no violating n may itself be <= a violating p.
    d=PAIR^fwd; rev=PAIR^rev; nset=0; pblocks=0; bit=1
    while d:
        v=d&LOW
        if v: nset|=v; pblocks|=bit
        d>>=W; bit<<=W
    return not rev & (pblocks*nset)

class Timeout(Exception):pass

def verify(j,path):
    gates=[('not',j,-1)]
    ws={w:i for i,w in enumerate(X)};ws[U^X[j]]=7
    for op,a,b,out in path:
        gates.append((op,ws[a],-1 if b is None else ws[b]))
        ws[out]=6+len(gates)
    circuit={'gates':gates,'output':ws[F]}
    for r in range(128):
        v=[bool(r>>i&1) for i in range(7)]
        for op,a,b in gates:
            v.append(not v[a] if op=='not' else v[a] and v[b] if op=='and' else v[a] or v[b])
        assert v[circuit['output']]==target(r)
    return circuit

def go(j,negative_count,keep,limit,memo):
    root=tuple(sorted([X[i] for i in range(7) if i!=j or keep]+[U^X[j]]))
    visited=0;start=time.monotonic(); path=[]; found=None
    @functools.lru_cache(maxsize=memo)
    def visit(ws,k,t):
        nonlocal visited,found
        visited+=1
        if visited%128==0 and time.monotonic()-start>limit:raise Timeout
        if F in ws and t==0:
            found=verify(j,path);return True
        if not k or not admissible(ws,k,t):return False
        live=set(ws)
        def child(op,a,b,z,newt):
            if z in live or z in (0,U):return False
            rest=live-{a} if b is None else live-{a,b}
            rest.add(z); cap=k-newt
            variants=[()] if len(rest)==cap else [(),(a,)] if b is None else [(),(a,),(b,),(a,b)]
            for add in variants:
                if len(rest)+len(add)>cap:continue
                w2=tuple(sorted((*rest,*add)))
                # Separation is cheaper than entering the transposition table
                # for the large number of immediately impossible choices.
                if not admissible(w2,k-1,newt):continue
                path.append((op,a,b,z))
                if visit(w2,k-1,newt):return True
                path.pop()
            return False
        if t:
            for a in ws:
                if child('not',a,None,U^a,t-1):return True
        if k>t:
            for a,b in itertools.combinations(ws,2):
                if child('and',a,b,a&b,t) or child('or',a,b,a|b,t):return True
        return False
    try:
        passed=visit(root,10,negative_count)
        verdict='WITNESS' if passed else 'EXHAUSTED'
    except Timeout:
        verdict='UNKNOWN'
    print(json.dumps(dict(head=j,keep=keep,further_nots=negative_count,status=verdict,
                         states=visited,seconds=round(time.monotonic()-start,3),circuit=found)),flush=True)
    visit.cache_clear()
    return verdict

def control():
    # Theta stars centered at 0,1,3,5 (0/1/3/5 vertex cover).
    pairs=[('or',2,3),('or',7,5),('and',0,8),('or',2,4),('or',10,6),('and',1,11),
           ('and',3,4),('and',5,6),('or',9,12),('or',15,13),('or',16,14)]
    vals=list(X)
    for op,a,b in pairs:
        vals.append(vals[a]&vals[b] if op=='and' else vals[a]|vals[b])
    assert vals[-1]==F
    for j in (0,2,3):
        # An unused first NOT may be dropped at the 12-gate bound.
        with_prefix=[('not',j,-1)]+[(op,a+(a>=7),b+(b>=7)) for op,a,b in pairs]
        for s in range(128):
            d=[bool(s>>i&1) for i in range(7)]
            for op,a,b in with_prefix:
                d.append(not d[a] if op=='not' else d[a] and d[b] if op=='and' else d[a] or d[b])
            assert d[-1]==target(s)
    print('verified three 12-gate controls on 128 rows and the 11-gate monotone optimum')
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--head',type=int,choices=[0,2,3])
    p.add_argument('--further-nots',type=int,choices=range(5))
    p.add_argument('--keep',type=int,choices=(0,1))
    p.add_argument('--seconds',type=float,default=10,help='per bucket, elapsed seconds')
    p.add_argument('--memo',type=int,default=120000)
    p.add_argument('--control',action='store_true')
    a=p.parse_args()
    if a.seconds<=0 or a.memo<1:p.error('require positive bounds')
    if a.control:control()
    for j in [a.head] if a.head is not None else [0,2,3]:
        for t in [a.further_nots] if a.further_nots is not None else [0,1]:
            for keep in [a.keep] if a.keep is not None else [0,1]:
                if go(j,t,keep,a.seconds,a.memo)=='WITNESS':raise SystemExit
