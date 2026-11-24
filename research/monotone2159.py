"""Live-wire exact search on a fixed first OR. The timeout is not a certificate."""
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import argparse, time

E=((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5))
edges=[(1<<i)|(1<<j) for i,j in E]
def graph(row):return any(row&e==e for e in edges)
rows=range(512)
maxneg=[q for q in rows if not graph(q) and all(graph(q|1<<i) for i in range(9) if not q>>i&1)]
pairs=list(product(edges,maxneg))
ONE=(1<<512)-1
X=tuple(sum(1<<q for q in rows if q>>i&1) for i in range(9))
GOAL=sum(1<<q for q in rows if graph(q))
HEAD=X[0]|X[2]
ALL=(1<<len(pairs))-1
# Saturated deletion lower bounds from checked 1007 (13) and 517 plus a leaf (12).
lower=(12,12,12,12,13,12,13,13,12)
off=[ONE^x for x in X]
free=[{0,m,*[x&m for x in X]} for m in off]

@lru_cache(maxsize=32768)
def separates(x):
    result=0
    for j,p in enumerate(edges):
        if x>>p&1:
            for k,q in enumerate(maxneg):
                if not x>>q&1:result |= 1<<(j*len(maxneg)+k)
    return result

def covers(ws):
    cover=0
    for x in ws:cover |= separates(x)
    return cover==ALL

def loss(z,a,b,ws,budget):
    new=[]
    for i,(m,base,left) in enumerate(zip(off,free,budget)):
        projected=z&m
        # A prior signal (including a retired gate's operand) remains available in the shortened circuit.
        lost=projected in base or any(projected==u&m for u in ws)
        if lost and left==0:return None
        new.append(left-int(lost))
    return tuple(new)

def follow(ws,k,slack):
    for a,b in combinations(ws,2):
        base=tuple(w for w in ws if w!=a and w!=b)
        basecover=0
        for w in base:basecover|=separates(w)
        for op,z in (('and',a&b),('or',a|b)):
            if z in ws or z in (0,ONE):continue
            bywire=basecover|separates(z)
            left=None
            for kept in ((),(a,),(b,),(a,b)):
                if len(base)+1+len(kept)>k:continue
                cov=bywire
                for w in kept:cov|=separates(w)
                if cov!=ALL:continue
                if left is None:
                    left=loss(z,a,b,ws,slack)
                    if left is None:break
                yield tuple(sorted((*base,z,*kept))),left,(op,a,b,z)

def root(size):
    return tuple(sorted((*X,HEAD))),loss(HEAD,X[0],X[2],X,tuple(size-b for b in lower))

def control():
    cv=next(c for c in combinations(range(9),5) if 1 in c and all(a in c or b in c for a,b in E))
    stars={c:[] for c in cv}
    for a,b in E:
        c=1 if (a,b) in ((0,1),(1,2)) else a if a in cv else b
        stars[c].append(b if c==a else a)
    assert all(stars.values())
    steps=[('or',X[0],X[2],HEAD)]; out=[]
    def add(op,a,b):
        z=a|b if op=='or' else a&b
        steps.append((op,a,b,z))
        return z
    for c,ns in stars.items():
        if c==1:
            v=HEAD
            for j in ns:
                if j not in (0,2):v=add('or',v,X[j])
        else:
            v=X[ns[0]]
            for j in ns[1:]:v=add('or',v,X[j])
        out.append(add('and',X[c],v))
    v=out[0]
    for w in out[1:]:v=add('or',v,w)
    assert len(steps)==16 and v==GOAL
    needed={GOAL}; layers=[None]*16
    for j in reversed(range(16)):
        _,a,b,z=steps[j];assert z in needed
        layers[j]=tuple(sorted(needed));needed=(needed-{z})|{a,b}
    ws,budget=root(16)
    assert ws==layers[0]
    for i in range(1,16):
        ans=next((entry for entry in follow(ws,16-i,budget) if entry[0]==layers[i] and entry[2][0]==steps[i][0] and entry[2][3]==steps[i][3] and set(entry[2][1:3])==set(steps[i][1:3])),None)
        assert ans is not None,(i,cv)
        ws,budget,_=ans
    print('control: all 512 assignments, all 15 suffix transitions; first OR(0,2); 16 gates;',len(pairs),'oriented tests',flush=True)

def main():
    p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=0);p.add_argument('--total',type=float,default=300);opt=p.parse_args()
    control()
    ws,budget=root(15)
    for i,x in enumerate(X):
        assert not covers(tuple(y for y in ws if y!=x)),i
    frontier=list(follow(ws,14,budget));print('necessary raw signals: 9; live head second-step states',len(frontier),flush=True)
    if not opt.seconds:return
    end=time.monotonic()+opt.total; complete=[]; unknown=[]; nodes=0
    class Bound(Exception):pass
    for j,(w,b,g) in enumerate(frontier):
        if time.monotonic()>=end:break
        limit=min(end,time.monotonic()+opt.seconds)
        @lru_cache(maxsize=6000)
        def visit(ws,k,b):
            nonlocal nodes
            nodes+=1
            if time.monotonic()>=limit:raise Bound
            if GOAL in ws:return ()
            if not k:return None
            for nxt,new_budget,gate in follow(ws,k,b):
                path=visit(nxt,k-1,new_budget)
                if path is not None:return (gate,)+path
            return None
        try:
            path=visit(w,13,b)
            if path is not None:
                path=(('or',X[0],X[2],HEAD),g)+path; mapping={x:i for i,x in enumerate(X)}; pins=[]
                for op,a,b,z in path:
                    assert a in mapping and b in mapping and z==(a|b if op=='or' else a&b)
                    pins.append((op,mapping[a],mapping[b]));mapping[z]=8+len(pins)
                assert path[-1][3]==GOAL and len(pins)<=15
                print('FULL WITNESS',pins,flush=True);return
            complete.append(j)
        except Bound:unknown.append(j)
        visit.cache_clear()
    print('completed second-step indices',complete,'unknown',unknown,'untested',len(frontier)-len(complete)-len(unknown),'visited',nodes,flush=True)
if __name__=='__main__':main()
