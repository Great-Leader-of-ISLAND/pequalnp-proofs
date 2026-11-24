"""Bounded exact search for a seven-input signed circuit supplied an adjacent-input OR."""
from functools import lru_cache
from itertools import combinations
from time import monotonic
import argparse,json

edges=[(0,2),(1,2),(0,3),(3,4),(1,4),(0,5),(5,6),(1,6)]
n=128; allrows=(1<<n)-1
raw=tuple(sum(1<<r for r in range(n) if (r>>i)&1) for i in range(7))
target=0
for a,b in edges: target|=raw[a]&raw[b]
pos=[r for r in range(n) if target>>r&1]
neg=[r for r in range(n) if not target>>r&1]
width=len(neg); low=(1<<width)-1; stripe=sum(1<<(i*width) for i in range(len(pos))); everything=stripe*low

def tab(d):
    tabs=[]
    for i in range(0,n,8):
        t=[0]
        for j in range(8):t += [v|d.get(i+j,0) for v in t]
        tabs.append(t)
    return tabs

P=tab({r:1<<(i*width) for i,r in enumerate(pos)});N=tab({r:1<<i for i,r in enumerate(neg)})
@lru_cache(90000)
def sep(z):
    p=v=0
    for pp,nn in zip(P,N):
        k=z&255;z>>=8;p|=pp[k];v|=nn[k]
    return p*(low^v)|(stripe^p)*v

def ops(a,b):return a&b,a|b,a&(allrows^b),b&(allrows^a)

class Limit(Exception):pass

def solve(edge,seconds,depth=10):
    seed=raw[edge[0]]|raw[edge[1]]; start=monotonic();nodes=0;top=0
    @lru_cache(140000)
    def go(m,ws):
        nonlocal nodes
        nodes+=1
        if nodes%128==0 and monotonic()-start>=seconds:raise Limit
        if target in ws:return ()
        if m==0 or len(ws)>m+1:return None
        masks=[sep(x) for x in ws]
        for i,j in combinations(range(len(ws)),2):
            a,b=ws[i],ws[j];rest=tuple(w for k,w in enumerate(ws) if k not in (i,j))
            coverage=0
            for k,mask in enumerate(masks):
                if k!=i and k!=j:coverage|=mask
            for kind,z in enumerate(ops(a,b)):
                if z==0 or z in ws:continue
                if z==target:return ((a,b,kind,z),)
                v=coverage|sep(z)
                for keep,add in (((),0),((a,),masks[i]),((b,),masks[j]),((a,b),masks[i]|masks[j])):
                    if len(rest)+len(keep)+1>m or (v|add)!=everything:continue
                    sol=go(m-1,tuple(sorted((*rest,*keep,z))))
                    if sol is not None:return ((a,b,kind,z),)+sol
        return None
    try:
        path=go(depth,tuple(sorted((*raw,seed))))
        status='excluded' if path is None else 'witness'
    except Limit:
        status='timeout';path=None
    cache=go.cache_info();go.cache_clear()
    if path:
        vals=list(raw)+[seed];marked=[]
        for a,b,k,z in path:
            marked.append((vals.index(a),vals.index(b),k))
            assert z==ops(a,b)[k]
            vals.append(z)
        assert vals[-1]==target;path=marked
    print(json.dumps(dict(edge=edge,depth=depth,nodes=nodes,cache_hits=cache.hits,status=status,path=path,seconds=round(monotonic()-start,3))),flush=True)

def control():
    # An eleven-operation theta circuit, shortened by supplying its first OR.
    seed=raw[2]|raw[3];w=list(raw)+[seed]
    for a,b,k in [(2,4,1),(3,4,0),(5,6,0),(5,7,1),(6,8,1),(9,10,1),(0,11,0),(1,12,0),(14,15,1),(13,16,1)]:
        w.append(ops(w[a],w[b])[k])
    assert w[-1]==target
    print('planted 10 paid steps verified on all 128 rows',flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=200);p.add_argument('--depth',type=int,default=10)
    a=p.parse_args();control()
    for e in [(0,2),(0,3)]:solve(e,a.seconds,a.depth)
