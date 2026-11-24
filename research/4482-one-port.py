"""Exact global search for five raw observations plus one computed monotone observation."""
import argparse
from functools import lru_cache
from itertools import combinations
from time import monotonic

E=((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5))
F=[any(r>>i&r>>j&1 for i,j in E) for r in range(512)]
class End(Exception):pass
def case(b,g,wall):
    labels={}
    for r,f in enumerate(F):labels[r&b]=labels.get(r&b,0)|(1<<f)
    pos=[r for r in range(512) if F[r] and labels[r&b]==3]
    neg=[r for r in range(512) if not F[r] and labels[r&b]==3]
    P=[p for p in pos if not any(t!=p and t&p==t for t in pos)]
    N=[n for n in neg if not any(t!=n and t&n==n for t in neg)]
    amax=(1<<len(P))-1;dmax=(1<<len(N))-1
    def raw(i,r):return bool(r&5) if i==9 else (r>>i)&1
    src=[(sum(1<<j for j,p in enumerate(P) if raw(i,p)),sum(1<<j for j,n in enumerate(N) if not raw(i,n))) for i in range(10)]
    goal=(amax,dmax)
    @lru_cache(None)
    def rect(w):
        a,d=w
        return sum(d<<(j*len(N)) for j in range(len(P)) if a>>j&1)
    mask=rect(goal);memo={};choice=[];nroot=0
    def search(wires,left,path):
        if any(w==goal for _,w in wires):
            out=next(i for i,w in wires if w==goal)
            if out<10:
                if not left:return
                path=path+[(True,out,out)];out=9+len(path)
            choice.extend([path,out]);raise End
        k=len(wires)
        if left==0 or k>left+1:return
        key=tuple(sorted(w for _,w in wires))
        if memo.get(key,-1)>=left:return
        memo[key]=left
        if len(memo)%32==0 and monotonic()>wall:raise TimeoutError
        for i,j in combinations(range(k),2):
            li,a=wires[i];lj,c=wires[j]
            other=[e for n,e in enumerate(wires) if n not in (i,j)]
            covered=0
            for _,u in other:covered|=rect(u)
            missing=mask^covered
            for op,w in [(False,(a[0]&c[0],a[1]|c[1])),(True,(a[0]|c[0],a[1]&c[1]))]:
                if w in key or not rect(w):continue
                debt=missing&~rect(w);new=(10+len(path),w)
                for retain in (0,1,2,3):
                    if len(other)+1+bin(retain).count('1')>left:continue
                    if debt&~((rect(a) if retain&1 else 0)|(rect(c) if retain&2 else 0)):continue
                    nxt=other+[new]+([wires[i]] if retain&1 else [])+([wires[j]] if retain&2 else [])
                    search(nxt,left-1,path+[(op,li,lj)])
    try:
        for k in range(1,min(g+1,10)+1):
            for ids in combinations(range(10),k):
                union=0
                for i in ids:union|=rect(src[i])
                if union!=mask:continue
                nroot+=1
                search([(i,src[i]) for i in ids],g,[])
    except TimeoutError:return 'UNKNOWN',nroot,len(memo),None
    except End:
        path,out=choice
        seen={}
        for r in range(512):
            v=[raw(i,r) for i in range(10)]
            for op,i,j in path:v.append(v[i]|v[j] if op else v[i]&v[j])
            key=(r&b,v[out])
            assert seen.setdefault(key,F[r])==F[r]
        return 'WITNESS',nroot,len(memo),choice
    return 'EXHAUSTED',nroot,len(memo),None
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--mask',type=int,action='append')
    p.add_argument('--gates',type=int,default=7)
    p.add_argument('--seconds',type=float,default=.7)
    a=p.parse_args();deadline=monotonic()+a.seconds
    items=a.mask if a.mask else [b for b in range(512) if bin(b).count('1')==5]
    count={'EXHAUSTED':0,'WITNESS':0,'UNKNOWN':0};total=0;roots=0
    for b in items:
        if monotonic()>deadline:break
        status,nr,ns,w=case(b,a.gates,deadline);roots+=nr;total+=ns;count[status]+=1
        print(status,b,'roots',nr,'states',ns,*([w] if w else []))
        if w:break
    print('totals',count,'total_masks',len(items),'candidate_roots',roots,'states',total)
