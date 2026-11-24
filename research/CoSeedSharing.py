"""Measure exact savings from reusing the proofs of complete, unordered frontier states."""
from collections import Counter,defaultdict
from itertools import combinations
from pathlib import Path
import json,re
s=Path(__file__).with_name('CoSeedBenchmark.lean').read_text().split('def raw : List Word := [',1)[1].split(']',1)[0]
raw=[tuple(int(v,16) for v in q) for q in re.findall(r'\((0x[0-9a-f]+),(0x[0-9a-f]+)\)',s)]
mask=(1<<440)-1;goal=(mask,0);zero=(0,0)
def ops(a,b):
    p,n=a;s,t=b
    return ((p&s,n&t),(p|s,n|t),(p&~s,n&~t),(s&~p,t&~n))
def children(m,ws):
    if m==0 or len(ws)>m+1:return []
    cs=[]
    for i,q in combinations(range(len(ws)),2):
        a,b=ws[i],ws[q];rest=ws[:i]+ws[i+1:q]+ws[q+1:];base=0
        for p,n in rest:base|=p^n
        for z in ops(a,b):
            if z==zero or z in ws:continue
            assert z!=goal
            cover=base|(z[0]^z[1])
            for keep,add in (((),0),((a,),a[0]^a[1]),((b,),b[0]^b[1]),((a,b),(a[0]^a[1])|(b[0]^b[1]))):
                if len(rest)+len(keep)+1<=m and (cover|add)==mask:cs.append(tuple(sorted((*rest,*keep,z))))
    return cs
def solve(j):
    occurrence=[Counter() for _ in range(11)];tree=[{} for _ in range(11)];parents=[{} for _ in range(11)]
    start=tuple(sorted((*raw,ops(raw[0],raw[j])[1])));occurrence[10][start]=1
    for m in range(10,0,-1):
        for w,n in occurrence[m].items():
            cs=children(m,w);parents[m][w]=cs
            for k in cs:occurrence[m-1][k]+=n
    for m in range(11):
        for w in occurrence[m]:tree[m][w]=1+sum(tree[m-1][c] for c in parents[m].get(w,[]))
    total=tree[10][start]
    print('seed',j,'total',total,flush=True)
    for m in range(1,10):
        vals=sorted(((n-1)*(tree[m][w]-1) for w,n in occurrence[m].items()),reverse=True)
        tight=sum((n-1)*(tree[m][w]-1) for w,n in occurrence[m].items() if len(w)==m+1)
        print(json.dumps(dict(j=j,m=m,at=len(vals),savings=[round(sum(vals[:K])/total,3) for K in [10,100,500,1500]],all=round(sum(vals)/total,3),tight=round(tight/total,3))),flush=True)
    for limit in [100,500,1500]:
        seen=[Counter() for _ in range(11)];seen[10][start]=1;work=0;nums=[]
        for m in range(10,0,-1):
            benefit=sorted(((n-1)*(tree[m][w]-1),w) for w,n in seen[m].items() if n>1)
            chosen=set(w for v,w in benefit[-limit:] if v>=5);nums.append(len(chosen))
            work+=sum(seen[m].values())
            for w,n in seen[m].items():
                for c in parents[m][w]:seen[m-1][c]+=1 if w in chosen else n
        work+=sum(seen[0].values())
        print(json.dumps(dict(j=j,perlevel=limit,certificates=sum(nums),calls=work,fraction=round(work/total,3))),flush=True)
for j in (2,3):solve(j)
