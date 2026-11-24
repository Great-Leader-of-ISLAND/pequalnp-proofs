"""Canalizing and cotree contradictions at a no-sharing frontier, using all 128 rows."""
from CoThetaSeedDiagnostic import raw,target,allrows,sep,ops,everything
from itertools import combinations
from functools import lru_cache
from time import monotonic
import json
NLS=(1,2,4,8,14,13,11,7);UN=(0,15,3,5,10,12)
@lru_cache(None)
def masks(n):
 return [sum(1<<k for k in range(1<<n) if not k&(1<<i)) for i in range(n)]
@lru_cache(100000)
def contradiction(ws):
 n=len(ws); patterns={0:allrows}
 for i,w in enumerate(ws):
  q={}
  for k,mask in patterns.items():
   a=mask&w;b=mask^a
   if a:q[k|1<<i]=a
   if b:q[k]=b
  patterns=q
 P=sum(1<<k for k,v in patterns.items() if v&target)
 N=sum(1<<k for k,v in patterns.items() if v&(allrows^target))
 if P&N:return 4
 offs=masks(n)
 for i in range(n):
  u=1<<i;basis=offs[i]
  if (P&(N>>u)&basis) and (N&(P>>u)&basis):return 1
 plus=[0]*n;minus=[0]*n
 for i,j in combinations(range(n),2):
  u=1<<i;v=1<<j;basis=offs[i]&offs[j]
  p=[(P>>offset)&basis for offset in (0,u,v,u+v)]
  z=[(N>>offset)&basis for offset in (0,u,v,u+v)]
  def clashes(t):
   return (z[0] if t&1 else p[0])|(z[1] if t&2 else p[1])|(z[2] if t&4 else p[2])|(z[3] if t&8 else p[3])
  needs=basis
  for t in UN:needs&=clashes(t)
  if not needs:continue
  nf=[t for t in NLS if not needs&clashes(t)]
  if not nf:return 2
  if all(t.bit_count()==1 for t in nf):tag=minus
  elif all(t.bit_count()==3 for t in nf):tag=plus
  else:continue
  tag[i]|=1<<j;tag[j]|=1<<i
 def connected(group,edge):
  stack=hit=group&-group
  while stack:
   bit=stack&-stack;stack^=bit
   add=edge[bit.bit_length()-1]&group&~hit;hit|=add;stack|=add
  return hit==group
 for group in range(1<<n):
  if group.bit_count()>=4 and connected(group,plus) and connected(group,minus):return 3
 return 0
def run(seed,method):
 t=monotonic();at=[0]*5;counter=0
 @lru_cache(220000)
 def go(m,ws):
  nonlocal counter
  counter+=1
  if counter%512==0 and monotonic()-t>240:raise TimeoutError
  if m==0 or len(ws)>m+1:return 1
  if method and len(ws)==m+1:
   fail=contradiction(ws);at[fail]+=1
   if 0<fail<=method:return 1
  total=1
  for i,j in combinations(range(len(ws)),2):
   a,b=ws[i],ws[j];rest=ws[:i]+ws[i+1:j]+ws[j+1:];cover=0
   for w in rest:cover|=sep(w)
   for z in ops(a,b):
    if not z or z in ws:continue
    assert z!=target
    cc=cover|sep(z)
    for keep,extra in (((),0),((a,),sep(a)),((b,),sep(b)),((a,b),sep(a)|sep(b))):
     if len(rest)+len(keep)+1<=m and cc|extra==everything:total+=go(m-1,tuple(sorted((*rest,*keep,z))))
  return total
 try:tot=go(10,tuple(sorted((*raw,raw[0]|raw[seed]))))
 except TimeoutError:tot='timeout'
 print(json.dumps(dict(seed=seed,prune=method,calls=tot,states=counter,types=at,seconds=round(monotonic()-t,3))),flush=True)
 go.cache_clear()
for seed in (2,3):
 for method in (3,1,0):run(seed,method)
