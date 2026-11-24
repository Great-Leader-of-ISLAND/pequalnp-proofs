"""Quantify full seven-input raw-gate relocation by its exact admitted unordered search tree."""
from itertools import combinations
from functools import lru_cache
from time import monotonic
from theta1924front import X,ALL,F,ALLPAIRS,PERMS
from theta1924free import separated
pairs=list(combinations(range(7),2));order=[5,61,69,9,0,14,6,10,65,45,2,1,13];rs={};first={}
for i,(a,b) in enumerate(pairs):
 for k in range(4):
  orb=[]
  for p in PERMS:
   u,v=p[a],p[b];op=k if u<v or k<2 else 5-k;orb.append(4*pairs.index(tuple(sorted((u,v))))+op)
  z=(X[a]&X[b],X[a]|X[b],X[a]&(ALL^X[b]),X[b]&(ALL^X[a]))[k];rs[z]=order.index(min(orb))+1 if min(orb) in order else 0;first[4*i+k]=z

def measure(bound,initial):
 @lru_cache(None)
 def go(m,ws):
  assert F not in ws
  cnt=1
  for a,b in combinations(ws,2):
   rest=tuple(w for w in ws if w not in (a,b));cover=0
   for w in rest:cover|=separated(w)
   ca=separated(a);cb=separated(b)
   for z in (a&b,a|b,a&(ALL^b),b&(ALL^a)):
    if z==0 or z in ws or rs.get(z,20)<bound:continue
    cov=cover|separated(z)
    for keep,extra in [((),0),((a,),ca),((b,),cb),((a,b),ca|cb)]:
     if len(rest)+1+len(keep)>m or cov|extra!=ALLPAIRS:continue
     cnt+=go(m-1,tuple(sorted((*rest,z,*keep))))
  return cnt
 count=go(9,tuple(sorted((first[initial],*X))));un=go.cache_info().currsize;go.cache_clear();return count,un
for i,gate in enumerate(order):
 t=monotonic();data=[measure(bound,gate) for bound in (0,1,i+1)];print('class',gate,'old,rawBan,rankBan',data,'seconds',round(monotonic()-t,2),flush=True)
