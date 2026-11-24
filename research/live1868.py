"""Bounded signed DAG enumeration on fixed paired rows for a two-gate prefix."""
from functools import lru_cache
from itertools import combinations
import json, time
from prefix1868 import labels, raw, head, states, ortable
from pathlib import Path
# Use all sensitive cube edges and all boundary products. A live state's
# outputs must tell these opposite-label assignments apart.
positive=[x for x in range(512) if labels[x] and all(not labels[x^(1<<j)] for j in range(9) if x>>j&1)]
negative=[x for x in range(512) if not labels[x] and all(labels[x|(1<<j)] for j in range(9) if not x>>j&1)]
pairs={(p,q) for p in positive for q in negative}
pairs|={(p,p^(1<<j)) for p in range(512) if labels[p] for j in range(9) if not labels[p^(1<<j)]}
pairs=sorted(pairs)
n=len(pairs); U=(1<<n)-1; top=(1<<(2*n))-1; pos=U<<n
def encode(v):
 return sum(((v>>q&1)|((v>>p&1)<<n))<<i for i,(p,q) in enumerate(pairs))
X=tuple(map(encode,raw)); A=encode(head)
def cuts(v):
 y,f=v>>n,v&U
 return y^f,y&(U^f)
@lru_cache(maxsize=35000)
def cover(live):
 d=m=0
 for w in live:
  a,b=cuts(w);d|=a;m|=b
 return d,m
def enumerate_case(ports,secs):
 z=encode(ortable(ports)); ins=X+(A,z)
 # A discarded head, including one used only by the other synthetic head,
 # requires care. Enumerate independently every eligible starting state.
 good=[]
 for st in states:
  if tuple(st['ports'])!=tuple(ports):continue
  for mask in range(1<<len(ins)):
   root=tuple(sorted(w for j,w in enumerate(ins) if mask>>j&1))
   if cover(root)[0]==U:good.append(root)
 limit=time.monotonic()+secs;path=[];count=0;found=None
 @lru_cache(maxsize=36000)
 def visit(k,ws):
  nonlocal count,found
  count+=1
  if count%128==0 and time.monotonic()>limit:raise TimeoutError
  if pos in ws:found=list(path);return True
  if k==0 or len(ws)>k+1:return False
  ds,ms=cover(ws)
  if ds!=U or (len(ws)==k+1 and ms!=U):return False
  have=set(ws)
  for a in ws:
   for b in ws:
    if a>b:continue
    unary=a==b
    ops=(('not',top^a),) if unary else (('and',a&b),('or',a|b))
    rest=have-{a,b}
    for op,v in ops:
     if v in (0,top) or v in have:continue
     for keep in (((),(a,)) if unary else ((),(a,),(b,),(a,b))):
      if len(rest)+1+len(keep)>k:continue
      nxt=tuple(sorted((*rest,*keep,v)))
      d,m=cover(nxt)
      if d!=U or (len(nxt)==k and m!=U):continue
      path.append((op,a,b,v))
      if visit(k-1,nxt):return True
      path.pop()
  return False
 try:result='witness_on_paired_rows' if any(visit(13,r) for r in sorted(good,key=len)) else 'excluded_on_paired_rows'
 except TimeoutError:result='unknown'
 if found:
  src=dict(zip(ins,(*raw,head,ortable(ports))))
  gates=[]
  for op,a,b,v in found:
   c,d=src[a],src[b];src[v]=(c&d if op=='and' else c|d if op=='or' else ((1<<512)-1)^c)
   gates.append((op,hex(c),hex(d)))
  if src[pos]==sum(int(v)<<i for i,v in enumerate(labels)):print('FULL 512-ROW WITNESS',gates,flush=True)
 print('ports',ports,'roots',len(good),'nodes',count,'result',result,flush=True)
 visit.cache_clear();cover.cache_clear()
if __name__=='__main__':
 print('rows',n,'positive edges',len(positive),'extreme negatives',len(negative),flush=True)
 for st in states:
  if not st['redundant']:enumerate_case(st['ports'],4)
