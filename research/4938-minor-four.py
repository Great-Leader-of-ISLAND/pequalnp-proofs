"""Check four-coordinate restrictions, allowing multiply-read leaves either sign."""
from itertools import combinations,product
from functools import lru_cache
from collections import Counter
from pathlib import Path
import runpy,time
d=runpy.run_path(str(Path(__file__).with_name('4938-formula-minors.py')))
E,labels=d['edges'],d['labels']
N=[{j for j in range(10) if (i,j) in E or (j,i) in E} for i in range(10)]
def demands(block):
 outside=[i for i in range(10) if i not in block]
 shift=lambda t,vs:sum((t>>j&1)<<v for j,v in enumerate(vs))
 S=[shift(i,block) for i in range(16)]
 return frozenset(sum(labels[r|q]<<i for i,q in enumerate(S)) for r in (shift(t,outside) for t in range(64)))
@lru_cache(None)
def trees(mult,pol):
 if sum(mult)==1:
  i=mult.index(1);v=sum((bool(r&(1<<i)))<<r for r in range(16))
  return (frozenset([0,65535,v,65535^v] if pol>>i&1 else [0,65535,v]),)
 ans=set()
 for a in product(*(range(m+1) for m in mult)):
  b=tuple(x-y for x,y in zip(mult,a))
  if not any(a) or not any(b) or a>b:continue
  for l in trees(a,pol):
   for r in trees(b,pol):
    base=l|r
    ans.add(base|frozenset(x&y for x in l for y in r))
    ans.add(base|frozenset(x|y for x in l for y in r))
 # Keeping all families avoids expensive quadratic dominance tests.
 return tuple(ans)
@lru_cache(None)
def admitted(mult,f):
 pol=sum((x>1)<<i for i,x in enumerate(mult))
 return any(f<=t for t in trees(mult,pol))
def canonical(mult,rows):
 order=tuple(sorted(range(4),key=lambda i:(mult[i],i)))
 if order==(0,1,2,3):return mult,rows
 remap=[sum(((r>>k)&1)<<i for k,i in enumerate(order)) for r in range(16)]
 return tuple(mult[i] for i in order),frozenset(sum(((v>>a)&1)<<j for j,a in enumerate(remap)) for v in rows)
def profiles():
 a=set()
 for q in range(1024):
  zeros={i for i in range(10) if q>>i&1}
  if any(i in zeros and j in zeros for i,j in E):continue
  m=tuple(1 if i in zeros else 2+(len(N[i]&zeros)>=2) for i in range(10))
  if sum(m)<=19:a.add(m)
  if sum(m)<19:
   for i in range(10):a.add(tuple(v+int(i==j) for j,v in enumerate(m)))
 return a
if __name__=='__main__':
 import sys
 cap=int(sys.argv[1]) if len(sys.argv)>1 else 5
 todo=profiles();F={b:demands(b) for b in combinations(range(10),4)}
 print('initial',Counter(map(sum,todo)),flush=True)
 for budget in range(4,cap+1):
  keep=set()
  for P in todo:
   for block,rows in F.items():
    mult=tuple(P[i] for i in block)
    if sum(mult)==budget and not admitted(*canonical(mult,rows)):break
   else:keep.add(P)
  todo=keep;print('through',budget,Counter(map(sum,todo)),admitted.cache_info(),flush=True)
 print('examples',sorted(todo)[:2])
