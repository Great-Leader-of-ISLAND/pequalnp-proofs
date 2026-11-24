"""Enumerate the posted second OR on all 512 inputs, and certify required live inputs."""
from itertools import product,combinations
from collections import Counter
from pathlib import Path
import json
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
labels=[any(s>>a & s>>b & 1 for a,b in edges) for s in range(512)]
raw=[sum(((s>>i)&1)<<s for s in range(512)) for i in range(9)]
head=raw[0]&raw[3]
available=raw+[head,0]
all_cases=[()] + [(i,) for i in range(11)] + list(product(range(11),repeat=2))
def ortable(ports):
 z=0
 for p in ports:z|=available[p]
 return z
def stat(ports):
 z=ortable(ports)
 needed=[]
 for i in range(9):
  for s in range(512):
   if s>>i&1:continue
   t=s^(1<<i)
   if labels[s]!=labels[t] and (head>>s^head>>t)&1==0 and (z>>s^z>>t)&1==0:
    needed.append((i,s,t));break
 return needed
outs={}
for c in all_cases:outs.setdefault(ortable(c),[]).append(c)
states=[]
for z,ports in outs.items():
 w=stat(ports[0]);states.append(dict(ports=ports[0],redundant=z in available,count=len(ports),forced=w))
def colliding(kept,z):
 seen={}
 mask=sum(1<<i for i in kept)
 for x in range(512):
  key=(x&mask,(head>>x)&1,(z>>x)&1)
  y=seen.setdefault(key,x)
  if labels[y]!=labels[x]:return (y,x)
 return None
for state in states:
 mandatory={a for a,_,_ in state['forced']}
 optional=sorted(set(range(9))-mandatory)
 allowed=[]
 failures=[]
 for k in range(len(optional)+1):
  for extras in combinations(optional,k):
   keep=sorted(mandatory|set(extras))
   pair=colliding(keep,ortable(state['ports']))
   if pair:failures.append((keep,pair))
   else:allowed.append(keep)
 state['minimal_kept']=[k for k in allowed if not any(set(l)<set(k) for l in allowed)]
 state['collision']=failures
p=Path(__file__).with_name('prefix1868.json')
p.write_text(json.dumps(states,separators=(',',':')))
print('port lists',len(all_cases),'different functions',len(outs),'distribution',sorted(Counter((s['redundant'],len(s['forced'])) for s in states).items()))
print('lists with represented second output',sum(s['count'] for s in states if s['redundant']))
print('every positive/negative pair displayed in',p.name)

for s in states:
 if not s['redundant'] and len(s['forced'])<9:print('exception',s['ports'],'minimal raw indices',s['minimal_kept'])
