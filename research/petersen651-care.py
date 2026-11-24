"""Search optimal 13-gate circuits for P−{0,1} with two intermediate boundary signals.

The two intermediates need match x4∨x5 and x2∨x6 only on independent sets
of the residual: positive residual rows are already accepted. Each permitted
local move keeps the entire 256-row residual function. Full ten-input replay
is the only acceptance condition. Missing a witness gives no lower bound.
"""
import argparse,importlib.util,json,random,time
from itertools import combinations
from pathlib import Path
load=importlib.util.spec_from_file_location('shard',Path(__file__).with_name('petersen651-or-edge.py'));full=importlib.util.module_from_spec(load);load.loader.exec_module(full)
E=[(a-2,b-2) for a,b in full.EDGES if min(a,b)>=2]; MASK=(1<<256)-1
RAW=[sum(1<<r for r in range(256) if r&(1<<i)) for i in range(8)]
R=0
for a,b in E:R|=RAW[a]&RAW[b]
CARE=MASK^R;A=RAW[2]|RAW[3];B=RAW[0]|RAW[4]
COV=[v for v in combinations(range(8),4) if all(a in v or b in v for a,b in E)]
def value(op,a,b):return a&b if op=='and' else a|b if op=='or' else MASK^a
def evaluate(gs,force=None):
 vals=RAW.copy()
 for j,(op,a,b) in enumerate(gs):vals.append(force[1] if force and force[0]==8+j else value(op,vals[a],vals[b]))
 return vals
def initial(rng):
 cs=list(rng.choice(COV));rng.shuffle(cs);parts={v:[] for v in cs}
 for a,b in E:
  c=rng.choice([q for q in cs if q in (a,b)]);parts[c].append(b if a==c else a)
 gs=[]
 def gate(op,a,b):gs.append((op,a,b));return 7+len(gs)
 def join(vs):
  vs=list(vs)
  while len(vs)>1:
   rng.shuffle(vs);a,b=vs.pop(),vs.pop();vs.append(gate('or',a,b))
  return vs[0]
 out=join([gate('and',c,join(parts[c])) for c in cs]);assert out==20 and evaluate(gs)[-1]==R;return gs
def reschedule(gs,rng):
 pending={8+j:g for j,g in enumerate(gs)};mapping={i:i for i in range(8)};out=[]
 while pending:
  ready=[w for w,(op,a,b) in pending.items() if a in mapping and b in mapping];w=rng.choice(ready);op,a,b=pending.pop(w);mapping[w]=8+len(out);out.append((op,mapping[a],mapping[b]))
 assert mapping[20]==20;return out
def nearest(v,t):return min((((a^t)&CARE).bit_count(),i) for i,a in enumerate(v))
def score(v):return nearest(v,A)[0]+nearest(v,B)[0]
def full_circuit(gs,vals):
 _,a=nearest(vals,A);_,b=nearest(vals,B);out=[{'op':'or','inputs':[0,1]}];w=list(range(2,10))
 def gate(op,*pins):out.append(dict(op=op,inputs=list(pins)));return len(out)+9
 for op,i,j in gs:w.append(gate(op,w[i],w[j]) if op!='not' else gate(op,w[i]));
 left=gate('or',0,w[b]);right=gate('or',1,w[a]);xy=10;z=gate('and',xy,left);z=gate('and',z,right);z=gate('or',z,w[-1]);c=dict(gates=out,output=z);assert len(out)==19 and not full.counterexamples(c,19);return c
def moves(gs,rng):
 v=evaluate(gs);j=rng.randrange(len(gs));w=8+j;op,a,b=gs[j];cp=evaluate(gs,(w,0))[-1]^evaluate(gs,(w,MASK))[-1];assert cp
 avail=[(t,x,y,value(t,v[x],v[y])) for x,y in combinations(range(w),2) for t in ('or','and')];avail.extend(('not',x,x,MASK^v[x]) for x in range(w));rng.shuffle(avail)
 for t,x,y,n in avail:
  if n!=v[w] and not ((n^v[w])&cp):
   q=gs.copy();q[j]=t,x,y;yield q
 # Rewrite a two-gate cone at its root; the intermediate may change freely.
 single=[p for p in {a,b} if p>=8 and sum(p in (u,k) for _,u,k in gs)==1]
 if not single:return
 p=rng.choice(single);rng.shuffle(avail);ntrials=0
 for t,x,y,n in avail:
  if max(x,y)>=p or n==v[p]:continue
  ntrials+=1
  for k in range(w):
   if k==p:continue
   for t2,y2 in [('or',n|v[k]),('and',n&v[k])]:
    if not ((y2^v[w])&cp):
     q=gs.copy();q[p-8]=t,x,y;q[j]=t2,p,k;yield q
  if not (((MASK^n)^v[w])&cp):
   q=gs.copy();q[p-8]=t,x,y;q[j]='not',p,p;yield q
  if ntrials>=23:break
def main():
 p=argparse.ArgumentParser();p.add_argument('--seconds',type=int,default=190);p.add_argument('--seed',type=int,default=6511);a=p.parse_args();rng=random.Random(a.seed);end=time.monotonic()+a.seconds;best=100;seen=set();rounds=0;gs=initial(rng)
 while time.monotonic()<end:
  rounds+=1
  if rounds%80==0:gs=initial(rng)
  elif rng.random()<0.19:gs=reschedule(gs,rng)
  v=evaluate(gs);assert v[-1]==R;d=score(v)
  if d<best:best=d;print('best mismatch on independent rows',best,'round',rounds,flush=True)
  if d==0:print('WITNESS',json.dumps(full_circuit(gs,v)),flush=True);return
  candidates=[]
  for q in moves(gs,rng):
   u=evaluate(q);assert u[-1]==R;key=tuple(q)
   if key in seen:continue
   seen.add(key);candidates.append((score(u),rng.random(),q))
   if len(candidates)>=12:break
  if candidates:gs=min(candidates)[2] if rng.random()<.65 else rng.choice(candidates)[2]
  if len(seen)>65000:seen.clear()
 print('UNKNOWN heuristic',rounds,'rounds, best',best,flush=True)
if __name__=='__main__':main()
