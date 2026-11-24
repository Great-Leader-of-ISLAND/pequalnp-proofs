"""Enumerate live-wire states after an actually fixed first gate on the nine-input graph.

Each call is a finite single bucket, with exactly t inversions after the first.
False/pruned for one bucket is never a verdict about other choices. A witness
must satisfy all 512 rows in the independent scalar interpreter.
"""
import argparse,time,json
from functools import lru_cache
from petersen670_frontier import Search, Bounded
from petersen670 import N,counterexamples

def main():
 p=argparse.ArgumentParser();p.add_argument('--gap',choices=('1665','1667'),required=True);p.add_argument('--mode',choices=('dead','live','negative-only'),required=True);p.add_argument('--not-count',type=int,required=True);p.add_argument('--seconds',type=int,default=45);p.add_argument('--nodes',type=int,default=750000);a=p.parse_args()
 s=Search('boundary');v=s.inputs; invert=a.gap=='1665'
 if a.mode=='negative-only' and not invert:p.error('negative-only applies only to an inverter')
 prefix=v[0]^s.mask if invert else v[0]&v[1]
 head={'op':'not','inputs':[0]} if invert else {'op':'and','inputs':[0,1]}
 # Each non-first input is essential independently of the prefix. For AND,
 # x0 and x1 remain essential when the other is zero (use 4 or 2). For NOT
 # the raw x0 need not be read again if its complement is the sole carrier.
 pool=(list(v) if a.mode=='dead' else list(v)+[prefix] if a.mode=='live' else list(v[1:])+[prefix]); root=tuple(sorted(pool));start=time.monotonic();states=0; path=[]; witness=None
 def replay():
  wire={value:i for i,value in enumerate(v)};wire[prefix]=N;gs=[head]
  for op,pins,z in path:
   gs.append({'op':op,'inputs':[wire[x] for x in pins]});wire[z]=N+len(gs)-1
  c={'gates':gs,'output':wire[s.goal]};assert len(gs)<=15 and not counterexamples(c,15);return c
 @lru_cache(maxsize=16000)
 def visit(pool,k,t):
  nonlocal states,witness
  states+=1
  if states>a.nodes or time.monotonic()>start+a.seconds:raise Bounded
  if s.goal in pool and t==0:
   witness=replay();return True
  if not s.viable(pool,k,t):return False
  for nxt,nt,_,gate in s.next(pool,k,t,()):
   path.append(gate)
   if visit(nxt,k-1,nt):return True
   path.pop()
  return False
 print(a.gap,a.mode,'suffix NOT count',a.not_count,'root inputs',len(root),flush=True)
 try:
  status='WITNESS' if visit(root,14,a.not_count) else 'EXCLUDED in this bucket'
 except Bounded: status='UNKNOWN: budget'
 print(status,'states',states,'seconds',round(time.monotonic()-start,3),flush=True)
 if witness is not None:print(json.dumps(witness),flush=True)

if __name__=='__main__':main()
