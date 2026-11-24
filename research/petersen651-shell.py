"""Synthesize the 11-gate residual for a proposed 19-gate first-OR construction.

Two deleted adjacent vertices are 0,1. Allow the residual graph on 2..9
both free linear inputs A=x4 OR x5 and B=x2 OR x6. Any residual circuit
with <=11 gates gives <=19 for the original via the verified shell below.
A negative result in this template cannot exhaust the official shard.
"""
import argparse,importlib.util,json,time
from functools import reduce
from itertools import combinations
from pathlib import Path
import petersen670 as cnf
spec=importlib.util.spec_from_file_location('shard',Path(__file__).with_name('petersen651-or-edge.py'));full=importlib.util.module_from_spec(spec);spec.loader.exec_module(full)
N=8; E=[(a-2,b-2) for a,b in full.EDGES if a>=2 and b>=2]
def bit(r,i):return bool(r & (1<<i))
def target(r):return any(bit(r,a) and bit(r,b) for a,b in E)
def pack(r):return r | (int(bool(r&12))<<8) | (int(bool(r&17))<<9)
def gate(gs,op,*pins):gs.append(dict(op=op,inputs=list(pins)));return 9+len(gs)
def join(gs,pins):return reduce(lambda a,b:gate(gs,'or',a,b),pins)
def shell(res):
 gs=[];xy=gate(gs,'or',0,1);A=gate(gs,'or',4,5);B=gate(gs,'or',2,6);cols=list(range(2,10))+[A,B]; layer=len(res['gates'])
 for j,g in enumerate(res['gates']):
  # Every bad/forward index at this stage must still read false in the full circuit.
  pins=[cols[p] if p<len(cols) else 10+3+layer+12 for p in g['inputs']];cols.append(gate(gs,g['op'],*pins))
 o=res['output'];R=cols[o] if o<len(cols) else 10+3+layer+12
 xb=gate(gs,'or',0,B);ya=gate(gs,'or',1,A);m=gate(gs,'and',xy,xb);n=gate(gs,'and',m,ya);end=gate(gs,'or',R,n)
 return {'gates':gs,'output':end}
def audit(c):return full.counterexamples(c,len(c['gates']))
def base_control():
 centers=next(v for v in combinations(range(8),4) if all(a in v or b in v for a,b in E));parts={v:[] for v in centers}
 for a,b in E:
  c=next(x for x in centers if x in (a,b));parts[c].append(b if a==c else a)
 gs=[];o=join(gs,[gate(gs,'and',v,join(gs,ps)) for v,ps in parts.items()]);return dict(gates=gs,output=o)
def main():
 p=argparse.ArgumentParser();p.add_argument('--solver',required=True);p.add_argument('--seconds',type=int,default=150);p.add_argument('--directory',type=Path,required=True);p.add_argument('--mode',choices=('raw','normal'),default='normal');a=p.parse_args();a.directory.mkdir(exist_ok=False)
 c=shell(base_control());assert len(c['gates'])==21 and not audit(c);full.check_symmetry()
 # No pure star prep (or a wiring relabelled by any residual embedding) can
 # contain either desired OR: its two endpoints have no common residual neighbor.
 assert all(not any((min(u,v),max(u,v)) in {tuple(sorted(e)) for e in E} and (min(w,v),max(w,v)) in {tuple(sorted(e)) for e in E} for v in range(8)) for u,w in [(2,3),(0,4)])
 print('21-gate shell control passed all 1024 assignments; direct stars cannot supply either free pair',flush=True)
 cnf.N=10;cnf.target=target;enc=cnf.Encoding(a.mode,bound=11,symmetry=False);rows={0,255,*[1<<i for i in range(8)],*[(1<<a)|(1<<b) for a,b in E],*[r for r in range(256) if not target(r) and all(bit(r,i) or target(r|(1<<i)) for i in range(8))]}
 for r in sorted(rows):enc.add_row(pack(r))
 end=time.monotonic()+a.seconds
 for _ in range(256):
  f=a.directory/'shell.cnf';enc.dimacs(f);print('rows',len(enc.rows),'vars',enc.top,'clauses',len(enc.clauses),flush=True)
  rem=end-time.monotonic()
  if rem<=0:print('UNKNOWN');return
  v,model=cnf.run_cadical(a.solver,f,a.directory/'unused',rem,False)
  if v!='SAT':print('solver result under residual template',a.mode,v,flush=True);return
  c=shell(enc.decode(model));bad=audit(c)
  if not bad:
   assert len(c['gates'])<=19;print('WITNESS',json.dumps(c),flush=True);(a.directory/'witness.json').write_text(json.dumps(c));return
  new=sorted({r>>2 for r in bad if pack(r>>2) not in enc.rows});assert new
  for r in new[:8]:enc.add_row(pack(r))
if __name__=='__main__':main()
