"""All unlabeled six-point graphs, exact biclique numbers and bounded SAT for the partial AND model."""
from itertools import combinations,permutations
from functools import lru_cache
from pathlib import Path
import argparse,json,subprocess,tempfile
V=range(6); E=list(combinations(V,2)); ix={p:i for i,p in enumerate(E)}
doubles=[(1<<a)|(1<<b) for a,b in E]
def canon():
 seen=bytearray(1<<15)
 maps=[[1<<ix[tuple(sorted((p[a],p[b])))] for a,b in E] for p in permutations(V)]
 for g in range(1<<15):
  if seen[g]:continue
  edges=[i for i in range(15) if g>>i&1]
  for m in maps:seen[sum(m[i] for i in edges)]=1
  yield g
def covers(g):
 arcs=set()
 for a in range(1,64):
  common=0
  for v in V:
   if a>>v&1:continue
   if all(g>>ix[tuple(sorted((u,v)))]&1 for u in V if a>>u&1):common|=1<<v
  if common:
   arcs.add(sum(1<<i for i,(u,v) in enumerate(E) if ((a>>u)&(common>>v)&1) or ((a>>v)&(common>>u)&1)))
 maximal=[c for c in arcs if not any(c!=b and c&b==c for b in arcs)]
 @lru_cache(None)
 def bc(rem):
  if not rem:return 0
  least=rem&-rem
  return 1+min(bc(rem&~b) for b in maximal if b&least)
 return bc(g)
def care(g):
 es=[doubles[i] for i in range(15) if g>>i&1]
 good=lambda s:all(s&e!=e for e in es)
 neg=[s for s in range(64) if good(s) and all(not good(s|1<<v) for v in V if not s>>v&1)]
 pos=sorted({s|1<<v for s in neg for v in V if not s>>v&1})
 return neg,pos
class Formula:
 def __init__(self):self.n=0;self.cl=[]
 def var(self):self.n+=1;return self.n
 def any(self,terms):
  o=self.var();self.cl.append([-o,*terms]);self.cl.extend([o,-a] for a in terms);return o
 def both(self,a,b):
  o=self.var();self.cl.extend([[-o,a],[-o,b],[o,-a,-b]]);return o
def seek(g,k,solver,seconds,folder):
 neg,pos=care(g);f=Formula()
 sel=[[[f.var() for j in range(6+i)] for side in range(2)] for i in range(k)]
 out=[f.var() for i in range(k)]
 if k:f.cl.append([out[-1]])
 for r in neg+pos:
  nodes=[]
  for i,(a,b) in enumerate(sel):
   side=[]
   for c in (a,b):
    terms=[c[v] for v in V if r>>v&1]+[f.both(c[6+j],v) for j,v in enumerate(nodes)]
    side.append(f.any(terms))
   nodes.append(f.both(*side))
  if r in neg:f.cl.extend([-x,-y] for x,y in zip(out,nodes))
  else:f.cl.append([f.both(x,y) for x,y in zip(out,nodes)])
 path=folder/'input.cnf'
 path.write_text(f'p cnf {f.n} {len(f.cl)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in f.cl))
 try:r=subprocess.run([solver,'-q',str(path)],capture_output=True,text=True,timeout=seconds)
 except subprocess.TimeoutExpired:return 'UNKNOWN',None
 if r.returncode==20:return 'UNSAT',None
 if r.returncode!=10:raise RuntimeError((r.returncode,r.stdout[-220:],r.stderr[-220:]))
 yes={int(t) for line in r.stdout.splitlines() if line.startswith('v ') for t in line[2:].split() if int(t)>0}
 gates=[[[j for j,v in enumerate(c) if v in yes] for c in cell] for cell in sel];outs=[i for i,v in enumerate(out) if v in yes]
 def ev(r):
  vals=[bool(r>>i&1) for i in V]
  for a,b in gates:vals.append(any(vals[i] for i in a) and any(vals[i] for i in b))
  return any(vals[6+i] for i in outs)
 assert all(not ev(r) for r in neg) and all(ev(r) for r in pos)
 return 'SAT',dict(mask=g,edges=[pair for i,pair in enumerate(E) if g>>i&1],bc=covers(g),gates=gates,out=outs,negative=neg,positive=pos)
def main():
 p=argparse.ArgumentParser();p.add_argument('solver');p.add_argument('--seconds',type=float,default=3);a=p.parse_args()
 graphs=list(canon());assert len(graphs)==156
 with tempfile.TemporaryDirectory() as tmp:
  folder=Path(tmp)
  cyc=sum(1<<ix[e] for e in [(0,2),(0,3),(1,2),(1,3)])
  assert covers(cyc)==1 and seek(cyc,1,a.solver,10,folder)[0]=='SAT' and seek(cyc,0,a.solver,10,folder)[0]=='UNSAT'
  entries=sorted(((covers(g),g) for g in graphs),reverse=True);print('distribution',[(k,sum(x==k for x,_ in entries)) for k in sorted(set(x for x,_ in entries))],flush=True)
  for k,g in entries:
   if not k:continue
   res,w=seek(g,k-1,a.solver,a.seconds,folder)
   print('GRAPH',g,'bc',k,res,flush=True)
   if w:print('CERTIFIED WITNESS',json.dumps(w),flush=True);return
if __name__=='__main__':main()
