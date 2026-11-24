"""Exact 13+13 incidence care rows, boundary of admissible extra minterms, 64-gate control."""
import json,itertools,collections
Q=13;V=range(Q);D=(0,1,3,9);ALL=(1<<13)-1
points=[sum(1<<((l+d)%Q) for d in D) for l in V]
lines=[sum(1<<l for l in V if points[l]>>p&1) for p in V]
def subset(x,y):return x&y==x
def disjoint_lines(s):return sum(1<<l for l in V if not points[l]&s)
def disjoint_points(t):return sum(1<<p for p in V if not lines[p]&t)
M=[];N=[]
for s in range(ALL+1):
 t=disjoint_lines(s)
 if disjoint_points(t)!=s:continue
 row=s|(t<<13);M.append(row)
 if not any(subset(s,a) for a in points) and not any(subset(t,b) for b in lines):N.append(row)
POS=[(1<<p)|(1<<(13+l)) for l in V for p in V if points[l]>>p&1]
def pic():
 support=[sum(1<<i for i,r in enumerate(N) if r>>j&1) for j in range(26)]
 every=(1<<len(N))-1; hist=collections.Counter(); bad=[]; total=0
 for s in range(ALL+1):
  avail=disjoint_lines(s);m=avail
  ps=every
  for p in V:
   if s>>p&1:ps&=support[p]
  while True:
   total+=1;T=s|(m<<13); c=ps
   for l in V:
    if m>>l&1:c&=support[13+l]
   if not c and all(any(subset(T^(1<<j),u) for u in N) for j in range(26) if T>>j&1):
    bad.append(T);hist[(s.bit_count(),m.bit_count())]+=1
   if not m:break
   m=(m-1)&avail
 print('care',len(POS),len(N),'maximal independent',len(M),'independent assignments',total,'minimal permissible extra signals',len(bad))
 print('free minterms by numbers of points and lines',sorted(hist.items()),flush=True)
 return bad
def eval_table(g):
 rows=POS+N;vs=[sum(1<<k for k,t in enumerate(rows) if t>>j&1) for j in range(26)]
 deg=[(int(j<13),int(j>=13)) for j in range(26)]
 for op,a,b in g:
  vs.append(vs[a]&vs[b] if op=='and' else vs[a]|vs[b])
  deg.append(tuple((x+y if op=='and' else max(x,y)) for x,y in zip(deg[a],deg[b])))
 return vs,deg
def stars(dual=False):
 gates=[];out=[]
 def add(o,a,b):gates.append((o,a,b));return 25+len(gates)
 for i,ne in enumerate(lines if dual else points):
  ns=[j+(13 if dual else 0) for j in V if ne>>j&1];z=ns[0]
  for u in ns[1:]:z=add('or',z,u)
  out.append(add('and',z,i+(0 if dual else 13)))
 z=out[0]
 for u in out[1:]:z=add('or',z,u)
 return gates,z
def control():
 for dual in [False,True]:
  gates,out=stars(dual);truth,deg=eval_table(gates)
  assert len(gates)==64 and truth[out]==(1<<len(POS))-1 and deg[out]==(1,1)
  hits=0
  for i,(_,a,b) in enumerate(gates):
   for alias in (a,b):
    def port(p):return alias if p==26+i else p-int(p>26+i)
    small=[(o,port(u),port(v)) for j,(o,u,v) in enumerate(gates) if j!=i]
    x,d=eval_table(small);hits+=sum(v==(1<<len(POS))-1 and min(di)>1 for v,di in zip(x,d))
  print('64-gate control',dual,'degree',deg[out],'63-gate single bypass witnesses',hits)
if __name__=='__main__':pic();control()
