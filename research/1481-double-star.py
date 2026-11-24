"""Double-alarm matching control on PG(2,3) within one gate of the live bound."""
from pathlib import Path
from functools import reduce
P=range(13); hood=[tuple(t for t in P if (p-t)%13 in (0,1,3,9)) for p in P]
def network(omit=2):
 gs=[]
 def gate(k,a,b):
  assert a!=b and max(a,b)<26+len(gs)
  z=26+len(gs);gs.append((k,a,b));return z
 def disj(wires):return reduce(lambda a,b:gate(1,a,b),wires)
 a=disj([gate(0,p,disj([13+t for t in hood[p]])) for p in P if p!=omit])
 b=disj([13+t for t in hood[omit]])
 return gs,gate(0,gate(1,a,omit),gate(1,a,b))
def columns(rows):
 return [sum(((r>>i)&1)<<j for j,r in enumerate(rows)) for i in range(26)]
def evaluate(gs,cols):
 w=cols[:]
 for op,a,b in gs:w.append(w[a]|w[b] if op else w[a]&w[b])
 return w
def blame(gs,base,marked):
 x=[int(i==base) for i in range(26)];d=[int(i==marked) for i in range(26)]
 for op,a,b in gs:
  d.append(d[a]|d[b] if op else (x[a]&d[b])|(d[a]&x[b]))
  x.append(x[a]|x[b] if op else x[a]&x[b])
 return d
def tests():
 edges=[1<<p|1<<(13+t) for p in P for t in hood[p]]
 # For every point set, turn on every line avoiding it. Each negative lies below one of these.
 bars=[sum(1<<t for t in hood[p]) for p in P]
 free=[8191]*8192
 for x in range(1,8192):
  low=x&-x;free[x]=free[x^low]&~bars[low.bit_length()-1]
 # Keep maximal negatives: close the point side and deduplicate.
 negs={sum((not (row&F))<<p for p,row in enumerate(bars))|F<<13 for F in free}
 assert all(not any(z&e==e for e in edges) for z in negs)
 return edges,sorted(negs)
if __name__=='__main__':
 E,N=tests();g,z=network();w=evaluate(g,columns(E+N))
 assert w[z]==(1<<len(E))-1
 double=[(p,t) for p in P for t in hood[p] if not blame(g,p,13+t)[z] and not blame(g,13+t,p)[z]]
 assert (0,0) in double
 print('strict gates',len(g),'output',z,'positive rows',len(E),'all maximal negatives',len(N),'double incidences',len(double),'example',(0,0))
