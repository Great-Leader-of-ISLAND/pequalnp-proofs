"""Certify raw leaf lower bounds for a bank with a given monotone truth column."""
from itertools import combinations
from collections import Counter
from pathlib import Path
import runpy
D=runpy.run_path(str(Path(__file__).with_name('3004-or-bank-rank.py')))
W=D['W']; edges=D['edges'];cols=D['cols'];adj=D['adj'];bits=D['bits'];matching=D['matching'];full=D['full']
n=14; total=len(edges)
incident=[sum(1<<j for j,e in enumerate(edges) if e>>v&1) for v in range(n)]
def supers(mask):return sum(1<<j for j,c in enumerate(cols) if c&mask==mask)
base=[supers(nei) for nei in adj]
pdata=[]
for j,e in enumerate(edges):
 a,b=bits(e);pdata.append((e,incident[a]|incident[b],supers((adj[a]|adj[b])^e)))
ent=[[(1<<j,supers(e^(1<<v))) for j,e in enumerate(edges) if e>>v&1] for v in range(n)]
def rank(z):
 pos=z&((1<<total)-1);neg=z>>total
 good=[e for e,p,m in pdata if not pos&p or neg&m]
 degree=[0]*n
 for e in good:
    for i in bits(e):degree[i]+=1
 essential=[any(not pos&p or neg&m for p,m in cells) for cells in ent]
 forced=sum(1<<v for v,d in enumerate(degree) if
    (d==0 and essential[v]) or (d<3 and (not pos&incident[v] or neg&base[v])))
 ordinary=len(good)+bin(forced).count('1')+matching(good,full^forced)
 exceptions=[e for i,e in enumerate(edges) if pos>>i&1]
 cutzero=28-len(exceptions)-matching(exceptions,full)
 return max(ordinary,cutzero)
if __name__=='__main__':
 for op in ['and-or','or-and']:
    stats=Counter(); misses=[]
    for a,b in combinations(range(n),2):
      for c in range(n):
       if c==a or c==b:continue
       z=((W[a]&W[b])|W[c]) if op=='and-or' else ((W[a]|W[b])&W[c])
       raw=rank(z);stats[raw]+=1
       if 2+2+raw-1 < 27:misses.append((a,b,c))
    print(op,sorted(stats.items()),'remaining',len(misses),misses[:12])
