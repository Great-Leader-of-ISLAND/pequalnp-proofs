"""Compare raw-leaf lower bounds for the bank and suffix on complementary parts of the KW game."""
from pathlib import Path
import runpy,sys
from collections import Counter
w=Path(__file__).resolve().parent
O=runpy.run_path(str(w/'3004-bank-orbits.py'));D=runpy.run_path(str(w/'3004-bank-enumerate.py'));L=O['D']
E,N,F,size=O['E'],O['N'],O['F'],O['size']
P=(1<<len(E))-1;NC=(1<<len(N))-1
def subs(mask):
 s=mask
 while s:yield s;s=(s-1)&mask
def classify(k):
 count=Counter();ex=[]
 for R,m,ei,ni in O['masks']():
    if size(R)>25-k:continue
    em=sum(1<<j for j in ei);nm=sum(1<<j for j in ni)
    if L['bank_leaves']([e for j,e in enumerate(E) if not em>>j&1],NC^nm)>k+1:continue
    for miss in subs(em):
      es=[e for j,e in enumerate(E) if not miss>>j&1]
      if L['bank_leaves'](es,NC^nm)>k+1:
        count['forced bank rank']+=(1<<size(nm))-1
        continue
      for bad in subs(nm):
        z=(P^miss)|(bad<<len(E))
        if D['can_replace'](z,k):count['literal']+=1
        elif D['rank'](z)>25-k:count['suffix rank']+=1
        elif L['bank_leaves'](es,NC^bad)>k+1:count['bank rank']+=1
        else:ex.append((R,miss,bad,z));count['open']+=1
 print('cost',k,dict(count),'sample',ex[:4],flush=True)
 return ex
if __name__=='__main__':
 for k in map(int,sys.argv[1:]):classify(k)
