"""Generate compiled literal state packs for empirical fixed-first kernel tests."""
from itertools import combinations
from pathlib import Path
import argparse
from theta1924sample8 import children
from theta1924front import X,ALL
from theta1924small import emit
p=argparse.ArgumentParser();p.add_argument('--first',type=int,required=True);p.add_argument('--mask',required=True);p.add_argument('--base',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--chunk',type=int,default=6)
a=p.parse_args()
_,packed=emit(a.base,int(a.mask,0))
pa,pb=list(combinations(range(7),2))[a.first//4]
x,y=X[pa],X[pb];z=(x&y,x|y,x&(ALL^y),y&(ALL^x))[a.first%4]
states=sorted(set(children(9,tuple(sorted((*X,z))))))
signals=sorted({w for s in states for w in s});idx={w:i for i,w in enumerate(signals)}
text=['import Bench','open CoNatBench','set_option maxHeartbeats 0','set_option maxRecDepth 4000']
text.extend(f'def w{i} : Word := {packed(w)}' for i,w in enumerate(signals))
for i,s in enumerate(states):text.append(f'def s{i} : List Word := ['+','.join(f'w{idx[w]}' for w in s)+']')
for j in range(0,len(states),a.chunk):
    checks=' && '.join(f'!guardedSearch 8 s{i}' for i in range(j,min(j+a.chunk,len(states))))
    text.append(f'theorem check{j} : ({checks})=true := by decide +kernel')
print('first',a.first,'states',len(states),'signals',len(signals),flush=True)
a.output.write_text('\n'.join(text)+'\n')
