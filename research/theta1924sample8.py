"""Prepare reproducible random depth-eight kernel workloads."""
import argparse
import random
from pathlib import Path
from itertools import combinations
from theta1924front import X,F,ALL,ALLPAIRS
from theta1924free import separated
from theta1924small import emit

def children(k,ws):
    for a,b in combinations(ws,2):
        rem=tuple(w for w in ws if w not in (a,b))
        base=0
        for w in rem:base|=separated(w)
        for z in (a&b,a|b,a&(ALL^b),b&(ALL^a)):
            if not z or z in ws:continue
            for keep in ((),(a,),(b,),(a,b)):
                if len(rem)+len(keep)+1>k:continue
                cov=base|separated(z)
                for w in keep:cov|=separated(w)
                if cov==ALLPAIRS:yield tuple(sorted((*rem,z,*keep)))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--mask',required=True);p.add_argument('--base',required=True,type=Path);p.add_argument('--output',required=True,type=Path)
    a=p.parse_args();base,packed=emit(a.base,int(a.mask,0))
    root=tuple(sorted(X))
    layer={c for s in children(10,root) for c in children(9,s)}
    sample=random.Random(1924).sample(sorted(layer),20)
    print('layer',len(layer),'signals',len({w for s in layer for w in s}),flush=True)
    lines=['namespace CoThetaBits']
    for i,ws in enumerate(sample):lines.append(f'def random{i} : List Wire := ['+',\n'.join(packed(z) for z in ws)+']')
    a.output.write_text(base+'\n'.join(lines)+'\nend CoThetaBits\n')
