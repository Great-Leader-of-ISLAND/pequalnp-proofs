"""Bound the possible truth columns of a single shared monotone-subformula output."""
from collections import Counter
from functools import lru_cache
from pathlib import Path
import argparse,runpy,time
D=runpy.run_path(str(Path(__file__).with_name('3004-mixed-bank-rank.py')))
W=D['W'];edges=D['edges'];total=len(edges);full=D['full'];matching=D['matching'];rank=D['rank']
posmask=(1<<total)-1
@lru_cache(maxsize=65536)
def repair(p):
    if not p:return 0
    es=[e for i,e in enumerate(edges) if p>>i&1]
    return len(es)+matching(es,full)
def can_replace(z,k):
    for v in [0,*W]:
        if (v&~z)>>total:continue
        bad=z&~v&posmask
        if bin(bad).count('1')<=k and repair(bad)<=k:return True
    return False
def layers(kmax):
    known=set(W)
    layers=[set(known)]
    for k in range(1,kmax+1):
        out=set()
        for i in range((k-1)//2+1):
            j=k-1-i
            for a in layers[i]:
                for b in layers[j]:
                    if i!=j or a<b:out.update((a&b,a|b))
        out.difference_update(known);known.update(out);layers.append(out)
    return layers
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('max_cost',type=int,choices=[1,2,3,4,5])
    args=parser.parse_args();start=time.monotonic()
    L=layers(args.max_cost)
    for k in range(1,len(L)):
        counts=Counter();remain=[]
        for z in sorted(L[k]):
            if can_replace(z,k):counts['literal repair']+=1;continue
            rw=rank(z)
            if k+rw+2-1>=27:counts['raw rank at two uses']+=1;continue
            remain.append((z,rw));counts['remaining']+=1
        print('gates',k,'minimal columns',len(L[k]),dict(counts),'examples',remain[:12], 'elapsed',round(time.monotonic()-start,3),flush=True)
