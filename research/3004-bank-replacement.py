"""Inductively reduce unresolved shared banks to already excluded lower-cost banks."""
from pathlib import Path
import argparse,runpy,time
from collections import Counter
D=runpy.run_path(str(Path(__file__).with_name('3004-bank-enumerate.py')))
W=D['W']; n=len(D['edges']); mask=(1<<n)-1
def subbank(z,k,ls):
    for c in range(1,k):
        budget=k-c
        for v in ls[c]:
            if (v&~z)>>n:continue
            bad=z&~v&mask
            if bin(bad).count('1')<=budget and D['repair'](bad)<=budget:return c
    return None
def pureor(k,ls):
    from itertools import combinations
    return {__import__('functools').reduce(int.__or__,a) for a in combinations(W,k+1)}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('maxcost',type=int);args=p.parse_args()
    ls=D['layers'](args.maxcost)
    for k in range(1,args.maxcost+1):
        counts=Counter();left=[];pure=pureor(k,ls)
        for z in sorted(ls[k]):
            if D['can_replace'](z,k):counts['literal']+=1
            elif k+D['rank'](z)+1>=27:counts['rank']+=1
            elif z in pure:counts['pure OR']+=1
            else:
                c=subbank(z,k,ls)
                if c is not None:counts['cheaper bank '+str(c)]+=1
                else:left.append(z)
        print(k,len(ls[k]),dict(counts),'remaining',len(left),left[:5],flush=True)
        if left:break
