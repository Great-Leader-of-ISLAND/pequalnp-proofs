"""Exclude a whole interval of single-bank truth columns using forced KW cells."""
from collections import Counter
from pathlib import Path
import argparse,runpy,time
D=runpy.run_path(str(Path(__file__).with_name('3004-bank-sandwich.py')))
E,N,P,NC,L,O=D['E'],D['N'],D['P'],D['NC'],D['L'],D['O']
pressure=runpy.run_path(str(Path(__file__).with_name('3004-suffix-rectangles.py')))['marks_possible']
negative_orbits=runpy.run_path(str(Path(__file__).with_name('3004-negative-orbits.py')))['possible']
A=D['D'];bits=L['bits'];size=L['size']

def run(k,limit):
    start=time.monotonic();stats=Counter();open_cases=[];complete=True
    def walk(fixed_p,free_p,fixed_n,free_n):
        nonlocal complete
        if not complete:return
        stats['visited']+=1
        if stats['visited']%256==0 and time.monotonic()-start>limit:
            complete=False;return
        best_p=fixed_p|free_p
        if best_p==0 or fixed_p==P or fixed_n|free_n==0:return
        # Here fixed_n is the negative rows on which z must be true.
        helpful=best_p|(fixed_n<<len(E))
        if A['can_replace'](helpful,k):
            stats['replacement']+=1;return
        if not pressure(best_p,fixed_n,r,25-k):
            stats['forced rectangles']+=1;return
        if A['rank'](helpful)>25-k:
            stats['suffix rank']+=1;return
        if L['bank_leaves']([E[j] for j in bits(fixed_p)],NC^(fixed_n|free_n))>k+1:
            stats['bank rank']+=1;return
        if not (free_p|free_n):
            stats['remaining']+=1
            if len(open_cases)<4:open_cases.append((fixed_p,fixed_n))
            return
        # Interleave refinement so both independent bounds grow early.
        if free_p and (not free_n or size(free_p)>size(free_n)):
            bit=free_p&-free_p
            walk(fixed_p|bit,free_p^bit,fixed_n,free_n)
            walk(fixed_p,free_p^bit,fixed_n,free_n)
        else:
            bit=free_n&-free_n
            walk(fixed_p,free_p,fixed_n|bit,free_n^bit)
            walk(fixed_p,free_p,fixed_n,free_n^bit)
    for r,m,ei,ni in O['masks']():
        if size(r)>25-k:continue
        em=sum(1<<j for j in ei);nm=sum(1<<j for j in ni)
        if k<=11:
            for bad in negative_orbits(r,nm,25-k):
                walk(P^em,em,bad,0)
                if not complete:break
        else:
            walk(P^em,em,0,nm)
        if not complete:break
    print('BANK_INTERVAL',k,'COMPLETE' if complete else 'INCOMPLETE',dict(stats),'first',open_cases,'elapsed',round(time.monotonic()-start,2),flush=True)
    return stats,complete
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('k',type=int,nargs='+');p.add_argument('--limit',type=int,default=50);a=p.parse_args()
    for k in a.k:run(k,a.limit)
