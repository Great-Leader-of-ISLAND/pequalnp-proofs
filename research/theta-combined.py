#!/usr/bin/env python3
"""Bounded exact search with ordinary-prefix and read-once cutoffs.
Completeness of the row transitions and of the two cutoffs is documented in
1940-two-not.md and theta-read-once.md. A Python result still needs kernel replay.
"""
import argparse,itertools,runpy,time
from pathlib import Path
w=Path(__file__).resolve().parent;step=runpy.run_path(str(w/'theta-layer-splits.py'));read=runpy.run_path(str(w/'theta-decomposition.py'))
X,U,F=step['X'],step['U'],step['F']

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seconds',type=float,default=60);p.add_argument('--max-states',type=int,default=90000);p.add_argument('--unoriented',action='store_true');a=p.parse_args();start=time.monotonic();D={v:frozenset() for v in X};current=set();atoms=set(X)
    for j in (0,2,3):
        root=(*X,U^X[j]);D[root[-1]]=frozenset({root[-1]})
        for n in range(1,9):
            for ws in itertools.combinations(root,n):
                for t in range(12-n):
                    if step['separates'](tuple(sorted(ws)),t):current.add((t,tuple(sorted(ws))))
    for d in range(11):
        if not current:break
        k=10-d;fresh=set();cheap=tight=expanded=0
        for t,ws in sorted(current):
            if time.monotonic()-start>a.seconds or len(fresh)>a.max_states:
                print('UNKNOWN bounded resource cutoff',d,len(current),len(fresh),flush=True);return
            if F in ws:print('UNEXPECTED target signal; extract and verify a concrete circuit before any claim',d,t,flush=True);return
            known=set().union(*(D[x] for x in ws))
            if len(known)<=d:cheap+=1;continue
            if len(ws)+t==k+1 and read['splits'](ws,t,True,a.unoriented) is None:tight+=1;continue
            expanded+=1
            for u,ww,(op,l,r,z) in step['children'](k,t,ws):
                fresh.add((u,ww));deps=D[l]|{z}
                if r is not None:deps=deps|D[r]
                # Each stored set is a set of gates of an acyclic single-output
                # program. Keep the first recipe so unions remain consistent.
                if z not in D:D[z]=deps
        print('level',d,'initial',len(current),'ordinary',cheap,'read-once',tight,'expanded',expanded,'next',len(fresh),flush=True)
        current=fresh
    if current:print('UNKNOWN residual after depth ten',len(current))
    else:print('EXHAUSTED on the combined frontier table; kernel replay separate',round(time.monotonic()-start,3),'seconds')
if __name__=='__main__':main()
