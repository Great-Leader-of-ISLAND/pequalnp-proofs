#!/usr/bin/env python3
"""Bounded breadth-first live-frontier layers for a Lean cut certificate.
The output is auxiliary data. Lean must recheck every child and every leaf.
Uses all P×N pairs; no extra one-inverter cut requiring an unproved lemma.
"""
import argparse, functools, itertools, json, runpy, time
from pathlib import Path
G=runpy.run_path(str(Path(__file__).with_name('theta-first-not.py')))
F,X,U,CUT,PAIR=(G[k] for k in ('F','X','U','cuts','PAIR'))
REQUIRED=PAIR

@functools.lru_cache(maxsize=120000)
def separates(ws,t):
    cov=0
    for w in ws:
        a,b=CUT(w)
        cov|=a if not t else a|b
    return cov & REQUIRED == REQUIRED

def children(k,t,ws):
    if not k or len(ws)+t>k+1: return
    def moves(op,a,b,z,nt):
        if z in ws or z in (0,U): return
        avail=set(ws)-{a,b};avail.add(z)
        for add in ((),(a,)) if b is None else ((),(a,),(b,),(a,b)):
            if len(avail)+len(add)+nt>k: continue
            child=tuple(sorted((*avail,*add)))
            if separates(child,nt):yield nt,child,(op,a,b,z)
    if t:
        for a in ws: yield from moves('not',a,None,U^a,t-1)
    if k>t:
        for a,b in itertools.combinations(ws,2):
            yield from moves('and',a,b,a&b,t);yield from moves('or',a,b,a|b,t)

def main():
    global REQUIRED
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--depth',type=int,choices=range(1,7),default=2)
    p.add_argument('--seconds',type=float,default=5);p.add_argument('--max-states',type=int,default=10000)
    p.add_argument('--compact',action='store_true');p.add_argument('--head',choices=('0','2','3','all'),required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    if a.compact:
        sample=runpy.run_path(str(Path(__file__).with_name('compact-theta-pairs.py')))['pairs']
        ps,ns=G['POS'],G['NEG'];REQUIRED=sum(1<<(ps.index(p)*len(ns)+ns.index(n)) for p,n in sample)
    until=time.monotonic()+a.seconds;recipes={z:('atom',i,None) for i,z in enumerate(X)}
    current=set()
    for j in (0,2,3) if a.head=='all' else (int(a.head),):
        root=(*X,U^X[j]);recipes[root[-1]]=('not',X[j],None)
        for n in range(1,9):
            for x in itertools.combinations(root,n):
                for t in range(12-n):
                    if separates(tuple(sorted(x)),t): current.add((t,tuple(sorted(x))))
    levels=[current];complete=True
    for d in range(a.depth):
        subs=set()
        for t,ws in sorted(current):
            if time.monotonic()>until or len(subs)>=a.max_states:complete=False;break
            for nt,child,(op,u,v,z) in children(10-d,t,ws):
                subs.add((nt,child));recipes.setdefault(z,(op,u,v))
        if not complete:break
        levels.append(subs);current=subs
    masks=list(recipes);ids={s:i for i,s in enumerate(masks)}
    rec=[]
    for s in masks:
        op,u,v=recipes[s];rec.append([op,u if op=='atom' else ids[u],None if v is None else ids[v]])
    a.output.write_text(json.dumps(dict(head=a.head,compact=a.compact,more_requested=not complete,recipes=rec,levels=[[[t,sorted(ids[z] for z in ws)] for t,ws in sorted(lev)] for lev in levels]),separators=(',',':'))+'\n')
    print('complete stored layers',len(levels)-1,'states',[len(lev) for lev in levels], 'distinct signals',len(masks),'full requested depth',complete)
if __name__=='__main__':main()
