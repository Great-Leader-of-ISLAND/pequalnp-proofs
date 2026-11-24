#!/usr/bin/env python3
"""Generate an untrusted, complete-or-explicitly-incomplete theta proof table.
Integers in state lists index an acyclic recipe dictionary. A cheap node stores
ordinary program recipe IDs, a merge node two ≤4-corner restrictions, a tree
node truthful positive/negative row IDs, and a step node points into the next level.
"""
import argparse,itertools,json,re,runpy,time
from pathlib import Path
w=Path(__file__).resolve().parent;step=runpy.run_path(str(w/'theta-layer-splits.py'));tree=runpy.run_path(str(w/'theta-decomposition.py'));fixed=runpy.run_path(str(w/'theta-fixed-merge.py'));G=step['G'];X,U,F=G['X'],G['U'],G['F']

def reduce_rows(ws,t):
    chosen=list(range(128)); pmap={r:1<<(i*len(G['NEG'])) for i,r in enumerate(G['POS'])};nmap={r:1<<i for i,r in enumerate(G['NEG'])}
    for block in (64,32,16,8,4,2,1):
        for start in range(0,128,block):
            cand=[r for r in chosen if not start<=r<start+block]
            if len(cand)==len(chosen):continue
            pair=(sum(pmap.get(r,0) for r in cand),sum(nmap.get(r,0) for r in cand))
            if tree['splits'](ws,t,True,True,custom_rows=pair) is None:chosen=cand
    return chosen

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);p.add_argument('--seconds',type=float,default=90);p.add_argument('--max-states',type=int,default=120000);p.add_argument('--signatures',type=Path,help='Use exactly the 256 pairs declared in this Lean source.');a=p.parse_args();until=time.monotonic()+a.seconds
    if a.signatures:
        basis=[tuple(int(v,16) for v in p) for p in re.findall(r'def x[0-6] : Sig := \((0x[0-9a-f]+),(0x[0-9a-f]+)\)',a.signatures.read_text())]
        assert len(basis)==7
        pairs={(sum((v[0]>>i&1)<<j for j,v in enumerate(basis)),sum((v[1]>>i&1)<<j for j,v in enumerate(basis))) for i in range(256)}
        assert len(pairs)==256
        required=sum(1<<(G['POS'].index(u)*len(G['NEG'])+G['NEG'].index(v)) for u,v in pairs)
        step['separates'].__wrapped__.__globals__['REQUIRED']=required
        print('fixed exact 256 Lean diagnostic pairs',flush=True)
    values=list(X);ids={v:i for i,v in enumerate(X)};deps=[frozenset() for _ in X];recipes=[('atom',i,None) for i in range(7)];current=set()
    def record(z,op,x,y):
        if z in ids:return
        i=len(values);values.append(z);ids[z]=i;u=ids[x];v=None if y is None else ids[y];recipes.append((op,u,v));scope=deps[u]|{i}
        if v is not None:scope|=deps[v]
        deps.append(scope)
    for j in (0,2,3):
        root=(*X,U^X[j]);record(root[-1],'not',X[j],None)
        for n in range(1,9):
            for ws in itertools.combinations(root,n):
                for t in range(12-n):
                    sig=tuple(sorted(ws))
                    if step['separates'](sig,t):current.add((t,sig))
    levels=[];complete=True
    for d in range(11):
        if not current:break
        k=10-d;nodes=[];fresh=set();tags={}
        for t,ws in sorted(current):
            if time.monotonic()>until or len(fresh)>a.max_states:complete=False;break
            if F in ws:raise RuntimeError('target present; model reconstruction and all-row validation required')
            indexes=[ids[z] for z in ws];ordinary=set().union(*(deps[i] for i in indexes))
            if len(ordinary)<=d:tag='ordinary';cert=sorted(ordinary)
            else:
                witness=fixed['find_merge'](ws) if len(ws)+t==k+1 else None
                if witness is not None:
                    fixed['verify'](ws,witness);u,v,g,h=witness;tag='merge';cert=[indexes[u],indexes[v],g,h]
                elif len(ws)+t==k+1 and tree['splits'](ws,t,True,True) is None:
                    tag='tree';cert=reduce_rows(ws,t)
                else:
                    tag='step';cert=[]
                    for t2,w2,(op,x,y,z) in step['children'](k,t,ws):record(z,op,x,y);fresh.add((t2,w2))
            nodes.append((t,sorted(indexes),tag,cert));tags[tag]=tags.get(tag,0)+1
        if not complete:break
        levels.append(nodes);print('level',d,'nodes',len(nodes),'classification',tags,'next',len(fresh),flush=True);current=fresh
    if current:complete=False
    payload=dict(complete=complete,recipes=recipes,levels=levels,signs=[0,2,3]);a.output.write_text(json.dumps(payload,separators=(',',':'))+'\n');print('certificate-data',complete,'gates',len(recipes),'bytes',a.output.stat().st_size,flush=True)
if __name__=='__main__':main()
