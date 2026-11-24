"""Two monotone CNF gadgets with non-star edge sets, then any ordinary stars.

Scalar truth signature determines soundness on the full cube. Pair and triple
OR preparations, as well as conjunctions of common clauses, cost once.
"""
from importlib.util import spec_from_file_location,module_from_spec
from itertools import combinations,product
from pathlib import Path
spec=spec_from_file_location('guards',Path(__file__).with_name('petersen651-guarded-stars.py'));g=module_from_spec(spec);spec.loader.exec_module(g)

def make():
    lib=[]
    for n in (2,3,4):
        pool=[s for s in g.MASK if n<4 or g.bits(s)<=2]
        for cs in combinations(pool,n):
            pos=g.HITEDGE[cs[0]]; neg=g.HITIND[cs[0]]
            for s in cs[1:]: pos&=g.HITEDGE[s]; neg&=g.HITIND[s]
            if not pos or neg: continue
            if any(pos&~m==0 for _,_,m in g.STARS):continue
            if any(a&b in (a,b) for a,b in combinations(cs,2)):continue
            fs=frozenset(s for s in cs if g.bits(s)>1)
            ps={fs.union(split) for split in product(*(g.PAIRS[s] for s in cs if g.bits(s)==3))}
            lib.append((frozenset(cs),pos,ps))
    return lib

def run():
    lib=make(); gs=[e for e in lib if any(3 in f for f in e[2])]
    best=21; result=None; passed=0; tested=0
    for cs,p,ps in gs:
        for ds,q,qs in lib:
            if p&~q==0 or q&~p==0: continue
            r=g.FULL&~(p|q)
            andcost=len(cs)+len(ds)-2-max(0,len(cs&ds)-1)
            for u in ps:
                if 3 not in u:continue
                for v in qs:
                    free=u|v
                    # The two gadget outputs require one OR.
                    base=len(free)+andcost+1; tested+=1
                    rel=frozenset(free&g.REL)
                    if base+g.bits(r)+g.tau(r)-g.rebates(rel)>=best:continue
                    passed+=1; c,stars=g.complete(r,rel)
                    if base+c<best:
                        best=base+c;result=(sorted(cs),sorted(ds),sorted(free),stars)
    print('non-star gadgets',len(lib),'eligible first gadgets',len(gs),'preparation pairs',tested,'exact completions',passed)
    print('best improvement on 21',None if result is None else (best,result))
if __name__=='__main__': run()
