"""Exact row obstructions for two six-vertex theta-deletion graphs."""
from itertools import combinations
from pathlib import Path
from functools import lru_cache
from theta1924front import F
import argparse

def prepare(gone):
    raw_ids=[j for j in range(7) if j!=gone]
    coords=[sum((r>>j&1)<<n for j,n in enumerate(raw_ids)) for r in range(64)]
    plus=[r for r,row in enumerate(coords) if F>>row&1]
    minus=[r for r,row in enumerate(coords) if not(F>>row&1)]
    cols=tuple(sum((r>>j&1)<<r for r in range(64)) for j in range(6))
    full=(1<<64)-1
    allpairs=(1<<(len(plus)*len(minus)))-1
    ranks=[0]*7
    for i,p in enumerate(plus):
        for j,q in enumerate(minus):ranks[(p^q).bit_count()]|=1<<(i*len(minus)+j)
    @lru_cache(None)
    def sep(x):
        return sum((((x>>p)^(x>>q))&1)<<(i*len(minus)+j) for i,p in enumerate(plus) for j,q in enumerate(minus))
    chosen=0
    @lru_cache(None)
    def go(k,ws):
        nonlocal chosen
        for a,b in combinations(ws,2):
            rest=tuple(w for w in ws if w not in (a,b))
            base=0
            for w in rest:base|=sep(w)
            for z in (a&b,a|b,a&(full^b),b&(full^a)):
                if not z or z in ws:continue
                for keep in ((),(a,),(b,),(a,b)):
                    if len(rest)+len(keep)+1>k:continue
                    cov=base|sep(z)
                    for w in keep:cov|=sep(w)
                    miss=allpairs^cov
                    if not miss:go(k-1,tuple(sorted((*rest,z,*keep))))
                    elif not chosen&miss:
                        v=next(miss&m for m in ranks if miss&m)
                        chosen|=v&-v
    go(7,tuple(sorted(cols)))
    pairs=[(p,q) for i,p in enumerate(plus) for j,q in enumerate(minus) if chosen>>(i*len(minus)+j)&1]
    for j in range(6):
        if not any(p^q==1<<j for p,q in pairs):
            pairs.append(next((p,q) for p in plus for q in minus if p^q==1<<j))
    if not any(q==0 for _,q in pairs):pairs.append((plus[0],0))
    width=411
    assert len(pairs)<width
    print('deleted',gone,'row pairs',len(pairs),'distinct states',go.cache_info().currsize)
    pairs+=([pairs[-1]]*(width-len(pairs)))
    words=[(sum(((p>>j)&1)<<i for i,(p,q) in enumerate(pairs)),sum(((q>>j)&1)<<i for i,(p,q) in enumerate(pairs))) for j in range(6)]
    return words,pairs

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--output',type=Path,required=True);args=a.parse_args()
    data=['namespace CoThetaSix','open CoThetaBits','open CoNatBench']
    for gone,name in [(2,'cycle'),(3,'pendant')]:
        ws,pairs=prepare(gone)
        data.append(f'def {name} : List CoThetaBits.Wire := ['+',\n'.join(f'({hex(x)},{hex(y)})' for x,y in ws)+']')
        data.append(f'theorem {name}_small : CoNatBench.guardedSearch 7 ({name}.map CoNatBench.project)=false := by decide +kernel')
        inds=[next(i for i,(p,q) in enumerate(pairs) if p^q==1<<j) for j in range(6)]
        data.append(f'def {name}Private : List Nat := '+str(inds))
    data.append('end CoThetaSix')
    args.output.write_text('\n'.join(data)+'\n')
