"""Universal three-variable restrictions of a signed formula on the Petersen graph."""
from functools import lru_cache
from itertools import combinations
from collections import Counter

edges=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(5+i,5+(i+2)%5) for i in range(5)]
edge_masks=tuple(1<<a|1<<b for a,b in edges)
labels=tuple(any(x&e==e for e in edge_masks) for x in range(1024))
def family(block):
    outside=[i for i in range(10) if i not in block]
    short=[sum((r>>j&1)<<v for j,v in enumerate(block)) for r in range(8)]
    return frozenset(sum(labels[sum((t>>j&1)<<v for j,v in enumerate(outside))|r]<<i for i,r in enumerate(short)) for t in range(128))
def maximal(items):
    big=[]
    for s in sorted(set(items),key=len,reverse=True):
        if not any(s<=t for t in big):big.append(s)
    return tuple(big)
@lru_cache(None)
def families(mult):
    if sum(mult)==1:
        i=next(j for j,n in enumerate(mult) if n)
        val=sum(((u>>i)&1)<<u for u in range(8))
        return tuple(frozenset([0,255,s]) for s in (val,255^val))
    result=[]
    for l0 in range(mult[0]+1):
        for l1 in range(mult[1]+1):
            for l2 in range(mult[2]+1):
                left=(l0,l1,l2);right=tuple(x-y for x,y in zip(mult,left))
                if not any(left) or not any(right) or left>right:continue
                for a in families(left):
                    for b in families(right):
                        result.append(a|b|frozenset(x&y for x in a for y in b))
                        result.append(a|b|frozenset(x|y for x in a for y in b))
    return maximal(result)
if __name__=='__main__':
    masks=[(1,1,1),(2,1,1),(1,2,1),(1,1,2)]
    types=Counter();details={}
    for triple in combinations(range(10),3):
        f=family(triple)
        row=tuple(any(f<=F for F in families(m)) for m in masks)
        typ=tuple(int((triple[i],triple[j]) in edges or (triple[j],triple[i]) in edges) for i,j in ((0,1),(0,2),(1,2)))
        types[typ,row]+=1
        details[triple]=row
    for (typ,row),n in sorted(types.items()):print(typ,row,n)
