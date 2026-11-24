"""Generate small actual nonterminal frontier examples for kernel cost measurements."""
from itertools import combinations
from pathlib import Path
import time
from theta1924front import X,F,POS,NEG,ALL,ALLPAIRS
from theta1924free import separated

probes={}
seen=set()
def dfs(k,ws):
    if k<9:
        if k not in probes:probes[k]=ws
        if all(i in probes for i in (2,3,4,5,6)):return True
    if k==0:return False
    for a,b in combinations(ws,2):
        rest=set(ws)-{a,b}
        for z in (a&b,a|b,a&(ALL^b),b&(ALL^a)):
            if z in ws or not z:continue
            for keep in ((),(a,),(b,),(a,b)):
                nxt=tuple(sorted((*rest,z,*keep)))
                if len(nxt)>k or (k-1,nxt) in seen:continue
                cover=0
                for c in nxt:cover|=separated(c)
                if cover!=ALLPAIRS:continue
                seen.add((k-1,nxt))
                if dfs(k-1,nxt):return True
    return False

def packed(mask):
    p=sum(((mask>>x)&1)<<(i*27+j) for i,x in enumerate(POS) for j,y in enumerate(NEG))
    n=sum(((mask>>y)&1)<<(i*27+j) for i,x in enumerate(POS) for j,y in enumerate(NEG))
    return '('+hex(p)+','+hex(n)+')'

if __name__=='__main__':
    import argparse
    q=argparse.ArgumentParser()
    q.add_argument('--output',type=Path)
    a=q.parse_args()
    dfs(10,tuple(sorted(X)))
    from collections import Counter
    print('state layers',sorted(Counter(k for k,ws in seen).items()),'distinct signals',len({x for k,ws in seen for x in ws}))
    print('probe sizes',[(k,len(ws)) for k,ws in sorted(probes.items())],len(seen))
    if a.output:
        lines=['namespace CoThetaBits']
        for k,ws in sorted(probes.items()):
            lines.append(f'def probe{k} : List Wire := ['+',\n'.join(packed(z) for z in ws)+']')
        lines.append('end CoThetaBits')
        a.output.write_text('\n'.join(lines)+'\n')
