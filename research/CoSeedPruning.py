"""Measure signed read-once and two-wire pruning on the exact 440 sampled pairs."""
from functools import lru_cache
from itertools import combinations
from time import monotonic
import argparse,re
from pathlib import Path
import json
def probe(raw,j,method,timeout):
    mask=(1<<440)-1;goal=(mask,0);zero=(0,0);start=monotonic()
    nodes=0;branches=0;pruned=0
    def ops(a,b):
        p,n=a;s,t=b
        return ((p&s,n&t),(p|s,n|t),(p&~s,n&~t),(s&~p,t&~n))
    @lru_cache(240000)
    def go(m,ws):
        nonlocal nodes,branches,pruned
        nodes+=1
        if nodes%256==0 and monotonic()-start>timeout:raise TimeoutError
        if goal in ws:return True
        if len(ws)>m+1 or m==0:return False
        full=twice=0
        for p,n in ws:
            d=p^n;twice|=full&d;full|=d
        if full!=mask:return False
        once=full^twice
        if method and len(ws)==m+1:
            if any((p&~n&once) and (n&~p&once) for p,n in ws):
                pruned+=1;return False
        for i,j in combinations(range(len(ws)),2):
            a,b=ws[i],ws[j];rest=ws[:i]+ws[i+1:j]+ws[j+1:];ba=0
            for p,n in rest:ba |=p^n
            for z in ops(a,b):
                if z==zero or z in ws:continue
                cov=ba|z[0]^z[1]
                for keep in ((),(a,),(b,),(a,b)):
                    if len(rest)+len(keep)>m-1:continue
                    cc=cov
                    for p,n in keep:cc |=p^n
                    if cc!=mask:continue
                    branches+=1
                    if go(m-1,tuple(sorted((*rest,z,*keep)))):return True
        return False
    head=ops(raw[0],raw[j])[1]
    try:result=go(10,tuple(sorted([*raw,head])))
    except TimeoutError:result='timed_out'
    return dict(j=j,method=method,result=result,unique=nodes,branches=branches,pruned=pruned,seconds=round(monotonic()-start,3))
if __name__=='__main__':
    path=Path(__file__).with_name('CoSeedBenchmark.lean')
    s=path.read_text().split('def raw : List Word := [',1)[1].split(']',1)[0]
    raw=[tuple(int(v,16) for v in q) for q in re.findall(r'\((0x[0-9a-f]+),(0x[0-9a-f]+)\)',s)]
    assert len(raw)==7
    for method in (1,0):
        for j in (2,3):print(json.dumps(probe(raw,j,method,75)),flush=True)
