"""Count the exact seven-input search tree after topologically sorting actual circuit gates."""
from pathlib import Path
from itertools import combinations
from functools import lru_cache
from time import monotonic
import re,json
s=Path(__file__).with_name('CoSeedBenchmark.lean').read_text().split('def raw : List Word := [',1)[1].split(']',1)[0]
raw=[tuple(int(v,16) for v in q) for q in re.findall(r'\((0x[0-9a-f]+),(0x[0-9a-f]+)\)',s)]
mask=(1<<440)-1;goal=(mask,0);zero=(0,0)
def op(a,b):
    p,n=a;s,t=b
    return ((p&s,n&t),(p|s,n|t),(p&~s,n&~t),(s&~p,t&~n))
def work(j,ordered):
    start=monotonic();active=[*raw,op(raw[0],raw[j])[1]];nodes=0
    @lru_cache(350000)
    def go(m,ws,last):
        nonlocal nodes
        nodes+=1
        if nodes%512==0 and monotonic()-start>210:raise TimeoutError
        count=1
        if len(ws)>m+1 or m==0:return count
        for i,q in combinations(range(len(ws)),2):
            da,a=ws[i];db,b=ws[q]
            depth=1+max(da,db) if ordered else 0
            if ordered and depth<last[0]:continue
            rest=ws[:i]+ws[i+1:q]+ws[q+1:];base=0;sa=a[0]^a[1];sb=b[0]^b[1]
            for _,(p,n) in rest:base |=p^n
            for z in op(a,b):
                if z==zero or any(w==z for _,w in ws):continue
                assert z!=goal
                # A legal circuit can be sorted in order of increasing gate depth,
                # and within each depth in order of the truth function it computes.
                key=(depth,z) if ordered else (0,zero)
                if ordered and key<=last:continue
                withz=base|(z[0]^z[1])
                for keep,ext in [((),0),((ws[i],),sa),((ws[q],),sb),((ws[i],ws[q]),sa|sb)]:
                    if len(rest)+len(keep)+1>m or withz|ext!=mask:continue
                    count+=go(m-1,tuple(sorted((*(rest+keep),key if ordered else (0,z)))),key)
        return count
    try: size=go(10,tuple(sorted((0,v) for v in active)),(0,zero))
    except TimeoutError: size='timeout'
    stats=go.cache_info()
    print(json.dumps({'j':j,'order':ordered,'recursive_calls':size,'unique_cached':nodes,'cache_hits':stats.hits,'seconds':round(monotonic()-start,3)}),flush=True)
    go.cache_clear()
for j in (2,3):
 for mode in (True,False):work(j,mode)
