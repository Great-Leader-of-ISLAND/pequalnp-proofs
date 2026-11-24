"""Exact small cofactor lower bounds and their effect on the theta live search."""
from functools import lru_cache
from itertools import combinations
from time import monotonic
from theta1924front import X,F,ALL,ALLPAIRS
from theta1924free import separated

def dense_values(table,n):
    rel=[i for i in range(n) if any(((table>>r)^(table>>(r^1<<i)))&1 for r in range(1<<n))]
    return sum(((table >> sum(((r>>j)&1)<<i for j,i in enumerate(rel)))&1)<<r for r in range(1<<len(rel))),rel

def run(table,n,cap):
    relcount=n
    full=(1<<(1<<n))-1
    cols=tuple(sum(((r>>i)&1)<<r for r in range(1<<n)) for i in range(n))
    P=[r for r in range(1<<n) if table>>r&1]
    N=[r for r in range(1<<n) if not(table>>r&1)]
    sepAll=(1<<(len(P)*len(N)))-1
    @lru_cache(None)
    def sep(w):
        return sum((((w>>p)^(w>>q))&1)<<(i*len(N)+j) for i,p in enumerate(P) for j,q in enumerate(N))
    @lru_cache(None)
    def visit(k,ws):
        if table in ws:return True
        for a,b in combinations(ws,2):
            rest=tuple(w for w in ws if w not in (a,b))
            fullcov=0
            for w in rest:fullcov|=sep(w)
            for z in (a&b,a|b,a&(full^b),b&(full^a)):
                if not z or z in ws:continue
                for reserve in ((),(a,),(b,),(a,b)):
                    if len(rest)+len(reserve)+1>k:continue
                    cov=fullcov|sep(z)
                    for w in reserve:cov|=sep(w)
                    if cov==sepAll and visit(k-1,tuple(sorted((*rest,z,*reserve)))):return True
        return False
    return visit(cap,tuple(sorted(cols)))

def slices():
    out=[]
    for i in range(7):
        for v in range(2):
            rows=tuple(r for r in range(128) if r>>i&1==v)
            target=sum(((F>>r)&1)<<j for j,r in enumerate(rows))
            exact,active=dense_values(target,6)
            if exact&1:exact^=(1<<(1<<len(active)))-1
            lb=len(active)-1
            while not run(exact,len(active),lb):
                lb+=1
                if lb==9:break
            # Extra irrelevant raw input nodes may be fixed zero for free.
            dense=tuple(r for j,r in enumerate(rows) if not any(j>>p&1 for p in range(6) if p not in active))
            m=(1<<len(dense))-1
            cols=tuple(sum(((r>>a)&1)<<j for j,r in enumerate(dense)) for a in range(7) if a!=i)
            one={0:0,**{x:0 for x in cols}}
            for a,b in combinations(cols,2):
                for z in (a&b,a|b,a&(m^b),b&(m^a)):one.setdefault(z,1)
            for a in tuple(one):
                if one[a]!=1:continue
                for b in cols:
                    for z in (a&b,a|b,a&(m^b),b&(m^a)):one.setdefault(z,2)
            out.append((dense,lb,one,m))
            print('cut',i,v,'active',len(active),'lower',lb,flush=True)
    return out

def count(cuts):
    @lru_cache(None)
    def cost(w):
        out=[]
        for rows,lb,cheap,m in cuts:
            n=sum(((w>>r)&1)<<j for j,r in enumerate(rows))
            if n&1:n^=m
            out.append((n,cheap.get(n,99)))
        return out
    pruned=calls=0
    @lru_cache(maxsize=120000)
    def go(k,ws):
        nonlocal pruned,calls
        calls+=1
        tot=1
        for j,(_,lb,_,_) in enumerate(cuts):
            if k>=lb:continue
            extra=dict(cost(w)[j] for w in ws)
            if k+sum(extra.values())<lb:
                pruned+=1
                return tot
        for a,b in combinations(ws,2):
            rest=tuple(w for w in ws if w not in (a,b))
            base=0
            for w in rest:base|=separated(w)
            for z in (a&b,a|b,a&(ALL^b),b&(ALL^a)):
                if not z or z in ws:continue
                for keep in ((),(a,),(b,),(a,b)):
                    if len(rest)+len(keep)+1>k:continue
                    cov=base|separated(z)
                    for w in keep:cov|=separated(w)
                    if cov==ALLPAIRS:tot+=go(k-1,tuple(sorted((*rest,z,*keep))))
        return tot
    print('total unfolded',go(10,tuple(sorted(X))),'distinct',calls,'pruned',pruned)
if __name__=='__main__':
    t=monotonic();cut=slices();count(cut);print('seconds',monotonic()-t)
