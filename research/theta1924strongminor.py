"""Enumerate signed identifications of vertex inputs as additional restriction tests."""
from itertools import combinations
from time import monotonic
from theta1924front import F,PERMS
from theta1924cofactors import dense_values,run,slices,count

def signed_minors():
    result=[]
    orbits={}
    for a,b in combinations(range(7),2):
        # A six-bit row explicitly chooses every coordinate except b.
        ids=tuple(i for i in range(7) if i!=b)
        for anti in (0,1):
            key=(min(tuple(sorted((perm[a],perm[b]))) for perm in PERMS),anti)
            rows=[]
            for r in range(64):
                old=sum((r>>j&1)<<v for j,v in enumerate(ids))
                rows.append(old|(((old>>a&1)^anti)<<b))
            f=sum((F>>r&1)<<j for j,r in enumerate(rows))
            exact,active=dense_values(f,6)
            if exact&1:exact^=(1<<(1<<len(active)))-1
            if key not in orbits:
                lo=len(active)-1
                while lo<10 and not run(exact,len(active),lo):lo+=1
                orbits[key]=lo
                print('minor',a,b,'opposite',anti,'vars',len(active),'proved lower',lo,flush=True)
            lo=orbits[key]
            if lo<7:continue
            dense=tuple(r for j,r in enumerate(rows) if not any(j>>p&1 for p in range(6) if p not in active))
            full=(1<<len(dense))-1
            cols=[sum((r>>a&1)<<j for j,r in enumerate(dense)) for a in range(7)]
            cols=tuple(set(x^(full if x&1 else 0) for x in cols))
            cheap={0:0,**{x:0 for x in cols}}
            for a1,b1 in combinations(cols,2):
                for z in (a1&b1,a1|b1,a1&(full^b1),b1&(full^a1)):cheap.setdefault(z,1)
            for u in tuple(cheap):
                if cheap[u]!=1:continue
                for v in cols:
                    for z in (u&v,u|v,u&(full^v),v&(full^u)):cheap.setdefault(z,2)
            result.append((dense,lo,cheap,full))
    return result
if __name__=='__main__':
    start=monotonic();cut=slices()+signed_minors();print('cuts',len(cut),flush=True)
    count(cut);print('time',monotonic()-start,flush=True)
