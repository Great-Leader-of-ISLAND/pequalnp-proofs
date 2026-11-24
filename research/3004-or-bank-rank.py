"""Lower bounds on the number of ordinary formula leaves with one OR bank on T."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import ast

src=(Path(__file__).resolve().parent/'3004-single-raw-bank.py').read_text()
W=ast.literal_eval(next(l[2:] for l in src.splitlines() if l.startswith('W=')))
rows=[sum(((v>>i)&1)<<k for k,v in enumerate(W)) for i in range(58)]
edges=rows[:21]
cols=rows[21:]
n=14
full=(1<<n)-1
adj=[0]*n
for e in edges:
    a,b=[i for i in range(n) if e>>i&1]
    adj[a]|=1<<b
    adj[b]|=1<<a
def bits(m):
    while m:
        s=m&-m
        yield s.bit_length()-1
        m^=s
def permitted_extension(m):
    v=0
    for c in cols:
        if c&m==m:v|=c
    return v
def matching(es,free):
    nb=[0]*7
    for e in es:
        if e&free!=e:continue
        p=(e&127).bit_length()-1
        nb[p]|=e>>7
    mates=[-1]*7
    def aug(a,seen):
        for b in bits(nb[a]):
            if b in seen:continue
            seen.add(b)
            if mates[b]<0 or aug(mates[b],seen):
                mates[b]=a;return 1
        return 0
    return sum(aug(i,set()) for i in range(7))
pairInfo=[]
for e in edges:
    a,b=bits(e); relevant=adj[a]|adj[b]|e
    pairInfo.append((e,relevant,permitted_extension(relevant^e)))
baseInfo=[(adj[i]|1<<i,permitted_extension(adj[i])) for i in range(n)]
def rank(T):
    good=[e for e,verts,extend in pairInfo if not T&verts or T&extend]
    avail=[0]*n
    for e in good:
        for i in bits(e):avail[i]+=1
    forced=sum(1<<i for i,(verts,ext) in enumerate(baseInfo) if avail[i]==0 or
        (avail[i]<3 and (not T&verts or T&ext)))
    return len(good)+bin(forced).count('1')+matching(good,full^forced)
def critical_pair(T,i):
    for j in bits(T & ~(1<<i)):
        for v in bits(adj[i] & ~(1<<j)):
            if not adj[j]&(1<<v):
                return True
    return False
if __name__=='__main__':
    for size in range(2,15):
        book=Counter();bad=[]
        for tup in combinations(range(n),size):
            T=sum(1<<v for v in tup);lb=rank(T);book[lb]+=1
            assert all(critical_pair(T,i) for i in tup)
            if lb+size+2-2<27:bad.append(T)
        if size==3:assert set(bad)==set(adj)
        print(size,'raw_leaf_lower',sorted(book.items()),'unresolved_at_multiplicity_2',len(bad),bad[:8])
