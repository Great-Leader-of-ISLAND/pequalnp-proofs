"""Minimum number of extra raw leaves forced by incompatible single-occurrence rectangles."""
from pathlib import Path
import runpy
D=runpy.run_path(str(Path(__file__).with_name('3004-mixed-bank-rank.py')))
E,N=D['edges'],D['cols'];bits=D['bits'];F=D['full'];n=len(E)
pairs=[[] for _ in range(14)]
for k,e in enumerate(E):
    for v in bits(e):
        mask=sum(1<<l for l,c in enumerate(N) if e&~c==1<<v)
        pairs[v].append((k,mask))
def pressure(pos,neg,R):
    prow=[0]*14;ncol=[0]*14
    for v,ts in enumerate(pairs):
        for k,cs in ts:
            ns=neg&cs if pos>>k&1 else cs
            if ns:
                prow[v]|=1<<k;ncol[v]|=ns
        if prow[v] and not R>>v&1:return 100
    clash=[]
    for e in E:
        u,v=bits(e)
        if prow[u]&prow[v] and ncol[u]&ncol[v]:clash.append(e)
    return bin(R).count('1')+D['matching'](clash,R)
if __name__=='__main__':
 for p,n in [(29183,137405399040),(29183,137371844608),(25535,137405399040),(1065919,137405399040)]:
    print(p,n,pressure(p,n,8191))

# If all four ordinary leaves in a path had only a single occurrence, zeroing
# the bank and every other variable would give a read-once minor computing P4.
paths=[]
edgeset=set(E)
for i,e in enumerate(E):
    a,b=bits(e)
    for j,s in enumerate(E):
        if e==s or not s&(1<<a):continue
        for k,t in enumerate(E):
            if e==t or not t&(1<<b):continue
            vs=e|s|t
            if bin(vs).count('1')==4:
                paths.append((1<<i|1<<j|1<<k,vs))
assert len(paths)==84
def marks_possible(pos,neg,R,budget):
    slack=budget-bin(R).count('1')
    if slack<0:return False
    misses=((1<<len(E))-1)^pos
    clauses=[vs for es,vs in paths if es&misses==es]
    prow=[0]*14;ncol=[0]*14
    for v,ts in enumerate(pairs):
        for k,cs in ts:
            ns=neg&cs if pos>>k&1 else cs
            if ns:prow[v]|=1<<k;ncol[v]|=ns
        if prow[v] and not R>>v&1:return False
    for e in E:
        u,v=bits(e)
        if prow[u]&prow[v] and ncol[u]&ncol[v]:clauses.append(e)
    if not clauses:return True
    def cover(clauses,left):
        if not clauses:return True
        if not left:return False
        short=min(clauses,key=lambda z: bin(z).count('1'))
        return any(cover([q for q in clauses if q&bit==0],left-1) for bit in (1<<v for v in bits(short&R)))
    return cover(clauses,slack)
