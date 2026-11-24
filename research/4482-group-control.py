"""Group genuine 11-wire physical states; certify with worst allowed local behavior."""
from pathlib import Path
from runpy import run_path
from itertools import combinations
D=Path(__file__).parent;lib=run_path(str(D/'4482-implicit-cover.py'));db=lib['data']
def bounds(bank):return [(p,n,p^n) for p,n in bank]
def merge(b,c):return [(p|q,n&m,d|e) for (p,n,d),(q,m,e) in zip(b,c)]
# Independent bitset implementation with separate maximal change masks.
def solve(bank,core):
    width=len(bank);N=1<<width;allrows=(1<<258)-1
    columns=[sum((b>>j&1)<<b for b in range(N)) for j in range(width)]
    missing=sum(1<<b for b in range(N) if bin(b).count('1')<=width-5 and bin(b&core).count('1')>=2)
    steps=0
    while missing:
        group=(missing&-missing).bit_length()-1
        inside=[];ex=allrows
        for j,(p,n,d) in enumerate(bank):
            if group>>j&1:inside.append((p,n))
            else:ex&=~d
        def witness(i,p,n):
            if not p or not n:return None
            if i==len(inside):return (p&-p).bit_length()-1,(n&-n).bit_length()-1
            a,b=inside[i]
            return witness(i+1,p&~a,n) or witness(i+1,p&a,n&b)
        pair=witness(0,ex,ex)
        if pair is None:return False,steps
        e,f=pair;interval=(1<<N)-1
        for mask,(p,n,d) in zip(columns,bank):
            if d>>e&1 or d>>f&1:interval&=mask
            if p>>e&1 and not n>>f&1:interval&=~mask
        assert interval>>group&1
        missing&=~interval;steps+=1
    return True,steps
if __name__=='__main__':
    raw=db['raw'];g=db['g1'];gate=db['gate'];core=493
    cur=bounds(db['bank0']);group=[(1,3,4)]
    for a,b in combinations(range(9),2):
        for op in (False,True):
            q=gate(raw[a],raw[b],op)
            if (op,a,b) in group or q==g:continue
            extension=merge(cur,bounds(raw+[g,q]))
            if solve(extension,core)[0]:cur=extension;group.append((int(op),a,b))
    print('width=11 distinct_real_states=',len(group),'common_rounds=',solve(cur,core), 'ops=',group)
