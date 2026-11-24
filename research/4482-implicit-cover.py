"""Check masks by deriving each next edge pair from the first uncovered group."""
from pathlib import Path
from runpy import run_path
from contextlib import redirect_stdout
from io import StringIO
D=Path(__file__).parent
with redirect_stdout(StringIO()):
    data=run_path(str(D/'4482-tight-probe.py'))
def low(x):return (x&-x).bit_length()-1
def check(bank,core,limit=1000):
    n=len(bank);N=1<<n;allblocks=(1<<N)-1;alledges=(1<<258)-1
    # Blocks are packed in raw integer order. The lowest remaining candidate
    # has no untested proper subset and is cheap to separate.
    bitcols=[sum((b>>i&1)<<b for b in range(N)) for i in range(n)]
    must=sum(1<<b for b in range(N) if bin(b).count('1')<=n-5 and bin(b&core).count('1')>=2)
    rounds=0;tests=0;scans=0
    while must and rounds<limit:
        B=low(must);exclusive=alledges;inside=[]
        for i,(p,m) in enumerate(bank):
            if B>>i&1:inside.append((p,m))
            else:exclusive&=~(p^m)
        def pair(q,pos,neg):
            nonlocal tests
            tests+=1
            if not pos or not neg:return None
            if q==len(inside):return low(pos),low(neg)
            a,b=inside[q]
            return pair(q+1,pos&~a,neg) or pair(q+1,pos&a,neg&b)
        e=pair(0,exclusive,exclusive)
        if e is None:return False,rounds,tests,scans
        r,s=e;interval=allblocks
        for c,(p,m) in zip(bitcols,bank):
            if (p^m)>>r&1 or (p^m)>>s&1:interval&=c
            if p>>r&1 and not m>>s&1:interval&=~c
        assert interval>>B&1
        must&=~interval;rounds+=1;scans+=len(inside)
    return not must,rounds,tests,scans
if __name__=='__main__':
    for i,c in [(0,493),(1,254)]:
        print(i,c,check(data[f'bank{i}'],c))
