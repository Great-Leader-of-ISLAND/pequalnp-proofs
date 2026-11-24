"""Verify every shared gate recipe against every stored 512-bit physical word."""
from argparse import ArgumentParser
from pathlib import Path
import gzip,hashlib
def stream(path):
    return gzip.open(path,'rt') if path.suffix=='.gz' else path.open()
def var(n):
    out=bytearray()
    while n>=128:out.append((n&127)|128);n>>=7
    out.append(n);return out
def main():
    ap=ArgumentParser(description=__doc__);ap.add_argument('table',type=Path);ap.add_argument('recipe',type=Path);ap.add_argument('--binary',type=Path)
    a=ap.parse_args();words=[];seed=None;complete=False
    with stream(a.table) as f:
        for line in f:
            tag,*v=line.split()
            if tag=='H':
                ver,seed,n=map(int,v)
                if ver!=1 or seed not in (0,1) or n!=258:raise ValueError('invalid native table header')
            elif tag=='W':
                if int(v[0])!=len(words):raise ValueError('nonsequential dictionary')
                words.append(int(v[1],16))
            elif tag=='E':
                num,wordcount,cert,miss,rounds=map(int,v)
                complete=(num==(9445 if seed else 2713) and len(words)==wordcount and num==cert and miss==0)
    if not complete:raise ValueError('original tight table is incomplete')
    nodes=[];mapping=[];expr=bytearray();links=bytearray();ended=False;roots=set()
    with stream(a.recipe) as f:
        for line in f:
            tag,*v=line.split();v=list(map(int,v))
            if tag=='H':
                if v!=[1,seed]:raise ValueError('wrong provenance header')
            elif tag=='E':
                if v!=[len(nodes),len(mapping)]:raise ValueError('wrong provenance trailer')
                ended=True
            elif tag=='R':
                dst,i=v
                if dst!=len(nodes) or i in roots or not 0<=i<9:raise ValueError('invalid input')
                roots.add(i);nodes.append(sum((r>>i&1)<<r for r in range(512)));expr+=var(i)
            elif tag in ('A','O'):
                dst,j,k=v
                if dst!=len(nodes) or not 0<=j<dst or not 0<=k<dst:raise ValueError('forward gate')
                nodes.append(nodes[j]&nodes[k] if tag=='A' else nodes[j]|nodes[k])
                expr+=var(9+2*j+(tag=='O'))+var(k)
            elif tag=='M':
                i,t=v
                if i!=len(mapping) or not 0<=t<len(nodes) or nodes[t]!=words[i]:raise ValueError('full word disagrees')
                mapping.append(t);links+=var(t)
            else:raise ValueError('invalid provenance record')
    if not ended or roots!=set(range(9)) or len(mapping)!=len(words):raise ValueError('incomplete provenance')
    binary=b'CT4482R1'+var(seed)+var(len(nodes))+var(len(words))+expr+links
    if a.binary:
        with a.binary.open('xb') as f:f.write(binary)
    print(f'RECIPE_OK seed={seed} nodes={len(nodes)} words={len(words)} '
          f'rows=512 packedBytes={len(binary)} sha256={hashlib.sha256(binary).hexdigest()}')
if __name__=='__main__':main()
