"""Drop repeated parent records and elide first-discovery target IDs in a verified BFS graph."""
from pathlib import Path
from argparse import ArgumentParser
from runpy import run_path
import hashlib
D=Path(__file__).parent
pack=run_path(str(D/'4482-junction-audit.py'))['var']
Reader=run_path(str(D/'4482-junction-unpack.py'))['Reader']

def compact(blob,random_access=False):
    if blob[:8]!=b'CT4482J1':raise ValueError('expected version 1')
    r=Reader(blob[8:]);seed,n,slen,plen=(r.number() for _ in range(4))
    shapes,parents=r.sub(slen),r.sub(plen)
    states=[(shapes.number(),shapes.number()) for _ in range(n)]
    preds=[None]+[(i-parents.number(),parents.number()) for i in range(1,n)]
    if not shapes.done() or not parents.done():raise ValueError('surplus fields')
    nex=1;edges=0;reused=0;arcs=bytearray()
    for i,(kind,q) in enumerate(states):
        if i>=nex:raise ValueError('node was never discovered by its parent')
        if kind&1:
            for _ in range(q):
                token=r.number();target=token>>4;g=token&15;edges+=1
                if target==nex:
                    if preds[target][0]!=i or preds[target][1]&15!=g:raise ValueError('bad parent')
                    nex+=1;arcs.extend(pack(g))
                elif target<nex:
                    reused+=1;arcs.extend(pack(((target+1)<<4)|g))
                else:raise ValueError('non-BFS backreference')
    if not r.done() or nex!=n:raise ValueError('incomplete arcs')
    fast=bytearray()
    if random_access:
        bits=width=0
        for _,encoded in preds[1:]:
            c=encoded>>4
            i,j=divmod(c//8,16)
            ranked=(j*(j-1)//2+i)*8+c%8
            if not 0<=i<j or ranked>=512:raise ValueError('first-discovery rule exceeds nine bits')
            bits|=ranked<<width;width+=9
            while width>=8:
                fast.append(bits&255);bits>>=8;width-=8
        if width:fast.append(bits)
    tag=b'CT4482J3' if random_access else b'CT4482J2'
    payload=tag+pack(seed)+pack(n)+pack(slen)+shapes.data+fast+arcs
    return payload,edges,reused

def main():
    p=ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('output',type=Path)
    p.add_argument('--random-access',action='store_true',help='also pack the raw first-discovery action in 9 bits')
    a=p.parse_args();blob=a.input.read_bytes();compactBytes,e,r=compact(blob,a.random_access)
    with a.output.open('xb') as f:f.write(compactBytes)
    print(f'JUNCTION_{compactBytes[6:8].decode()} old={len(blob)} packed={len(compactBytes)} ascii85Upper={(len(compactBytes)*5+3)//4} '
          f'edges={e} reuses={r} sha256={hashlib.sha256(compactBytes).hexdigest()}')
if __name__=='__main__':main()
