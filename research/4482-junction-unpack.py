"""Replay a packed junction archive from its root, with no TSV, recipe or graph sidecar."""
from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from pathlib import Path
from runpy import run_path
import hashlib
D=Path(__file__).parent
ref=run_path(str(D/'4482-junction-audit.py'))

class Reader:
    def __init__(self,data):self.data=data;self.i=0
    def number(self):
        v=0
        for s in range(0,35,7):
            if self.i>=len(self.data):raise ValueError('truncated varint')
            b=self.data[self.i];self.i+=1;v|=(b&127)<<s
            if b<128:
                if s and b==0:raise ValueError('noncanonical varint')
                return v
        raise ValueError('oversized varint')
    def sub(self,n):
        if self.i+n>len(self.data):raise ValueError('truncated substream')
        s=self.data[self.i:self.i+n];self.i+=n;return Reader(s)
    def done(self):return self.i==len(self.data)

def read(blob):
    if blob[:8] not in (b'CT4482J1',b'CT4482J2'):raise ValueError('magic')
    short=blob[:8]==b'CT4482J2'
    r=Reader(blob[8:]);seed=r.number();n=r.number();slen=r.number();plen=0 if short else r.number()
    if seed not in (0,1) or not 1<=n<=15000:raise ValueError('bounds')
    sh,pr=r.sub(slen),r.sub(plen)
    shape=[(sh.number(),sh.number()) for _ in range(n)]
    parent=[] if short else [None]+[(i-pr.number(),pr.number()) for i in range(1,n)]
    routes=[[r.number() for _ in range(q)] if shapeId&1 else [] for shapeId,q in shape]
    if not sh.done() or not pr.done() or not r.done():raise ValueError('trailing fields')
    perms=ref['lib']['automorphisms'](seed)
    table=[]
    for g in perms:
        rm=[sum(((r>>i)&1)<<g[i] for i in range(9)) for r in range(512)]
        layers=[]
        for j in range(0,512,8):
            t=[0]*256
            for b in range(1,256):
                t[b]=t[b&(b-1)] | 1<<rm[j+(b&-b).bit_length()-1]
            layers.append(t)
        table.append(layers)
    @lru_cache(None)
    def view(w,g):
        if g>=len(perms):raise ValueError('invalid transporter')
        if not g:return w
        out=0
        for layer in table[g]:out|=layer[w&255];w>>=8
        return out
    def step(ws,code,g):
        mask=code%4;op=code//4%2;both=code//8;a=both//16;b=both%16
        if not 0<=a<b<len(ws):raise ValueError('invalid operands')
        w=ws[a]|ws[b] if op else ws[a]&ws[b]
        if w in ws:raise ValueError('nonfresh gate')
        result=[w]+[v for i,v in enumerate(ws) if not (i==a and mask&1 or i==b and mask&2)]
        return tuple(sorted(view(v,g) for v in result))
    raws=tuple(sum(((r>>i)&1)<<r for r in range(512)) for i in range(9))
    banks=[tuple(sorted(raws+((raws[0]|raws[2],) if seed else ())))]
    for idx,(p,entry) in enumerate(parent[1:],1):
        if not 0<=p<idx or not shape[p][0]&1:raise ValueError('invalid parent')
        banks.append(step(banks[p],entry>>4,entry&15))
    edges=0;leaves=Counter();inners=0
    for idx,((shapeId,q),rs) in enumerate(zip(shape,routes)):
        if idx>=len(banks):raise ValueError('unreached state')
        xs=banks[idx]
        k=shapeId>>1
        if not 1<=k<=7 or not 6<len(xs)<=6+k:raise ValueError(('budget/width',idx))
        if not shapeId&1:
            if len(xs)!=6+k:raise ValueError('loose leaf')
            leaves[q]+=1
            continue
        inners+=1
        expected=list(ref['moves'](xs,k))
        if len(expected)!=len(rs):raise ValueError(('source fanout',idx,len(expected),len(rs)))
        for (code,_),entry in zip(expected,rs):
            target,g=entry>>4,entry&15
            child=step(xs,code,g)
            if short and target==0:
                t=len(banks);banks.append(child)
            else:t=target-int(short)
            if not 0<=t<len(banks) or t>=n or (shape[t][0]>>1)<k-1 or child!=banks[t]:
                raise ValueError(('bad edge',idx,code,t,g))
            edges+=1
    if shape[0][0]!=15:raise ValueError('root budget')
    if len(banks)!=n or len(set(banks))!=n:raise ValueError('non-unique or missing canonical records')
    if any(c!=1 for c in leaves.values()):raise ValueError('duplicate retained leaf id')
    return seed,len(banks),inners,len(leaves),edges

def main():
    p=ArgumentParser(description=__doc__);p.add_argument('archive',type=Path);a=p.parse_args()
    data=a.archive.read_bytes()
    seed,n,i,l,e=read(data)
    print(f'JUNCTION_UNPACK_OK seed={seed} restored={n} internals={i} leaves={l} '
          f'outgoing={e} bytes={len(data)} ascii85Upper={(len(data)*5+3)//4} '
          f'sha256={hashlib.sha256(data).hexdigest()}')
if __name__=='__main__':main()
