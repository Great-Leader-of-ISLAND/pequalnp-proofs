"""Pack pure grouping hints for real tight leaves; no truth columns or interval proofs are trusted."""
import argparse,json,hashlib
from pathlib import Path
from runpy import run_path
D=Path(__file__).parent
sp=run_path(str(D/'4482-share-table.py'))
var=run_path(str(D/'4482-junction-audit.py'))['var']
R=run_path(str(D/'4482-junction-unpack.py'))['Reader']

def rankperm(order):
    left=list(range(len(order)));z=0
    for x in order:
        i=left.index(x);z=z*len(left)+i;left.pop(i)
    return z

def permrank(n,z):
    digits=[]
    for p in range(1,n+1):z,t=divmod(z,p);digits.append(t)
    if z:raise ValueError('excess permutation digits')
    left=list(range(n));return [left.pop(p) for p in reversed(digits)]

def colseq(data,sid,g):
    ws=data.states[sid][0]
    return sorted(range(len(ws)),key=lambda i:data.sig(ws[i],g))

def encode(data,root,first,count,groups):
    out=bytearray(b'CT4482L1');out+=var(root)+var(first)+var(count)+var(len(groups))
    long=0
    for group in groups:
        cap=group['fuel']
        if not 0<=cap<=63:raise ValueError('round budget exceeds encoding')
        out+=var(group['core']*64+cap)
        ms=sorted(group['members'],key=lambda m:m[0]);out+=var(len(ms))
        prev=first
        for sid,g,seq in ms:
            order=colseq(data,sid,g);n=len(order)
            if n>=15 or not 0<=g<16 or sorted(seq)!=list(range(n)):raise ValueError('alignment')
            remap=[order.index(i) for i in seq];orig=list(range(n))
            j=next((j for j in range(n) if remap==orig[:j]+orig[j+1:]+[j]),15)
            out+=var(sid-prev);prev=sid;out.append(16*g+j)
            if j==15:out+=var(rankperm(remap));long+=1
    return bytes(out),long

def decode(data,blob):
    if blob[:8]!=b'CT4482L1':raise ValueError('leaf magic')
    r=R(blob[8:]);root,first,count,ng=(r.number() for _ in range(4))
    if root not in (0,1) or first+count>len(data.states) or ng>count:raise ValueError('leaf header')
    groups=[]
    for _ in range(ng):
        core,fuel=divmod(r.number(),64);m=r.number();ms=[];sid=first
        if not 1<=m<=count:raise ValueError('empty or oversized group')
        for _ in range(m):
            sid+=r.number()
            if sid>=first+count or r.done():raise ValueError('member outside slice')
            g,j=divmod(r.data[r.i],16);r.i+=1
            if g>=len(data.perms):raise ValueError('non-graph action')
            order=colseq(data,sid,g);n=len(order)
            if j==15:seq=[order[t] for t in permrank(n,r.number())]
            elif j<n:seq=order[:j]+order[j+1:]+[order[j]]
            else:raise ValueError('bad alignment')
            ms.append([sid,g,seq])
        groups.append(dict(core=core,fuel=fuel,members=ms))
    if not r.done():raise ValueError('trailing bytes')
    return root,first,count,groups

def main():
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('table',type=Path)
    a.add_argument('manifest',type=Path);a.add_argument('output',type=Path);ns=a.parse_args()
    seed,states=sp['reader'](ns.table);doc=json.loads(ns.manifest.read_text())
    if doc['seed']!=seed or doc['format'] not in (2,3):raise ValueError('input manifest')
    data=sp['Data'](seed,states,doc['orbit']);lo,n=doc['first'],doc['count'];gs=doc['groups']
    payload,long=encode(data,seed,lo,n,gs);s,first,count,replayed=decode(data,payload)
    if (s,first,count)!=(seed,lo,n):raise ValueError('changed slice')
    for original,read in zip(gs,replayed):
        if original['core']!=read['core'] or original['fuel']!=read['fuel'] or sorted(original['members'])!=read['members']:
            raise ValueError('changed group')
    rounds,size,coverage=sp['audit'](data,replayed,lo,n)
    with ns.output.open('xb') as f:f.write(payload)
    print(f'LEAF_PACK_OK seed={seed} first={lo} states={coverage} groups={len(gs)} '
          f'rounds={rounds} maxGroup={size} fullPermExceptions={long} bytes={len(payload)} '
          f'sha256={hashlib.sha256(payload).hexdigest()}')
if __name__=='__main__':main()
