"""Re-enumerate every admissible move, audit orbit routing, and encode the state DAG."""
from collections import deque,Counter
from functools import lru_cache
from argparse import ArgumentParser
from pathlib import Path
from runpy import run_path
import gzip,hashlib,json,struct
D=Path(__file__).parent
lib=run_path(str(D/'4482-share-table.py'))
mark=lib['mark'];TOP=(1<<258)-1

def read_graph(p):
    words=[];recipes=[];nodes=[];seed=None;trailer=None
    op=gzip.open if p.suffix=='.gz' else open
    with op(p,'rt') as f:
        for line in f:
            kind,*v=line.split()
            if kind=='H':
                ver,seed,rows=map(int,v)
                if ver!=1 or seed not in (0,1) or rows!=258:raise ValueError('header')
            elif kind=='W':
                i,r=map(int,v[:2]);w=int(v[2],16)
                if i!=len(words) or not 0<=w<1<<512:raise ValueError('word record')
                words.append(w);recipes.append(r)
            elif kind in ('I','L'):
                i,budget,leaf,n,*idx=map(int,v)
                if i!=len(nodes) or len(idx)!=n or not 6<n<=6+budget or min(idx)<0 or max(idx)>=len(words):raise ValueError('node indices')
                if (kind=='I')!=(leaf<0) or (kind=='L' and n!=6+budget):raise ValueError('terminal metadata')
                ws=tuple(words[j] for j in idx)
                if ws!=tuple(sorted(set(ws))):raise ValueError('physical nodes are not canonical sets')
                nodes.append((ws,budget,leaf))
            elif kind=='E':trailer=tuple(map(int,v))
            else:raise ValueError('unexpected record')
    inner=sum(x[2]<0 for x in nodes);leaves=sorted(x[2] for x in nodes if x[2]>=0)
    if trailer!=(len(nodes),inner,len(leaves),len(words)) or leaves!=list(range(len(leaves))):raise ValueError('incomplete graph metadata')
    if (inner,len(leaves))!=((965,9445) if seed else (303,2713)):raise ValueError('wrong signed root totals')
    return seed,nodes,dict(zip(words,recipes))

def moves(ws,k):
    # Code = ((i*16+j)*2+op)*4+drop; bit0 drops i and bit1 drops j.
    n=len(ws);deltas=[mark(w)[2] for w in ws]
    if n<=6:return
    for i in range(n):
        for j in range(i+1,n):
            remaining=0
            for z,v in enumerate(deltas):
                if z!=i and z!=j:remaining|=v
            for op in (0,1):
                t=(ws[i]|ws[j]) if op else (ws[i]&ws[j])
                if t in ws:continue
                active=remaining|mark(t)[2]
                for mask in range(4):
                    if n+1-(mask&1)-((mask>>1)&1)>6+k-1:continue
                    if active|(0 if mask&1 else deltas[i])|(0 if mask&2 else deltas[j])!=TOP:continue
                    child=(t,)+tuple(w for h,w in enumerate(ws)
                                      if not (h==i and mask&1 or h==j and mask&2))
                    yield (((16*i+j)*2+op)*4+mask),child

def var(n):
    out=bytearray()
    while n>=128:out.append((n&127)|128);n>>=7
    out.append(n);return out

def audit(seed,raw,limit_sample=8,stratified=False):
    perms=lib['automorphisms'](seed);actions=[]
    # Python pushes an assignment to its image. Lean's reorder pulls back
    # along its row equivalence. Match On the raw input coordinates, which
    # uniquely determine the required official row permutation.
    formal_group=[0,10] if seed else [0,1,2,3,4,5,9,8,7,6,10,11]
    for g in perms:
        rm=[sum((r>>i&1)<<g[i] for i in range(9)) for r in range(512)]
        lut=[]
        for i in range(0,512,8):
            z=[0]*256
            for v in range(1,256):
                b=(v&-v).bit_length()-1;z[v]=z[v&(v-1)]|(1<<rm[i+b])
            lut.append(z)
        actions.append(lut)
    @lru_cache(None)
    def image(w,g):
        if not g:return w
        z=0
        for lut in actions[g]:
            z|=lut[w&255];w>>=8
        return z
    by={}
    for old,(ws,k,leaf) in enumerate(raw):
        if ws not in by or k>by[ws][0]:by[ws]=(k,leaf,old)
    rawinputs=tuple(sum((r>>i&1)<<r for r in range(512)) for i in range(9))
    root=tuple(sorted(rawinputs+((rawinputs[0]|rawinputs[2],) if seed else ())))
    if root not in by or by[root][0]!=7:raise ValueError('canonical root missing')
    seen={root:0};q=deque([root]);parent=[None];info=[];routing=[];hist=Counter();samples=[];dominated=0
    while q:
        ws=q.popleft();nid=seen[ws];k,leaf,archive_id=by[ws];info.append((k,leaf,archive_id))
        if leaf>=0:routing.append([]);continue
        links=[]
        for code,child in moves(ws,k):
            for g in range(len(perms)):
                candidate=tuple(sorted(image(w,g) for w in child))
                state=by.get(candidate)
                if state is not None and state[0]>=k-1:break
            else:raise ValueError(f'uncovered actual transition seed={seed} node={nid} rem={k} move={code}')
            if state[0]>k-1:dominated+=1
            if candidate not in seen:
                seen[candidate]=len(seen);parent.append((nid,code,g));q.append(candidate)
            links.append((code,seen[candidate],g))
        routing.append(links);hist[len(links)]+=1
        if not stratified and len(samples)<limit_sample:
            samples.append({'id':nid,'budget':k,'words':[hex(w) for w in ws],
                            'routes':links})
    # Separate streams. Routing stores one target and one group index per actual
    # survivor, with the gate and retention selection reconstructed by moves().
    shape=bytearray();pred=bytearray();child=bytearray()
    discoveryDepth=[0]
    for i,((k,leaf,_),kids) in enumerate(zip(info,routing)):
        shape+=var((k<<1)|(leaf<0))
        shape+=var(len(kids) if leaf<0 else leaf)
        if i:
            p,c,g=parent[i];pred+=var(i-p)+var((c<<4)|g)
            discoveryDepth.append(discoveryDepth[p]+1)
        for _,t,g in kids:child+=var((t<<4)|g)
    nodes_by_id=list(seen)
    bands=[[],[],[],[],[]]
    for nid,rs in enumerate(routing):
        if info[nid][1]>=0:continue
        k=len(rs);bands[0 if k==0 else 1 if k<=8 else 2 if k<=24 else 3 if k<=63 else 4].append(nid)
    if stratified:
        if limit_sample<5:raise ValueError('stratified mode needs at least five samples')
        for b,part in enumerate(bands):
            wanted=min(len(part),limit_sample//5+int(b<limit_sample%5))
            part.sort(key=lambda i:(len(routing[i]),info[i][0],len(nodes_by_id[i]),i))
            for j in range(wanted):
                i=part[(2*j+1)*len(part)//(2*wanted)]
                samples.append({'id':i,'budget':info[i][0],'words':[hex(w) for w in nodes_by_id[i]],
                                'routes':routing[i],'band':b,'population':len(part)})
    for sample in samples:
        inputs=[int(w,16) for w in sample['words']]
        gids=sorted({g for _,t,g in sample['routes']})
        tids=sorted({t for _,t,g in sample['routes']})
        sample['images']={str(g):[hex(image(w,g)) for w in inputs] for g in gids}
        sample['targets']={str(t):[hex(w) for w in nodes_by_id[t]] for t in tids}
        sample['budgets']={str(t):info[t][0] for t in tids}
        sample['parents']={str(t):parent[t] for t in tids if t}
    stream=b'CT4482J1'+var(seed)+var(len(info))+var(len(shape))+var(len(pred))+shape+pred+child
    meta={'root':seed,'formalGroup':formal_group,'rawPermutations':perms,
          'nativeRecords':len(raw),'uniquePhysical':len(by),'reachableBFS':len(info),
          'internals':sum(l<0 for _,l,_ in info),'leaves':sum(l>=0 for _,l,_ in info),
          'survivingEdges':sum(len(s) for s in routing),'higherBudgetEdges':dominated,
          'maxDiscoveryDepth':max(discoveryDepth),'discoveryHistogram':sorted(Counter(discoveryDepth).items()),
          'fanoutBands':[(len(part),sum(len(routing[i]) for i in part)) for part in bands],
          'maxFanout':max(hist,default=0),'routingBytes':len(child),'parentMoveBytes':len(pred),
          'shapeBytes':len(shape),'packedBytes':len(stream),'histogram':sorted(hist.items()),
          'sha256':hashlib.sha256(stream).hexdigest()}
    return stream,meta,samples
def main():
    ap=ArgumentParser(description=__doc__);ap.add_argument('graph',type=Path);ap.add_argument('--binary',type=Path)
    ap.add_argument('--sample',type=Path);ap.add_argument('--sample-count',type=int,default=8)
    ap.add_argument('--stratified',action='store_true',help='sample each actual exit-count band: 0, 1-8, 9-24, 25-63, 64+')
    a=ap.parse_args();seed,rows,_=read_graph(a.graph);stream,meta,samples=audit(seed,rows,a.sample_count,a.stratified)
    if a.binary:
        with a.binary.open('xb') as f:f.write(stream)
    if a.sample:
        with a.sample.open('x') as f:json.dump({'meta':meta,'samples':samples},f,separators=(',',':'))
    print('JUNCTION',json.dumps(meta,separators=(',',':')))
if __name__=='__main__':main()
