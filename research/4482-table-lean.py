"""Render contiguous authentic tight-state records for single-process Lean timing."""
import argparse
import gzip
import re
from pathlib import Path
from functools import lru_cache
from itertools import combinations
from runpy import run_path

BASE=Path(__file__).parent

def load_table(path, expected_complete=True):
    opener=gzip.open if path.suffix=='.gz' else open
    words=[]; states=[]; head=None; end=None
    with opener(path,'rt') as stream:
        for line in stream:
            tag,*v=line.split()
            if tag=='H':
                if head or len(v)!=3:raise ValueError('duplicate or invalid header')
                head=tuple(map(int,v))
            elif tag=='W':
                ident=int(v[0]);w=int(v[1],16)
                if len(v)!=2 or ident!=len(words) or not 0<=w<1<<512:raise ValueError('invalid word record')
                words.append(w)
            elif tag=='S':
                n,core,steps,*idx=map(int,v)
                if not 7<=n<=11 or len(idx)!=n or min(idx)<0 or max(idx)>=len(words):raise ValueError('bad state indices')
                ws=tuple(words[z] for z in idx)
                if list(ws)!=sorted(set(ws)):raise ValueError('state truth words are not strictly sorted')
                if core!=-1 and (not 0<=core<1<<n or bin(core).count("1")!=7 or steps<=0):raise ValueError('bad anchor')
                states.append((ws,core,steps))
            elif tag=='E':
                if end or len(v)!=5:raise ValueError('invalid trailer')
                end=tuple(map(int,v))
            else:raise ValueError('unknown table line')
    if head not in ((1,0,258),(1,1,258)) or end is None:raise ValueError('missing expected header/trailer')
    if (len(states),len(words),sum(c>=0 for _,c,_ in states),sum(c<0 for _,c,_ in states),
        max((r for _,_,r in states),default=0))!=end:raise ValueError('trailer counts disagree')
    if expected_complete and len(states)!=(2713,9445)[head[1]]:raise ValueError('incomplete official root table')
    if len(set(ws for ws,_,_ in states))!=len(states):raise ValueError('duplicate canonical states')
    return head[1],states

@lru_cache(None)
def geometry(n):
    return [sum(((B>>i)&1)<<B for B in range(1<<n)) for i in range(n)]

@lru_cache(None)
def target(n,anchor):
    return sum(1<<B for B in range(1<<n) if bin(B).count("1")<=n-5 and bin(B&anchor).count("1")>=2)

def render(seed,states,offset,module,group,link,rows):
    imports=['import PEqualNP.CoImplicitBlock4482']
    if link:imports.append('import PEqualNP.CoPortEdgeRows4482')
    out=imports+[f'namespace {module}','open CoBitBlock4482 CoBlockIntervals4482 CoImplicitBlock4482',
        'set_option maxHeartbeats 0','set_option maxRecDepth 200000']
    words=sorted({w for ws,_,_ in states for w in ws})
    ids={w:i for i,w in enumerate(words)}
    for i,w in enumerate(words):
        p=sum(((w>>hi)&1)<<j for j,(lo,hi) in enumerate(rows))
        q=sum(((w>>lo)&1)<<j for j,(lo,hi) in enumerate(rows))
        out.append(f'def w{i} : Mark := ({hex(p)},{hex(q)})')
        if link:
            out.append(f'theorem w{i}_physical : CoPortEdgeRows4482.mark (0x{w:x}:BitVec 512) = w{i} := by decide +kernel')
    for n in sorted({len(ws) for ws,_,_ in states}):
        for i,mask in enumerate(geometry(n)):
            out.append(f'def g{n}_{i} : BitVec {1<<n} := {hex(mask)}')
    for n,c in sorted({(len(ws),c) for ws,c,_ in states}):
        out.append(f'def m{n}_{c} : BitVec {1<<n} := {hex(target(n,c))}')
    labels=[]
    for i,(ws,core,steps) in enumerate(states,offset):
        n=len(ws);lab=f's{seed}_{i}';labels.append(lab)
        cols=','.join(f'⟨w{ids[w]}, g{n}_{j}⟩' for j,w in enumerate(ws))
        out.append(f'def {lab} : Bool := check ([{cols}] : List (Col {1<<n})) {steps} m{n}_{core}')
    for ix in range(0,len(labels),group):
        here=labels[ix:ix+group];fn=f'verified_{seed}_{offset+ix}'
        expr=here[0] if len(here)==1 else '['+','.join(here)+'].all id'
        out+=[f'theorem {fn} : {expr} = true := by decide +kernel',f'#print axioms {fn}']
    out+=[f'end {module}','']
    return '\n'.join(out)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path)
    ap.add_argument('out',type=Path,help='one new .lean file')
    ap.add_argument('--start',type=int,default=0)
    ap.add_argument('--count',type=int,default=8)
    ap.add_argument('--group',type=int,default=1,help='checks per kernel theorem')
    ap.add_argument('--link-physical',action='store_true',help='also kernel-check each distinct full-word projection')
    a=ap.parse_args()
    if a.out.exists():ap.error('output exists; choose a fresh filename')
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*',a.out.stem) or a.out.suffix!='.lean':ap.error('invalid Lean module filename')
    seed,states=load_table(a.table)
    if not(0<=a.start<len(states) and 1<=a.count<=len(states)-a.start and a.group>=1):ap.error('invalid chunk')
    portion=states[a.start:a.start+a.count]
    if any(q<0 for _,q,_ in portion):ap.error('selected chunk includes a genuine missing anchor')
    F=run_path(str(BASE/'4482-one-port.py'))['F']
    rows=[(z,z|1<<b) for z in range(512) if not F[z] for b in range(9) if not(z>>b&1) and F[z|1<<b]]
    if len(rows)!=258:raise ValueError('wrong graph row count')
    source=render(seed,portion,a.start,a.out.stem,a.group,a.link_physical,rows)
    with a.out.open('x',encoding='utf-8') as f:f.write(source)
    print(f'root={seed} first={a.start} count={len(portion)} group={a.group} '
          f'rounds={sum(s for _,_,s in portion)} utf8={len(source.encode())} file={a.out.name}')

if __name__=='__main__':main()
