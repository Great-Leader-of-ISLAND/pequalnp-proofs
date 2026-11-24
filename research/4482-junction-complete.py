"""Generate whole physical root certificates, or bounded debugging slices of that exact verifier."""
from argparse import ArgumentParser
from pathlib import Path
from runpy import run_path
import re
D=Path(__file__).parent
a=ArgumentParser(description=__doc__);a.add_argument('table',type=Path);a.add_argument('archive',type=Path)
a.add_argument('archive_module');a.add_argument('out',type=Path)
a.add_argument('--start',type=int,default=0);a.add_argument('--count',type=int)
a.add_argument('--chunk',type=int,default=32)
a.add_argument('--first-leaf',action='store_true',help='check the first real tight leaf as a one-row probe')
arg=a.parse_args()
if not all(re.fullmatch('[A-Z][A-Za-z0-9_]*',t) for t in (arg.archive_module,arg.out.stem)) or arg.out.exists():a.error('fresh Lean output and valid modules required')
lib=run_path(str(D/'4482-junction-fixed.py'));sp=run_path(str(D/'4482-share-table.py'))
seed,n,ids,edgeBits,par,inn,cols,banks=lib['cgraph'](arg.archive.read_bytes())
s,states=sp['reader'](arg.table)
if seed!=s or not states:raise ValueError('different rooted graphs')
hints=[];maxw=0
for ws,anchors,fuel in states:
    if not 0<=fuel<64 or not 0<=anchors<1<<len(ws) or bin(anchors).count('1')!=7:raise ValueError('invalid leaf hint')
    hints.append(anchors*64+fuel);maxw=max(maxw,len(ws))
for x in cols['rows'][1]:
    if x//8 and x//8-1>=len(hints):raise ValueError('missing actual tight leaf')
lo=arg.start;hi=n if arg.count is None else lo+arg.count
if arg.first_leaf:
    lo=next(i for i,x in enumerate(cols['rows'][1]) if x//8);hi=lo+1
if not 0<=lo<hi<=n or arg.chunk<1:a.error('invalid subrange')
full=lo==0 and hi==n
w=6+maxw;blocks=lib['packcol'](hints,w);shade=('false','true')[seed]
out=['import PEqualNP.CoJunctionComplete4482','import PEqualNP.'+arg.archive_module,
     'namespace '+arg.out.stem,'open CoJunctionComplete4482 CoJunctionFixed4482 CoPortRoots4482',
     'set_option maxRecDepth 200000','set_option maxHeartbeats 0',
     'abbrev gr := '+arg.archive_module+'.graph','private instance : NeZero gr.size := ⟨by decide +kernel⟩',
     f'def hints : Column := ⟨{w},#['+','.join(map(hex,blocks))+']⟩',
     f'def test := rowCheck gr hints {shade} 7']
active=[]
for start in range(lo,hi,arg.chunk):
    stop=min(hi,start+arg.chunk);name=f'b{start}_{stop}'
    out.append(f'theorem {name} : Holds test {start} {stop} := '
               f'slice_sound (a:={start}) (k:={stop-start}) (by decide +kernel)')
    active.append((start,stop,name))
while len(active)>1:
    nxt=[]
    for i in range(0,len(active),2):
        if i+1==len(active):nxt.append(active[i]);continue
        l,mid,left=active[i];mid2,r,right=active[i+1]
        if mid!=mid2:raise ValueError('gap in proof')
        name=f'u{l}_{r}';out.append(f'theorem {name} : Holds test {l} {r} := join_blocks {left} {right}')
        nxt.append((l,r,name))
    active=nxt
if full:
    source='init' if seed else 'raws'
    out+=[f'def result : CoJunctionTarget4482.Certificate (Fin gr.size) {source}.toFinset :=',
          f'  certified (hints:=hints) (seeded:={shade}) (depth:=7) (by decide +kernel) (all_rows {active[0][2]})',
          '#print axioms result']
else:out+=['#print axioms '+active[0][2]]
out+=['end '+arg.out.stem,''];text='\n'.join(out)
with arg.out.open('x') as f:f.write(text)
print(f'PHYSICAL_COMPLETE_SOURCE root={seed} range=[{lo},{hi}) graphNodes={n} '
      f'complete={full} chunk={arg.chunk} hints={len(hints)} utf8={len(text.encode())}')
