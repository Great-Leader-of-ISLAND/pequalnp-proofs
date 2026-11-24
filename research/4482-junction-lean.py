"""Render a bounded actual internal frontier-and-genuine-transport kernel benchmark."""
import argparse,json,re
from pathlib import Path
from runpy import run_path
D=Path(__file__).parent
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('sample',type=Path);p.add_argument('out',type=Path)
    p.add_argument('--start',type=int,default=0);p.add_argument('--count',type=int,default=4)
    a=p.parse_args()
    if a.out.exists() or a.out.suffix!='.lean' or not re.fullmatch('[A-Z][A-Za-z0-9_]*',a.out.stem):p.error('use a fresh Lean module path')
    doc=json.loads(a.sample.read_text());nodes=doc['samples'][a.start:a.start+a.count]
    if len(nodes)!=a.count or not nodes:p.error('missing node range')
    bank=run_path(str(D/'4482-junction-audit.py'));mark=bank['mark']
    words=set()
    for n in nodes:
        for s in n['images'].values():words.update(int(w,16) for w in s)
        for s in n['targets'].values():words.update(int(w,16) for w in s)
        words.update(int(w,16) for w in n['words'])
    wordids={w:i for i,w in enumerate(sorted(words))}
    out=['import PEqualNP.CoJunctionCost4482',f'namespace {a.out.stem}','open CoJunctionCost4482',
         'set_option maxRecDepth 200000','set_option maxHeartbeats 0']
    for w,i in wordids.items():out.append(f'def w{i} : W := {hex(w)}')
    edges=0
    for n in nodes:
        ni=n['id'];ws=[int(w,16) for w in n['words']]
        got=[x for x,_ in bank['moves'](ws,n['budget'])]
        if got!=[x[0] for x in n['routes']]:raise ValueError('sample does not match independent move enumeration')
        pins=[]
        for w in ws:
            h,l,z=mark(w);pins.append(f'(w{wordids[w]},({hex(h)},{hex(l)}))')
        out.append(f'def p{ni} : List Pin := ['+','.join(pins)+']')
        for typ,table in [('v',n['images']),('t',n['targets'])]:
            out.append(f'def {typ}{ni} : Nat → List W')
            for key,vec in table.items():out.append(f'  | {key} => ['+','.join(f'w{wordids[int(w,16)]}' for w in vec)+']')
            out.append('  | _ => []')
        out.append(f'def r{ni} : List (Nat×Nat×Nat) := ['+','.join(f'({c},{t},{g})' for c,t,g in n['routes'])+']')
        out.append(f'theorem verify{ni} : routes v{ni} t{ni} (choices p{ni} {n["budget"]}) r{ni} = true := by decide +kernel')
        out.append(f'#print axioms verify{ni}');edges+=len(n['routes'])
    out+=['end '+a.out.stem,''];s='\n'.join(out)
    with a.out.open('x') as f:f.write(s)
    print(f'JUNCTION_KERNEL_INPUT nodes={len(nodes)} survivingBranches={edges} utf8={len(s.encode())}')
if __name__=='__main__':main()
