"""Render a bounded actual internal frontier-and-genuine-transport kernel benchmark."""
import argparse,json,re
from pathlib import Path
from runpy import run_path
D=Path(__file__).parent
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('sample',type=Path);p.add_argument('out',type=Path)
    p.add_argument('--start',type=int,default=0);p.add_argument('--count',type=int,default=4)
    p.add_argument('--private',action='store_true',help='reuse each wire\'s 258-row exclusivity mask')
    p.add_argument('--discovery',action='store_true',help='match new destinations to their source/action/permutation')
    a=p.parse_args()
    if a.discovery:a.private=True
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
    mod='CoJunctionPrivateCost4482' if a.private else 'CoJunctionCost4482'
    out=['import PEqualNP.'+mod,f'namespace {a.out.stem}','open CoJunctionCost4482',
         'set_option maxRecDepth 200000','set_option maxHeartbeats 0']
    for w,i in wordids.items():out.append(f'def w{i} : W := {hex(w)}')
    edges=0
    for n in nodes:
        ni=n['id'];ws=[int(w,16) for w in n['words']]
        got=[x for x,_ in bank['moves'](ws,n['budget'])]
        if got!=[x[0] for x in n['routes']]:raise ValueError('sample does not match independent move enumeration')
        pins=[]
        for i,w in enumerate(ws):
            h,l,z=mark(w);pin=f'(w{wordids[w]},({hex(h)},{hex(l)}))'
            if a.private:
                u=bank['TOP']
                for j,other in enumerate(ws):
                    if i!=j:u&=~mark(other)[2]
                pin=f'({pin},{hex(u)})'
            pins.append(pin)
        tp='CoJunctionPrivateCost4482.Annotated' if a.private else 'Pin'
        out.append(f'def p{ni} : List {tp} := ['+','.join(pins)+']')
        for typ,table in [('v',n['images']),('t',n['targets'])]:
            out.append(f'def {typ}{ni} : Nat → List W')
            for key,vec in table.items():out.append(f'  | {key} => ['+','.join(f'w{wordids[int(w,16)]}' for w in vec)+']')
            out.append('  | _ => []')
        out.append(f'def r{ni} : List (Nat×Nat×Nat) := ['+','.join(f'({c},{t},{g})' for c,t,g in n['routes'])+']')
        check=f'routes v{ni} t{ni}'
        if a.discovery:
            if 'parents' not in n:raise ValueError('refresh the sample with the current junction auditor')
            out.append(f'def parent{ni} : Nat → Option (Nat×Nat×Nat)')
            for key,(i,c,g) in n['parents'].items():out.append(f'  | {key} => some ({i},{c},{g})')
            out.append('  | _ => none')
            check=f'CoJunctionPrivateCost4482.compactRoutes v{ni} t{ni} parent{ni} {ni}'
        out.append(f'theorem verify{ni} : {check} ({mod}.choices p{ni} {n["budget"]}) r{ni} = true := by decide +kernel')
        out.append(f'#print axioms verify{ni}');edges+=len(n['routes'])
    out+=['end '+a.out.stem,''];s='\n'.join(out)
    with a.out.open('x') as f:f.write(s)
    print(f'JUNCTION_KERNEL_INPUT nodes={len(nodes)} survivingBranches={edges} utf8={len(s.encode())}')
if __name__=='__main__':main()
