"""Render actual node benchmarks against the physical sequential-route verifier."""
import argparse,json,re
from pathlib import Path
from runpy import run_path
D=Path(__file__).parent
def vec(data):return '['+','.join(map(str,data))+']'
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('sample',type=Path);p.add_argument('out',type=Path)
    p.add_argument('--start',type=int,default=0);p.add_argument('--count',type=int,default=1)
    a=p.parse_args();doc=json.loads(a.sample.read_text());ns=doc['samples'][a.start:a.start+a.count];stem=a.out.stem
    if len(ns)!=a.count or a.count<1 or a.out.exists() or not re.fullmatch('[A-Z][A-Za-z0-9_]*',stem):p.error('invalid range or output')
    libs=run_path(str(D/'4482-junction-audit.py'));ref=libs['moves'];mark=libs['mark']
    fast=run_path(str(D/'4482-junction-unique.py'))['choices'];perm=doc['meta']['formalGroup']
    words=set()
    for n in ns:
        for ws in [n['words'],*n['images'].values(),*n['targets'].values()]:words.update(int(x,16) for x in ws)
    names={w:f'w{i}' for i,w in enumerate(sorted(words))}
    out=['import PEqualNP.CoJunctionStream4482','namespace '+stem,
         'open CoPortRoots4482 CoPortFrontier4482 CoBitBlock4482 CoJunctionLogical4482 CoJunctionStream4482',
         'set_option maxRecDepth 200000','set_option maxHeartbeats 0']
    out += [f'def {n} : W := {hex(w)}' for w,n in names.items()]
    edges=0
    for n in ns:
        i=n['id'];k=n['budget'];xs=[int(x,16) for x in n['words']]
        expected=[q for q,_ in ref(xs,k)];steps=[x[0] for x in n['routes']]
        if expected!=steps or list(fast(xs,k))!=expected:raise ValueError('an actual move was lost or gained')
        uds=[];pins=[];edges+=len(steps)
        for q,w in enumerate(xs):
            pos,neg,_=mark(w);u=libs['TOP']
            for j,v in enumerate(xs):
                if j!=q:u &= ~mark(v)[2]
            pins.append(f'({names[w]},({hex(pos)},{hex(neg)}))');uds.append(hex(u))
        out += [f'def source{i} : Record := ⟨{vec(pins)},{k}⟩',f'def index{i} (w : W) := (stateWords source{i}).idxOf w',
                f'def masks{i} : List Bits := {vec(uds)}',f'def mask{i} (w : W) := masks{i}.getD (index{i} w) 0',
                f'def views{i} : Nat → List W']
        for g,ws in n['images'].items():
            out.append(f'  | {perm[int(g)]} => '+vec(names[int(w,16)] for w in ws))
        out += ['  | _ => []',f'def f{i} (g : G) (w : W) := (views{i} g.val).getD (index{i} w) 0',
                f'def banks{i} : Nat → List W']
        for t,ws in n['targets'].items():out.append(f'  | {t} => '+vec(names[int(w,16)] for w in ws))
        out+=['  | _ => []',f'def limits{i} : Nat → Nat']
        for t in n['targets']:
            out.append(f'  | {t} => {n.get("budgets",{}).get(t,k-1)}')
        out+=['  | _ => 0',f'def tab{i} (t : Nat) : Record := '
              f'⟨(banks{i} t).map (fun w => (w,CoPortEdgeRows4482.mark w)),limits{i} t⟩',
              f'def arcs{i} : List (Nat×G) := '+vec(f'({t},{perm[g]})' for _,t,g in n['routes']),
              f'theorem proof{i} : stream tab{i} source{i} f{i} (runs source{i} {len(xs)} mask{i}) arcs{i} = true := by decide +kernel',
              f'#print axioms proof{i}']
    out += ['end '+stem,''];s='\n'.join(out)
    with a.out.open('x') as f:f.write(s)
    print(f'PHYSICAL_STREAM_INPUT nodes={len(ns)} realBranches={edges} utf8={len(s.encode())}')
if __name__=='__main__':main()
