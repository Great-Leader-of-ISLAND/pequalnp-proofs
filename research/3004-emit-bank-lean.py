"""Emit finite Lean row certificates for the fully forced seven-gate bank cases in one run."""
from pathlib import Path
import ast
import argparse
import re
import runpy

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('log',type=Path)
    ap.add_argument('out',type=Path)
    args=ap.parse_args()
    lib=runpy.run_path(str(Path(__file__).with_name('3004-bank-leaf-check.py')))
    found={}; pending=[]; total=None
    for line in args.log.read_text().splitlines():
        m=re.search(r'\bREMAIN (\d+) (\d+) (\d+)',line)
        if m: pending.append(tuple(map(int,m.groups())))
        m=re.search(r'\bBANK_COMPILED (\d+) (COMPLETE|INCOMPLETE) .*remaining=(\d+)',line)
        if not m: continue
        if m[1]=='7':
            total=int(m[3])
            for _,p,b in pending:
                reason,data=lib['test'](p,b,7,.25,60000)
                if reason!='eight-forced-lca':continue
                wires,((a,bv),(n,p1,p2),(q,n1,n2))=data
                labels=[i for i,_ in wires]
                positive=[i for _,(i,_) in wires]
                negative=[j for _,(_,j) in wires]
                z=p|(b<<21)
                found[z]='(%d, make %s %s %s %d %d %d %d %d %d %d %d)'%(
                    z,labels,positive,negative,labels.index(a),labels.index(bv),q,n1,n2,p1,p2,n)
        pending=[]
    if not found:raise SystemExit('no supported explicit certificates found')
    source='''import PEqualNP.CoBankProof3004

namespace CoBankChecked3004
open CoBankProof3004 CoAO3143Restriction

def cases : List (Nat × Cert) :=
  ['''+',\n   '.join(found.values())+''']

theorem checked : cases.all (fun z => decide (Check z.1 z.2)) = true := by decide +kernel

theorem excluded_case {entry : Nat × Cert} (he : entry ∈ cases) {k S}
    (run : Cone (val entry.1) k S) (cap : k ≤ 7)
    (ground : ∀ w ∈ S, ∃ j : R, w=raw j) : False :=
  excluded entry.2 (of_decide_eq_true ((List.all_eq_true.mp checked) entry he)) run cap ground

end CoBankChecked3004
'''
    args.out.write_text(source)
    print('emitted distinct finite witnesses',len(found),'original complete-run terminals',total)
