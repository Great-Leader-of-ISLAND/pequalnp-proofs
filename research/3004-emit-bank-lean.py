"""Turn each terminal bank column into a small independently checkable Lean certificate."""
from pathlib import Path
import argparse
import re
import runpy

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('log',type=Path)
    ap.add_argument('out',type=Path)
    args=ap.parse_args()
    lib=runpy.run_path(str(Path(__file__).with_name('3004-bank-leaf-check.py')))
    found={};wide={}; pending=[]; total=None; observed=0
    lines=args.log.read_text().splitlines()
    if not any(re.search(r'\bREMAIN \d+ \d+ \d+',l) for l in lines):
        # The public workflow preserves exact terminal triples as BANK_LEAF rows in its log.
        summary=next((l for l in lines if re.search(r'\bBANK_COMPILED 7 COMPLETE ',l)),None)
        if summary:
            cases=[m.groups() for l in lines if (m:=re.search(r'\bBANK_LEAF 7 (\d+) (\d+) (\d+)',l))]
            lines=['REMAIN '+' '.join(v) for v in cases]+[summary]
    for line in lines:
        m=re.search(r'\bREMAIN (\d+) (\d+) (\d+)',line)
        if m: pending.append(tuple(map(int,m.groups())))
        m=re.search(r'\bBANK_COMPILED (\d+) (COMPLETE|INCOMPLETE) .*remaining=(\d+)',line)
        if not m: continue
        if m[1]=='7':
            total=int(m[3]);observed+=len(pending)
            for _,p,b in pending:
                reason,data=lib['test'](p,b,7,.25,60000)
                z=p|(b<<21)
                if reason=='eight-forced-lca':
                    wires,((a,bv),(n,p1,p2),(q,n1,n2))=data
                    labels=[i for i,_ in wires]
                    positive=[i for _,(i,_) in wires]
                    negative=[j for _,(_,j) in wires]
                    found[z]='(%d, make %s %s %s %d %d %d %d %d %d %d %d)'%(
                        z,labels,positive,negative,labels.index(a),labels.index(bv),q,n1,n2,p1,p2,n)
                else:
                    rows=lib['ROWS']; ds={rows[i]&~rows[j]:(i,j) for i in lib['ids'](z)
                                                       for j in lib['ids'](lib['FULL']^z)}
                    used=0; pairs=[]
                    for d in sorted(ds,key=lambda x:(lib['count'](x),x)):
                        if not d or d&used:continue
                        pairs.append(ds[d]); used|=d
                        if len(pairs)==9:break
                    if len(pairs)==9:
                        wide[z]='(%d, nine %s %s)'%(z,[i for i,j in pairs],[j for i,j in pairs])
        pending=[]
    if not found and not wide:raise SystemExit('no supported explicit certificates found')
    source='''import PEqualNP.CoBankProof3004

namespace CoBankChecked3004
open CoBankProof3004 CoAO3143Restriction

def cases : List (Nat × Cert) :=
  ['''+',\n   '.join(found.values())+''']

def wideCases : List (Nat × Nine) :=
  ['''+',\n   '.join(wide.values())+''']

theorem checked : cases.all (fun z => decide (Check z.1 z.2)) = true := by decide +kernel

theorem wide_checked : wideCases.all (fun z => decide (CheckNine z.1 z.2)) = true := by decide +kernel

theorem excluded_case {entry : Nat × Cert} (he : entry ∈ cases) {k S}
    (run : Cone (val entry.1) k S) (cap : k ≤ 7)
    (ground : ∀ w ∈ S, ∃ j : R, w=raw j) : False :=
  excluded entry.2 (of_decide_eq_true ((List.all_eq_true.mp checked) entry he)) run cap ground

theorem excluded_wide {entry : Nat × Nine} (he : entry ∈ wideCases) {k S}
    (run : Cone (val entry.1) k S) (cap : k ≤ 7)
    (ground : ∀ w ∈ S, ∃ j : R, w=raw j) : False :=
  nine_excluded entry.2 (of_decide_eq_true ((List.all_eq_true.mp wide_checked) entry he)) run cap ground

end CoBankChecked3004
'''
    args.out.write_text(source)
    print('emitted LCA',len(found),'nine-way',len(wide),'distinct',len(found)+len(wide),
          'observed triples',observed,'declared terminals',total)
