"""Read the complete stdout from Lean's #print axioms; reject any additional dependency."""
import argparse,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('output',type=Path);p.add_argument('theorem');a=p.parse_args()
s=a.output.read_text();m=re.search(r"'"+re.escape(a.theorem)+r"' depends on axioms:\s*\[([^\]]*)\]",s,re.S)
if not m:raise SystemExit('axiom-list record missing for '+a.theorem)
actual={x.strip() for x in m[1].split(',') if x.strip()};allowed={'propext','Classical.choice','Quot.sound'}
if not actual<=allowed:raise SystemExit('extra axioms: '+', '.join(sorted(actual-allowed)))
print('complete axiom allowlist passed:',a.theorem,', '.join(sorted(actual)))
