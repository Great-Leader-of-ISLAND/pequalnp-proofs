"""Generate ordinary closed Lean bucket theorems for a bounded root range."""
from pathlib import Path
import argparse
p=argparse.ArgumentParser();p.add_argument('first',type=int);p.add_argument('last',type=int)
p.add_argument('--chunk',type=int,default=16);p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
s=['import Bench','open CoNatBench','set_option maxHeartbeats 0','set_option maxRecDepth 4000']
for i in range(a.first,a.last):
    for j in range(0,448,a.chunk):
        s.append(f'theorem t{i}_{j} : casesBlock {i} {j} {min(a.chunk,448-j)} = true := by decide +kernel')
a.output.write_text('\n'.join(s)+'\n')
