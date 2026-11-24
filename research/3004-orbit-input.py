"""Emit ordinary-variable orbits and permitted bank row families for the compiled verifier."""
from pathlib import Path
import runpy,sys
d=runpy.run_path(str(Path(__file__).with_name('3004-negative-orbits.py')))
k=int(sys.argv[1]);E,N=d['E'],d['N'];print(k,*E,*N)
for R,m,es,ns in d['O']['masks']():
    if d['size'](R)>25-k:continue
    em=sum(1<<j for j in es);nm=sum(1<<j for j in ns)
    # A fixed negative family is exact, its orbit only uses automorphisms fixing R.
    for a in d['possible'](R,nm,25-k):print(R,em,a)
