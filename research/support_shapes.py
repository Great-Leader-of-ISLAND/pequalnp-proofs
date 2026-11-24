"""One sequential solver, concrete boundary trees, relaxed prefix union cost."""
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import time
from support_slp import UnionCircuit, controls

base=Path(__file__).resolve().parent
F=runpy.run_path(str(base/'formula_domains.py'))
solver, checker=sys.argv[1:]
controls(solver)
counts=(18,16,17,15,16,17,17,17,19,19,19)
schedule=json.loads((base/'tree-prior.json').read_text())
start=time.monotonic()
shapes = F['shapes'](9)
with tempfile.TemporaryDirectory() as wd:
    d=Path(wd)
    for center,idx,kind in schedule:
        if time.monotonic()-start > 1200:
            print('Time budget reached; other shapes still open',flush=True)
            break
        eligible=[s for s in shapes if F['has_cherry'](s) and F['clause_count'](s)>=counts[center]]
        leaves=[]
        n,cs=F['cnf'](center,eligible[idx],'original',leaves)
        union=UnionCircuit(n,cs)
        n,cs=union.attach([[v for label,v in leaf] for leaf in leaves])
        cnf,drat,model=d/'one.cnf',d/'one.drat',d/'one.model'
        with cnf.open('w') as out:
            print('p cnf',n,len(cs),file=out)
            for clause in cs:print(*clause,0,file=out)
        with model.open('w') as out:
            proc=subprocess.run([solver,'-q','-t','9',str(cnf),str(drat)],stdout=out,timeout=20)
        lines=model.read_text().splitlines()
        if proc.returncode==10 and 's SATISFIABLE' in lines:
            truth={int(v) for l in lines if l.startswith('v ') for v in l.split()[1:] if int(v)>0}
            assert all(any((z in truth) if z>0 else (-z not in truth) for z in clause) for clause in cs)
            print('relaxed support-budget SAT',center,idx,
                  [sum(1<<label for label,var in leaf if var in truth) for leaf in leaves],flush=True)
        elif proc.returncode==20 and 's UNSATISFIABLE' in lines:
            with (d/'verify').open('w') as log:
                try:
                    res=subprocess.run([checker,str(cnf),str(drat)],stdout=log,stderr=subprocess.STDOUT,timeout=20)
                except subprocess.TimeoutExpired:
                    print('checker timeout',center,idx,flush=True)
                    continue
            assert res.returncode==0 and 's VERIFIED' in (d/'verify').read_text().splitlines()
            print('support-budget VERIFIED',center,idx,hashlib.sha256(cnf.read_bytes()).hexdigest(),flush=True)
        elif proc.returncode in (0,124) and any(x in lines for x in ('s UNKNOWN','s INDETERMINATE')):
            print('UNKNOWN',center,idx,flush=True)
        else: raise ValueError((proc.returncode,lines[:3]))
