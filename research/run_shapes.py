"""Sequential, bounded search for the actual one-star subclass of shard 13."""
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import time

base = Path(__file__).resolve().parent
F = runpy.run_path(str(base/'graph1343-shard13-formula.py'))
solver, checker = sys.argv[1:]
counts = (18,16,17,15,16,17,17,17,19,19,19)
t0 = time.monotonic()
shapes = F['shapes'](9)
cnf = F['cnf']

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for part in iter(lambda:stream.read(1024*1024),b''):
            h.update(part)
    return h.hexdigest()

def replay(tree, rows, model, select, arity=11):
    # The generator allocates the leaf's selectors, then one new variable per row.
    # Recursing through the real tree independently rebuilds the formula mask.
    iterator = iter([x for x in select])
    rowset = (1 << len(rows))-1
    def walk(t):
        op,kids = t
        if op=='leaf':
            mask = next(iterator)
            return sum(1<<i for i,r in enumerate(rows) if mask&r)
        child = [walk(k) for k in kids]
        acc = 0 if op=='or' else rowset
        for bits in child:
            acc = (acc|bits) if op=='or' else (acc&bits)
        return acc
    return walk(tree)

with tempfile.TemporaryDirectory() as temp:
    d = Path(temp)
    for center in (9,8,10,0,2,5,6,7,1,4,3):
        eligible = [s for s in shapes if F['has_cherry'](s) and F['clause_count'](s)>=counts[center]]
        stats = {'verified_unsat':0,'sat':0,'unknown':0}
        for num,tree in enumerate(eligible):
            if time.monotonic()-t0 > 1600:
                print('Bounded run unfinished; overall UNKNOWN',flush=True)
                sys.exit(0)
            n,clauses=cnf(center,tree)
            inp,proof,out=d/'shape.cnf',d/'shape.drat',d/'model'
            with inp.open('w') as ff:
                print('p cnf',n,len(clauses),file=ff)
                for clause in clauses: print(*clause,0,file=ff)
            with out.open('w') as ff:
                proc=subprocess.run([solver,'-q','-t','6',str(inp),str(proof)],stdout=ff,timeout=20)
            text=out.read_text()
            if proc.returncode==20 and 's UNSATISFIABLE' in text.splitlines():
                with (d/'check').open('w') as log:
                    try:
                        res=subprocess.run([checker,str(inp),str(proof)],stdout=log,stderr=subprocess.STDOUT,timeout=20)
                    except subprocess.TimeoutExpired:
                        stats['unknown']+=1
                        continue
                if res.returncode or 's VERIFIED' not in (d/'check').read_text().splitlines(): raise ValueError('Unverified certificate')
                print('verified',center,num,digest(inp),digest(proof),flush=True)
                stats['verified_unsat']+=1
            elif proc.returncode==10 and 's SATISFIABLE' in text.splitlines():
                truth={int(v) for l in text.splitlines() if l.startswith('v ') for v in l.split()[1:] if int(v)>0}
                edges = F['EDGES']; neg = F['MIS']
                positives=[(1<<a)|(1<<b) for a,b in edges if center not in (a,b)]
                critical=positives+neg
                masks=[]; nextvar=[1]
                def extract(t):
                    op,kids=t
                    if op=='leaf':
                        masks.append(sum(1<<u for u in range(11) if nextvar[0]+u in truth))
                        nextvar[0]+=11
                    else:
                        for kid in kids:extract(kid)
                    nextvar[0]+=len(critical)
                extract(tree)
                assert nextvar[0]==n+1 and len(masks)==9
                assert replay(tree,critical,truth,masks)==(1<<len(positives))-1
                allrows=[r for r in range(1<<11) if not r&(1<<center)]
                expected=sum(1<<i for i,r in enumerate(allrows) if any(r&m==m for m in positives))
                assert replay(tree,allrows,truth,masks)==expected
                print('relaxed SAT; replayed 1024 rows',center,num,json.dumps(masks),flush=True)
                stats['sat']+=1
                break
            elif proc.returncode in (0,124) and ('s UNKNOWN' in text or 's INDETERMINATE' in text):
                stats['unknown']+=1
            else: raise RuntimeError((proc.returncode,text[:100]))
        print('SUMMARY',center,len(eligible),stats,flush=True)
