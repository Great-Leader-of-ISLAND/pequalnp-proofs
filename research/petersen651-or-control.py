"""Check edge transitivity and calibrate both shard-1 encodings at 21 gates."""
from itertools import combinations
from pathlib import Path
from functools import reduce
import importlib.util,sys,tempfile
spec=importlib.util.spec_from_file_location('shard',Path(__file__).with_name('petersen651-or-edge.py'))
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
s.check_symmetry();s.K=21;s.BAD=s.N+s.K;s.OMIT=s.BAD+1
vs=next(v for v in combinations(range(s.N),6) if all(a in v or b in v for a,b in s.EDGES)); groups={v:[] for v in vs}
for a,b in s.EDGES:
    c=next(v for v in vs if v in (a,b));groups[c].append(b if a==c else a)
gs=[('or',(0,1))]
def gate(op,a,b):gs.append((op,(a,b)));return s.N+len(gs)-1
def union(xs):return reduce(lambda a,b: gate('or',a,b),xs)
output=union([gate('and',v,union(qs)) for v,qs in groups.items()]);assert len(gs)==21
mapping={i:i for i in range(s.N+1)}; order=gs[:1]; pending=dict(enumerate(gs[1:],s.N+1))
while pending:
    mx,mi,w,op=min((max(mapping[a],mapping[b]),min(mapping[a],mapping[b]),w,op) for w,(op,(a,b)) in pending.items() if a in mapping and b in mapping)
    mapping[w]=s.N+len(order);order.append((op,(mi,mx)));del pending[w]
c={'gates':[dict(op=o,inputs=list(p)) for o,p in order],'output':mapping[output]};assert not s.counterexamples(c,21)
for mode in ('raw','normal'):
    e=s.Encoding(mode)
    for rec,(op,(a,b)) in zip(e.gs,order[1:]):
        ops,ls,rs,left,right=rec;e.add(ops[('and','or','not').index(op)]);e.add(left[ls.index(a)]);e.add(right[rs.index(b)])
    e.add(e.osel[e.outs.index(c['output'])]);
    for x in s.seed_rows('frontier'):e.add_row(x)
    with tempfile.TemporaryDirectory() as d:
        cnf=Path(d)/'control.cnf';e.dimacs(cnf);v,m=s.run_cadical(sys.argv[1],cnf,Path(d)/'unused',35,False);assert v=='SAT' and e.decode(m)==c
    print('PASS',mode,'21-gate pinned first OR control, replayed all 1024 inputs',flush=True)
print('PASS first OR orbit includes all 15 edges under 120 graph automorphisms')
