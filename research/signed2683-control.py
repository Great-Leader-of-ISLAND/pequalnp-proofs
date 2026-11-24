"""Study the exact fourteen-binary-gate residual of L-meta-2683, S empty."""
import argparse
from pathlib import Path
import json
import petersen670 as ref

def cofactor_frontier():
    rows = set()
    for row in range(512):
        want = ref.target(row)
        # The signed source is x0. Both cofactors are positive in x1 through x8.
        if all(ref.target(row ^ (1 << i)) != want for i in range(1,9) if bool(row & (1 << i)) == want):
            rows.add(row)
    for row in range(512):
        assert any(((r ^ row) & 1) == 0 and ref.target(r) == ref.target(row) and
                   ((r & row == r) if ref.target(row) else (r & row == row)) for r in rows)
    return sorted(rows)

def select_control():
    c = ref.cover_control()
    plus = lambda a: a + int(a >= 9)
    gs = [('not',(0,))] + [(g['op'], tuple(plus(a) for a in g['inputs'])) for g in c['gates']]
    true_idx = 9+len(gs)
    gs += [('or',(0,9)), ('and',(plus(c['output']),true_idx))]
    mapped={i:i for i in range(9)}
    remain=set(range(len(gs))); out=[]
    while remain:
        ready = [(tuple(sorted((mapped[i] for i in gs[j][1]),reverse=True)),j) for j in remain if all(p in mapped for p in gs[j][1])]
        _,j=min(ready)
        mapped[9+j]=9+len(out)
        out.append({'op':gs[j][0],'inputs':sorted(mapped[i] for i in gs[j][1])})
        remain.remove(j)
    return {'gates':out,'output':mapped[9+len(gs)-1]}

def build(bound):
    m=ref.Encoding('normal',bound=bound,symmetry=False)
    ops,ls,rs,left,right=m.gs[0]
    m.add(ops[2]);m.add(left[ls.index(0)])
    for dummy in m.dummies: m.add(-dummy)
    for ops,*_ in m.gs[1:]: m.add(-ops[2])
    for row in cofactor_frontier(): m.add_row(row)
    return m

def run(solver,checker,d):
    d.mkdir(exist_ok=False)
    ctrl=select_control()
    assert not ref.counterexamples(ctrl,len(ctrl['gates']))
    for pinned in (True,False):
        bound=len(ctrl['gates']) if pinned else 15
        model=build(bound)
        if pinned:
            for (ops,ls,rs,left,right),g in zip(model.gs,ctrl['gates']):
                a,*extra=g['inputs']; b=extra[0] if extra else model.omit
                model.add(ops[('and','or','not').index(g['op'])]);model.add(left[ls.index(a)]);model.add(right[rs.index(b)])
        cnf=d/('positive.cnf' if pinned else 'residual.cnf');proof=d/'proof.drat';model.dimacs(cnf)
        print('positive' if pinned else 'residual','physical gates',bound,'frontier',len(model.rows),'vars',model.top,'clauses',len(model.clauses),flush=True)
        status,values=ref.run_cadical(solver,cnf,proof,25 if pinned else 240,False)
        if pinned: assert status=='SAT'
        print(status,flush=True)
        if status=='SAT':
            candidate=model.decode(values)
            assert not ref.counterexamples(candidate,bound)
            print('all 512 rows passed',json.dumps(candidate),flush=True)
        if status=='UNSAT':
            status,_=ref.run_cadical(solver,cnf,proof,150,True)
            ok=status=='UNSAT' and ref.verify_proof(checker,cnf,proof,90,d/'drat.log')
            print('DRAT verified',ok)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('solver');p.add_argument('checker');p.add_argument('folder',type=Path)
    a=p.parse_args();run(a.solver,a.checker,a.folder)
