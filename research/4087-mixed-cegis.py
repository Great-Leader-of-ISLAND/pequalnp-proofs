"""Bounded SAT repair of the public L-meta-4087 mixed 18-gate near miss.

Python stdlib plus the Lean toolchain's CaDiCaL, a system SAT binary, or PySAT.
The self-test never runs a SAT solver. Output and resumable state use a separate directory.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
DEFAULT = HERE / "4087-mixed-near-18.json"
D = (0, 1, 3, 9)
FIRST = (0, 1, 2, 5, 6, 7, 8, 9, 10)
NORMAL = FIRST + (3, 4, 11, 12, 13, 14, 15, 16, 17)
SWAP = FIRST + (11, 12, 13, 3, 4, 15, 14, 16, 17)
# Names below refer to the archived gate numbers, even in a new schedule.
WINDOWS = [
    (NORMAL, (3, 4, 11, 12, 13, 14, 17)),
    (SWAP,   (3, 4, 11, 12, 13, 15, 16)),
    (NORMAL, (3, 4, 12, 13, 14, 15, 17)),
    (SWAP,   (4, 12, 13, 14, 15, 16, 17)),
    (NORMAL, (3, 4, 9, 10, 11, 12, 13)),
    (SWAP,   (1, 2, 3, 4, 11, 12, 13)),
]


def atomic(path, data):
    with tempfile.NamedTemporaryFile('w', dir=path.parent, delete=False) as f:
        json.dump(data, f, separators=(',', ':'))
        f.write('\n')
    os.replace(f.name, path)


def pop(x):
    return bin(x).count('1')


class Problem:
    def __init__(self, seed):
        self.seed = seed
        self.pin = set(range(26))
        self.ports = []
        for t, ((side, c), r) in enumerate(zip(seed['centers'], seed['rot'])):
            scale = (1, 3, 9)[r]
            at = 26 + max(0, 5*t-1)
            quad = [((c + scale*d) % 13) if side else (13 + (c - scale*d) % 13) for d in D]
            self.ports.append((at, quad))
            self.pin.update((at, at+1, at+2))
        assert len(seed['centers']) == len(seed['rot']) == 9 and len(self.pin) == 53
        self.lines = [sum(1 << ((l+d) % 13) for d in D) for l in range(13)]
        pencils = [sum(1 << l for l, m in enumerate(self.lines) if m >> p & 1) for p in range(13)]
        arcy = [all(pop(y&m) <= 2 for m in pencils) for y in range(8192)]
        self.pos = [(1 << p, 1 << l) for p in range(13) for l,m in enumerate(self.lines)
                    if m >> p & 1 and all(c != (l if side else p) for side,c in seed['centers'])]
        self.neg = []
        for x in range(8192):
            if any(pop(x&m) > 2 for m in self.lines):
                continue
            available = sum(1 << l for l, m in enumerate(self.lines) if not (x&m))
            y = available
            while True:
                if arcy[y]:
                    self.neg.append((x, y))
                if not y:
                    break
                y = (y-1) & available
        assert len(self.pos) == 16 and len(self.neg) == 12234
        self.rows = self.pos + self.neg
        # Pack each column once from the raw promise rows. Slice construction is in C.
        bits = [bytearray((len(self.rows)+7)//8) for _ in range(26)]
        for i, (x, y) in enumerate(self.rows):
            mask = x | y << 13
            while mask:
                k = (mask & -mask).bit_length()-1
                bits[k][i//8] |= 1 << (i%8)
                mask &= mask-1
        self.bank = [int.from_bytes(col, 'little') for col in bits] + [0]*44
        for at, (a,b,c,d) in self.ports:
            self.bank[at] = self.bank[a] | self.bank[b]
            self.bank[at+1] = self.bank[c] | self.bank[d]
            self.bank[at+2] = self.bank[at] | self.bank[at+1]
        self.want = (1 << len(self.pos))-1
        self.seed_rows = self.eval(seed['gates'])
        self.misses = [self.pos.index((1 << p, 1 << l)) for p,l in ((2,1),(6,10))]
        assert self.seed_rows == self.want ^ sum(1 << i for i in self.misses)
        self.seed_neg = self.diverse([i for i in range(len(self.pos), len(self.rows))
                                      if sum(map(pop, self.rows[i])) >= 5], 16)

    def eval(self, gates):
        wires = self.bank.copy()
        assert len(gates) == 18
        for i,(op,a,b) in enumerate(gates):
            assert op in (0,1) and all(k in self.pin or 70 <= k < 70+i for k in (a,b))
            wires.append((wires[a] & wires[b]) if op else (wires[a] | wires[b]))
        return wires[-1]

    def diverse(self, rows, cap):
        if len(rows) <= cap:
            return rows.copy()
        # Spread selected counterexamples over distinct supports. Deterministic, bounded.
        ordered = sorted(rows, key=lambda i:(-sum(map(pop, self.rows[i])),i))
        pool = ordered[:128] + ordered[128::max(1,len(ordered)//128)]
        pool = list(dict.fromkeys(pool))
        masks = {i:self.rows[i][0] | self.rows[i][1] << 13 for i in pool}
        dist = {i:27 for i in pool}
        result = []
        while len(result) < cap and dist:
            best = max(dist, key=dist.get)
            result.append(best)
            del dist[best]
            for i in dist:
                dist[i] = min(dist[i],pop(masks[best]^masks[i]))
        return result


def reorder(gates, order):
    assert sorted(order) == list(range(18)) and order[-1] == 17
    pos = {k:70+t for t,k in enumerate(order)}
    result = []
    for k in order:
        op,a,b = gates[k]
        a,b = [j if j<70 else pos[j-70] for j in (a,b)]
        assert max(a,b) < 70 + len(result)
        result.append((op,a,b))
    return result


class CNF:
    def __init__(self):
        self.refs = [False]
        self.cs = []
        self.one = self.new(True)
        self.cl(self.one)

    def new(self, seedval):
        self.refs.append(bool(seedval))
        return len(self.refs)-1

    def cl(self, *xs):
        self.cs.append(xs)

    def val(self, lit):
        return self.refs[abs(lit)] == (lit>0)

    def exactly_one(self, opts, chosen):
        ss = [self.new(w==chosen) for w in opts]
        self.cl(*ss)
        pref = []
        for i,s in enumerate(ss[:-1]):
            p = self.new(i >= opts.index(chosen))
            self.cl(-s,p)
            if pref:
                self.cl(-pref[-1],p)
                self.cl(-s,-pref[-1])
            pref.append(p)
        self.cl(-ss[-1],-pref[-1])
        return ss,pref

    def mux(self, select, wires, baseline):
        v = self.new(self.val(baseline))
        for s,w in zip(select,wires):
            self.cl(-s,-v,w)
            self.cl(-s,v,-w)
        return v

    def row_gate(self, op, x, y):
        and_gate = self.val(op)
        z = self.new((self.val(x) and self.val(y)) if and_gate else (self.val(x) or self.val(y)))
        for c in [(-op,-z,x),(-op,-z,y),(-op,z,-x,-y),
                  (op,z,-x),(op,z,-y),(op,-z,x,y)]:
            if self.one in c:
                continue
            self.cl(*(lit for lit in c if lit != -self.one))
        return z

    def dump(self, path):
        with open(path,'w') as out:
            out.write('p cnf %d %d\n' % (len(self.refs)-1,len(self.cs)))
            out.writelines(' '.join(map(str,c))+' 0\n' for c in self.cs)


def encode(p, template, rows):
    order, mutable = WINDOWS[template]
    gs = reorder(p.seed['gates'],order)
    enc = CNF()
    rec = {}
    for i,(op,a,b) in enumerate(gs):
        if order[i] not in mutable:
            continue
        opts = sorted(p.pin) + list(range(70,70+i))
        a,b = sorted((a,b))
        ls,_ = enc.exactly_one(opts,a)
        rs,pref = enc.exactly_one(opts,b)
        for j in range(1,len(opts)):
            enc.cl(-ls[j],-pref[j-1])  # left source index <= right
        rec[i] = (enc.new(op), opts, ls, rs)
    final = []
    for row in rows:
        ws = [enc.one if (col>>row)&1 else -enc.one for col in p.bank]
        for i,(op,a,b) in enumerate(gs):
            if i in rec:
                opvar,opts,ls,rs = rec[i]
                os = [ws[j] for j in opts]
                a,b = sorted((a,b))
                x = enc.mux(ls,os,ws[a])
                y = enc.mux(rs,os,ws[b])
            else:
                opvar = enc.one if op else -enc.one
                x,y = ws[a],ws[b]
            ws.append(enc.row_gate(opvar,x,y))
        final.append(len(enc.cs))
        enc.cl(ws[-1] if row<len(p.pos) else -ws[-1])
    return enc,gs,rec,final


def decode(gs, rec, model):
    gates = list(gs)
    for i,(op,opts,ls,rs) in rec.items():
        left = [k for k,s in zip(opts,ls) if s in model]
        right = [k for k,s in zip(opts,rs) if s in model]
        assert len(left) == len(right) == 1
        gates[i] = (int(op in model),left[0],right[0])
    return gates


def self_test(p):
    rows = list(range(len(p.pos))) + p.seed_neg
    for t in range(len(WINDOWS)):
        enc,gs,rec,ends = encode(p,t,rows)
        assert p.eval(gs) == p.seed_rows
        mismatches = [i for i,c in enumerate(enc.cs) if not any(enc.val(j) for j in c)]
        assert mismatches == sorted(ends[i] for i in p.misses)
        model = {i for i,b in enumerate(enc.refs) if b}
        assert p.eval(decode(gs,rec,model)) == p.seed_rows
    print('No SAT calls. Replayed 16 positives + 12234 negatives in six schedules/windows;')
    print('all six planted CNFs violate exactly the final clauses for (2,1) and (6,10).')
    print('Last template:',len(enc.refs)-1,'variables,',len(enc.cs),'clauses,',len(rows),'rows.')


def memory_limits(child=False):
    # Linux hosted runner. Keep a larger inherited hard limit for the solver.
    # While it runs, the sum of both processes' address-space limits is 2800 MiB.
    old = resource.getrlimit(resource.RLIMIT_AS)[1]
    hard = 2100*1024**2 if old == resource.RLIM_INFINITY else min(2100*1024**2,old)
    soft = hard if child else min(hard,700*1024**2)
    resource.setrlimit(resource.RLIMIT_AS,(soft,hard))


def limit_solver():
    memory_limits(child=True)


def solver_command():
    for x in (shutil.which('cadical'),*sorted(Path.home().glob('.elan/toolchains/*/bin/cadical')),
              shutil.which('kissat')):
        if x and os.access(x,os.X_OK):
            return [str(x),'-q']
    if shutil.which('z3'):
        return [shutil.which('z3'),'-dimacs']
    import importlib.util
    if importlib.util.find_spec('pysat'):
        return [sys.executable,__file__,'--pysat']
    return None


def solver(cmd, cnf, sec):
    try:
        out = subprocess.run(cmd + [str(cnf)],stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT,timeout=sec,preexec_fn=limit_solver)
    except subprocess.TimeoutExpired:
        return 'timeout',set()
    lines = out.stdout.decode(errors='replace').splitlines()
    if out.returncode==20 or 's UNSATISFIABLE' in lines:
        return 'unsat',set()
    if out.returncode==10 or 's SATISFIABLE' in lines:
        model = {int(z) for line in lines if line.startswith('v ') for z in line[2:].split() if int(z)>0}
        if model:
            return 'sat',model
    raise RuntimeError('Solver returned %s: %s'%(out.returncode,lines[-3:]))


def run(p,args,start):
    stop = start+min(84,max(1,args.seconds))
    directory = args.directory.resolve()
    directory.mkdir(parents=True,exist_ok=True)
    # Include source digest so a changed model encoder cannot silently reuse UNSAT.
    key = hashlib.sha256(Path(__file__).read_bytes()+args.seed.read_bytes()).hexdigest()
    ledger = directory/'progress.json'
    found = directory/'witness.json'
    state = json.loads(ledger.read_text()) if ledger.exists() else {'key':key,'templates':{}}
    if state['key'] != key:
        raise ValueError('Different seed/program. Choose a distinct output directory.')
    if found.exists():
        w=json.loads(found.read_text())
        assert w['key']==key and w['centers']==p.seed['centers'] and w['rot']==p.seed['rot']
        assert p.eval(w['gates']) == p.want
        print('Existing full witness verified:',found,flush=True)
        return
    cmd = solver_command()
    if not cmd:
        raise SystemExit('No CaDiCaL, Kissat, Z3 or PySAT found; no search started.')
    print('Using',cmd[0],'; time limit',min(84,args.seconds),'seconds',flush=True)
    todo = [t for t in range(len(WINDOWS)) if state['templates'].get(str(t),{}).get('status')!='unsat']
    with tempfile.TemporaryDirectory(dir=directory) as tmp:
        cnf = Path(tmp)/'window.cnf'
        for j,t in enumerate(todo):
            now=time.monotonic()
            if stop-now<1.5:
                break
            end=min(stop,now+(stop-now)/(len(todo)-j))
            item=state['templates'].setdefault(str(t),{'negatives':p.seed_neg.copy(),'attempts':0})
            while end-time.monotonic()>0.65:
                rows=list(range(len(p.pos)))+item['negatives']
                if len(rows)>150:
                    item['status']='row_limit'
                    break
                enc,gs,rec,_=encode(p,t,rows)
                enc.dump(cnf)
                left=end-time.monotonic()
                if left<=0.10:
                    item['status']='timeout'
                    break
                status,model=solver(cmd,cnf,left)
                item['attempts']+=1
                item['status']=status
                if status!='sat':
                    break
                candidate=decode(gs,rec,model)
                val=p.eval(candidate)
                assert all(bool((val>>r)&1)==(r<len(p.pos)) for r in rows)
                bad=val ^ p.want
                if not bad:
                    answer={'centers':p.seed['centers'],'rot':p.seed['rot'],'gates':candidate,
                            'missing':[],'negative_errors':0,'key':key,'template':t,
                            'schedule_in_original_indices':WINDOWS[t][0]}
                    atomic(found,answer)
                    item['status']='witness'
                    atomic(ledger,state)
                    print('Full witness verified',found,flush=True)
                    return
                errors=[i for i in range(len(p.pos),len(p.rows)) if bad>>i & 1]
                item['last_violations']=len(errors)
                added=p.diverse(errors,12)
                assert added and not set(added).intersection(item['negatives'])
                item['negatives'].extend(added)
                item['status']='counterexamples'
                atomic(ledger,state)
            atomic(ledger,state)
            print('window',t,'status',item.get('status'),'training negatives',len(item['negatives']),
                  'attempts',item['attempts'],flush=True)
    print('No full witness in bounded run; a timeout is inconclusive.',flush=True)


if __name__=='__main__':
    if len(sys.argv)==3 and sys.argv[1]=='--pysat':
        from pysat.formula import CNF as PyCNF
        from pysat.solvers import Minisat22
        with Minisat22(bootstrap_with=PyCNF(from_file=sys.argv[2]).clauses) as sat:
            if sat.solve():
                print('s SATISFIABLE\nv',*sat.get_model(),0)
            else:
                print('s UNSATISFIABLE')
        sys.exit()
    start=time.monotonic()
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed',type=Path,default=DEFAULT)
    parser.add_argument('--directory',type=Path)
    parser.add_argument('--seconds',type=float,default=84)
    parser.add_argument('--self-test',action='store_true')
    args=parser.parse_args()
    if not args.self_test and sys.platform.startswith('linux'):
        memory_limits()
    p=Problem(json.loads(args.seed.read_text()))
    if args.self_test:
        self_test(p)
    else:
        if args.directory is None:
            parser.error('--directory is required for search')
        run(p,args,start)
