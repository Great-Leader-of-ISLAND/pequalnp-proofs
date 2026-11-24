"""Try replacing three stars of the explicit 27-gate Heawood circuit by ten gates."""
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
import json, subprocess, sys

EDGES = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
         (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
         (6,8),(6,9),(6,11)]
def subset(a,b):
    return a & b == a

def boundary(centers, compress):
    lines = sorted({b for a,b in EDGES if a in centers})
    fibres = {}
    for b in lines:
        key = tuple(a for a in centers if (a,b) in EDGES) if compress else (b,)
        fibres.setdefault(key,[]).append(b)
    groups = [[a] for a in centers] + list(fibres.values())
    hit = [(i,j) for i,g in enumerate(groups) for j,h in enumerate(groups)
           if any((a,b) in EDGES for a in g for b in h)]
    pos = sorted({(1<<a)|(1<<b) for a,b in hit})
    n = len(groups)
    def independent(mask):
        return not any(subset(edge,mask) for edge in pos)
    negs = [mask for mask in range(1<<n) if independent(mask) and
            all(not independent(mask | (1<<i)) for i in range(n) if not mask>>i & 1)]
    return groups,pos,negs

class SAT:
    def __init__(self):self.n=0;self.cl=[]
    def new(self):self.n+=1;return self.n
    def one(self,lits):
        self.cl.append(lits)
        self.cl.extend([-u,-v] for u,v in combinations(lits,2))

def search(centers, compress, delta, solver, duration):
    groups,pos,negs = boundary(centers, compress)
    n = len(groups)
    k = 11 - sum(len(g)-1 for g in groups) - delta
    label = (centers, compress, k, n, len(pos), len(negs))
    f=SAT(); inputs=[]; ops=[]
    for i in range(k):
        options=[[f.new() for _ in range(n+i)] for _ in range(2)]
        for opts in options:f.one(opts)
        # The gates commute. A repeated input remains allowed for padding.
        for j,b in enumerate(options[1]):
            f.cl.extend([-a,-b] for a in options[0][j+1:])
        inputs.append(options);ops.append(f.new()) # true means AND
    for j in range(n+k-1):
        essential=j>=n or any(p>>j&1 and any(subset(p^(1<<j),v) for v in negs) for p in pos)
        if essential:f.cl.append([s[j] for opts in inputs for s in opts if j<len(s)])
    # Lexicographically order commuting independent gates by their largest input
    # and then their smaller input. Each meaningful DAG has such an extension.
    for earlier,later in zip(inputs,inputs[1:]):
        for a,lit in enumerate(earlier[1]):
            f.cl.extend([-lit,-h] for h in later[1][:a])
            for j,l in enumerate(earlier[0]):
                for v in later[0][:j]:f.cl.append([-lit,-later[1][a],-l,-v])
    matrix={}
    for row in pos+negs:
        wires=[]
        for j in range(n):
            z=f.new();f.cl.append([z if row>>j&1 else -z]);wires.append(z)
        for op,sides in zip(ops,inputs):
            vs=[]
            for choices in sides:
                v=f.new();vs.append(v)
                for s,wire in zip(choices,wires):f.cl.extend([[-s,-wire,v],[-s,wire,-v]])
            a,b=vs;z=f.new();wires.append(z)
            f.cl.extend([[-op,-z,a],[-op,-z,b],[-op,-a,-b,z],[op,-a,z],[op,-b,z],[op,-z,a,b]])
        f.cl.append([wires[-1] if row in pos else -wires[-1]])
        matrix[row]=wires
    if delta == 0:
        dag = []
        def add(op,a,b):
            dag.append((op,min(a,b),max(a,b)))
            return n+len(dag)-1
        stars = []
        for c in centers:
            adj = [j for j,g in enumerate(groups) if any((c,b) in EDGES for b in g)]
            z = adj[0]
            for j in adj[1:]:
                z = add('or',z,j)
            stars.append(add('and',z,groups.index([c])))
        z=stars[0]
        for z1 in stars[1:]:
            z=add('or',z,z1)
        assert len(dag)==k
        remap = {j:j for j in range(n)}
        for i in range(k):
            avail = []
            for j,(op,a,b) in enumerate(dag):
                if n+j not in remap and a in remap and b in remap:
                    l,r=sorted((remap[a],remap[b]));avail.append((r,l,op,j))
            r,l,op,j=min(avail)
            remap[n+j]=n+i
            f.cl.extend([[inputs[i][0][l]],[inputs[i][1][r]],[ops[i] if op=='and' else -ops[i]]])
    with TemporaryDirectory() as d:
        path=Path(d)/'window.cnf'
        with path.open('w') as h:
            print('p cnf',f.n,len(f.cl),file=h)
            for clause in f.cl:print(*clause,0,file=h)
        try:r=subprocess.run([solver,'-q',str(path)],capture_output=True,text=True,timeout=duration)
        except subprocess.TimeoutExpired:print(label,'UNKNOWN',flush=True);return
    if r.returncode==20:print(label,'UNSAT',flush=True);return
    assert r.returncode==10
    model={int(lit) for s in r.stdout.splitlines() if s.startswith('v ') for lit in s[2:].split()}
    gates=[]
    def record(op,a,b):
        gates.append((op,a,b))
        return 13+len(gates)
    def joins(raw):
        v=raw[0]
        for j in raw[1:]:v=record('or',v,j)
        return v
    wires=[joins(g) for g in groups]
    for typ,pins in zip(ops,inputs):
        a,b=[wires[next(i for i,x in enumerate(side) if x in model)] for side in pins]
        wires.append(record('and' if typ in model else 'or',a,b))
    top=wires[-1]
    for c in range(7):
        if c not in centers:
            line=joins([b for a,b in EDGES if a==c])
            top=record('or',top,record('and',c,line))
    assert len(gates)==27-delta
    # Independent full-cube evaluation using transposed integer truth tables.
    N=1<<14
    raw=[]
    for i in range(14):
        run=1<<i
        word=((1<<run)-1)<<run
        for j in range(13-i):
            word|=word<<(2*run);run*=2
        raw.append(word)
    ws=raw[:];answer=0
    for a,b in EDGES:answer|=raw[a]&raw[b]
    for op,a,b in gates:
        ws.append(ws[a]&ws[b] if op=='and' else ws[a]|ws[b])
    assert ws[top]==answer
    print(label,'SAT and full 16384 rows confirmed, total gates',len(gates),flush=True)
    if delta: print('PHYSICAL WITNESS',json.dumps((gates,top)),flush=True)

if __name__=='__main__':
    cases=[((0,1,3),True),((0,1,2),False),((0,1,3),False)]
    for centers,compress in cases:
        search(centers,compress,0,sys.argv[1],10)
    for centers,compress in cases:
        search(centers,compress,1,sys.argv[1],60)
