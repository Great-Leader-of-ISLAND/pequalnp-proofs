"""Synthesize a replacement for selected line-star blocks, preserving the care rows."""
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess,sys,json
from generic2147 import points,POS,M,N,subset,eval_table

def boundary(lines,neg):
    fibres={}
    for p in range(13):
        profile=tuple(l for l in lines if points[l]>>p&1)
        if profile:fibres.setdefault(profile,[]).append(p)
    groups=list(fibres.values())+[[13+l] for l in lines]
    masks=[sum(1<<i for i in group) for group in groups]
    def project(r):return sum(1<<i for i,m in enumerate(masks) if r&m)
    pos={project(r) for r in POS if any(r>>(13+l)&1 for l in lines)}
    negs={project(r) for r in neg}
    pos=sorted(x for x in pos if not any(x!=y and subset(y,x) for y in pos))
    negs=sorted(x for x in negs if not any(x!=y and subset(x,y) for y in negs))
    assert not any(subset(p,n) for p in pos for n in negs)
    return groups,pos,negs

class SAT:
    def __init__(self):self.n=0;self.cl=[]
    def new(self):self.n+=1;return self.n
    def one(self,lits):
        self.cl.append(lits)
        self.cl.extend([-u,-v] for u,v in combinations(lits,2))

def search(lines,neg,solver,duration,delta):
    groups,pos,negs=boundary(lines,neg)
    n=len(groups);k=5*len(lines)-1-sum(len(g)-1 for g in groups)-delta
    label=('generic' if neg is N else 'full',lines,n,k,len(pos),len(negs))
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
    # When gate g is the sole reader of raw u, it must distinguish each pair
    # for which u is the only input true on the positive and false on the negative.
    # This follows from monotonicity of the suffix in all other wires.
    for u in range(n):
        collisions=[(p,q) for p in pos for q in negs if p & ~q == 1<<u]
        for i in range(k):
            elsewhere=[choice[u] for j,opts in enumerate(inputs) if i!=j for choice in opts]
            for r in {p for p,q in collisions}:f.cl.append(elsewhere+[matrix[r][n+i]])
            for r in {q for p,q in collisions}:f.cl.append(elsewhere+[-matrix[r][n+i]])
    if delta==0 and len(lines)==3:
        # Independently include a 64-gate control via its actual selections,
        # in the same order used by the symmetry-breaking clauses.
        masks=[sum(1<<p for p in g) for g in groups]
        dag=[]
        def record(name,a,b):dag.append((name,min(a,b),max(a,b)));return n+len(dag)-1
        stars=[]
        for l in lines:
            leaves=[i for i,mask in enumerate(masks) if mask & points[l]]
            z=leaves[0]
            for j in leaves[1:]:z=record('or',z,j)
            stars.append(record('and',z,groups.index([13+l])))
        z=stars[0]
        for t in stars[1:]:z=record('or',z,t)
        assert len(dag)==k
        rename={j:j for j in range(n)}
        for idx in range(k):
            choices=[]
            for t,(op,a,b) in enumerate(dag):
                if n+t in rename or a not in rename or b not in rename:continue
                v,w=sorted((rename[a],rename[b]));choices.append((w,v,op,t))
            w,v,op,t=min(choices);rename[n+t]=n+idx
            f.cl.extend([[inputs[idx][0][v]],[inputs[idx][1][w]],[ops[idx] if op=='and' else -ops[idx]]])

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
    gates=[];ports=[]
    def add(op,a,b):gates.append((op,a,b));return 25+len(gates)
    def ors(ns):
        z=ns[0]
        for x in ns[1:]:z=add('or',z,x)
        return z
    for g in groups:ports.append(ors(g))
    for op,sides in zip(ops,inputs):
        a,b=[ports[next(i for i,v in enumerate(sel) if v in model)] for sel in sides]
        ports.append(add('and' if op in model else 'or',a,b))
    out=ports[-1]
    for l,p in enumerate(points):
        if l in lines:continue
        q=ors([i for i in range(13) if p>>i&1]);out=add('or',out,add('and',q,13+l))
    assert len(gates)==64-delta
    vals,degs=eval_table(gates)
    assert vals[out]==(1<<len(POS))-1
    def run(row):
        ws=[bool(row>>j&1) for j in range(26)]
        for op,a,b in gates:ws.append((ws[a] and ws[b]) if op=='and' else (ws[a] or ws[b]))
        return ws[out]
    assert all(map(run,POS)) and not any(map(run,neg))
    print(label,'SAT',len(gates),'formal degrees',degs[out],'full incidence',not any(map(run,M)),flush=True)
    if delta:print('PHYSICAL',json.dumps([gates,out]),flush=True)

if __name__=='__main__':
    solver=sys.argv[1];seconds=int(sys.argv[2]);common=lambda ls: all(points[i]&points[j] for i,j in combinations(ls,2))
    lines=(0,1,2)
    for neg in (N,M):
        search(lines,neg,solver,8,0)
        search(lines,neg,solver,seconds,1)
