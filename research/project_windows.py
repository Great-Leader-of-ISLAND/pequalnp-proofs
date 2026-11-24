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
    shapes=[(0,1),next(s for s in combinations(range(13),3) if points[s[0]]&points[s[1]]&points[s[2]]),next(s for s in combinations(range(13),3) if not points[s[0]]&points[s[1]]&points[s[2]])]
    for lines in shapes:
        seen={}
        for neg in (N,M):
            _,p,q=boundary(lines,neg);key=tuple(p),tuple(q)
            if key in seen:print(lines,'identical compressed care rows to',seen[key],flush=True);continue
            seen[key]='generic' if neg is N else 'full'
            if len(lines)==2:search(lines,neg,solver,15,0)
            search(lines,neg,solver,seconds,1)
