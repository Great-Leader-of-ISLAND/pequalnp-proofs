"""Finite monotone synthesis dictionary for a Petersen 19-gate witness.

mixes arbitrarily many nonstar positive CNF blocks with all stars, with shared
linear and nonlinear wires. generate FILE produces DIMACS, decode MODEL reads
standard CaDiCaL/competition 'v' lines and rechecks all 1024 assignments.
"""
import argparse
from importlib.util import spec_from_file_location,module_from_spec
from itertools import combinations
from pathlib import Path
def load(name):
    spec=spec_from_file_location(name,Path(__file__).with_name(name+'.py'))
    mod=module_from_spec(spec);spec.loader.exec_module(mod);return mod
g=load('petersen651-guarded-stars'); pg=load('petersen651-paired-guards')

def subset(s):
    xs=sorted(s)
    for i in range(1,len(xs)):
        yield from (frozenset(t) for t in combinations(xs,i))
def partitions(s):
    return [(q,s-q) for q in subset(s) if min(s) in q]
def ordered(sets):
    return sorted(sets,key=lambda s:(len(s),tuple(sorted(s))))

class Model:
    def __init__(self,budget):
        self.n=0;self.cs=[]
        terms={s:p for s,p,_ in pg.make()}
        for c,s,e in g.STARS:terms[frozenset((1<<c,s))]=e
        roots=ordered(terms); ops={s for t in roots for s in (*subset(t),t) if len(s)>=2}
        ors={s for t in roots for s in t if g.bits(s)>=2}|{3}
        ors.update(p for s in sorted(ors) if g.bits(s)==3 for p in g.PAIRS[s])
        self.pre={s:self.var() for s in sorted(ors,key=lambda s:(g.bits(s),s))}
        self.andgate={s:self.var() for s in ordered(ops)}
        self.roots={s:self.var() for s in roots}
        self.cs.append([self.pre[3]])
        for s,v in self.pre.items():
            if g.bits(s)==3:self.cs.append([-v]+[self.pre[p] for p in g.PAIRS[s]])
        for t,v in self.andgate.items():
            if len(t)==2:
                for s in t:
                    if s in self.pre:self.cs.append([-v,self.pre[s]])
                continue
            splits=[]
            for l,r in partitions(t):
                x=self.var();splits.append(x)
                for c in (l,r):
                    w=self.signal(c)
                    if w:self.cs.append([-x,w])
            self.cs.append([-v]+splits)
        for t,v in self.roots.items():self.cs.append([-v,self.andgate[t]])
        for i in range(len(g.E)):
            self.cs.append([v for t,v in self.roots.items() if (terms[t]>>i)&1])
        inputs=list(self.pre.values())+list(self.andgate.values())+list(self.roots.values())
        self.atmost(inputs,budget+1)
    def var(self):
        self.n+=1
        return self.n
    def signal(self,t):
        return self.andgate[t] if len(t)>1 else self.pre.get(next(iter(t)))
    def atmost(self,lits,k):
        prev=[]
        for x in lits:
            cur=[self.var() for _ in range(min(k,len(prev)+1))]
            self.cs.append([-x,cur[0]])
            for i,p in enumerate(prev):
                self.cs.append([-p,cur[i]])
                self.cs.append([-p,-x]+([cur[i+1]] if i+1<len(cur) else []))
            prev=cur
    def dimacs(self,p):
        with p.open('w') as f:
            print('p cnf',self.n,len(self.cs),file=f)
            for c in self.cs:print(*c,0,file=f)
    def decode(self,vs):
        gates=[];lin={1<<i:i for i in range(10)}; con={}
        def add(op,a,b):
            gates.append((op,a,b));return 9+len(gates)
        for s in sorted(self.pre,key=lambda s:(s!=3,g.bits(s),s)):
            if self.pre[s] not in vs:continue
            if g.bits(s)==2:
                h=s&-s;lin[s]=add('or',lin[h],lin[s^h])
            else:
                h=next(p for p in g.PAIRS[s] if p in lin);lin[s]=add('or',lin[h],lin[s^h])
        for s,w in lin.items():con[frozenset((s,))]=w
        for t in ordered(self.andgate):
            if self.andgate[t] not in vs:continue
            a,b=next((a,b) for a,b in partitions(t) if a in con and b in con)
            con[t]=add('and',con[a],con[b])
        out=[con[t] for t,v in self.roots.items() if v in vs]
        result=out[0]
        for w in out[1:]:result=add('or',result,w)
        for i in range(1024):
            vals=[bool(i&(1<<j)) for j in range(10)]
            for op,a,b in gates:vals.append((vals[a] and vals[b]) if op=='and' else (vals[a] or vals[b]))
            assert vals[result]==any(i&m==m for m in g.EM)
        assert gates[0]==('or',0,1)
        return gates,result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('action',choices=('generate','decode','check'));p.add_argument('file',type=Path,nargs='?');p.add_argument('--budget',type=int,default=19);a=p.parse_args();m=Model(a.budget)
    if a.action=='generate':m.dimacs(a.file)
    if a.action=='decode':
        vs={int(w) for row in a.file.read_text().splitlines() if row.startswith('v ') for w in row[2:].split() if int(w)>0}
        gs,o=m.decode(vs);assert len(gs)<=a.budget;print(gs,o)
    if a.action=='check':
        # Select one endpoint for every edge using a minimum vertex cover, and
        # add unused z. This known 21-gate control tests linear and root decode.
        cover=next(c for c in combinations(range(10),6) if all(a in c or b in c for a,b in g.E))
        nb={v:0 for v in cover}
        for a,b in g.E:
            c=a if a in nb else b;nb[c]|=1<<(a+b-c)
        vs={m.pre[3]}
        for i,s in nb.items():
            if not s:continue
            t=frozenset((1<<i,s));vs.update((m.roots[t],m.andgate[t]))
            if s in m.pre:vs.add(m.pre[s])
            if g.bits(s)==3:vs.add(m.pre[g.PAIRS[s][0]])
        gs,o=m.decode(vs);assert len(gs)==21;print('21-gate control passed all 1,024 rows')
    print('linear',len(m.pre),'conjunctions',len(m.andgate),'root choices',len(m.roots),'CNF',m.n,len(m.cs))
