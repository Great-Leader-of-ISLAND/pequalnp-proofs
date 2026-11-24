"""Necessary union-circuit capacity for a nine-leaf one-star boundary.

All nine linear supports are nonzero and distinct by the >=9 support coloring
bound. Linearizing all leaves cannot compute all 16 positives (the >=10 support
bound). A genuinely mixed edge must get from a first clean source AND (zero
singleton support) to a nonzero terminal. Somewhere on that path it first
enters a nonzero support, using an OR whose other pin has exactly the same
nonzero support as the output. Such a gate cannot create a distinct nontrivial
support. Every other clean gate acts as pure union or constant zero on
singletons. Hence at most 11 of 13 prefix slots create new nontrivial support
masks. Strictly increasing mask order is a topological order for proper union;
unused slots in this relaxation can be filled by unused, distinct two-sets.
"""
from itertools import combinations


class UnionCircuit:
    def __init__(self, nvars, clauses):
        self.n = nvars
        self.clauses = clauses
        self.true = self.new()
        self.add(self.true)

    def new(self):
        self.n += 1
        return self.n

    def add(self,*ls):
        self.clauses.append(list(ls))

    def one_hot(self,n):
        bits = [self.new() for _ in range(n)]
        self.add(*bits)
        seen = -self.true
        for i,b in enumerate(bits):
            self.add(-seen,-b)
            if i < n-1:
                nxt = self.new()
                self.add(-b,nxt)
                self.add(-seen,nxt)
                self.add(-nxt,seen,b)
                seen = nxt
        return bits

    def select(self, flags, data):
        z = self.new()
        for flag,bit in zip(flags,data):
            self.add(-flag,-bit,z)
            self.add(-flag,bit,-z)
        return z

    def lt(self,a,b):
        equal = self.true
        for x,y in reversed(list(zip(a,b))):
            self.add(-equal,-x,y)
            nxt = self.new()
            self.add(-nxt,equal)
            self.add(-nxt,-x,y)
            self.add(-nxt,x,-y)
            self.add(-equal,x,y,nxt)
            self.add(-equal,-x,-y,nxt)
            equal = nxt
        self.add(-equal)

    def attach(self, leaves, width=11, budget=11):
        ws = [[self.true if i==j else -self.true for i in range(width)] for j in range(width)]
        for k in range(budget):
            a,b = self.one_hot(len(ws)),self.one_hot(len(ws))
            for u,l in enumerate(a):
                for v in range(u+1):
                    self.add(-l,-b[v])
            result=[]
            for col in zip(*ws):
                x,y=self.select(a,col),self.select(b,col)
                z=self.new()
                self.add(-x,z)
                self.add(-y,z)
                self.add(-z,x,y)
                result.append(z)
            # Any union of two distinct nonempty wires contains at least two
            # variables unless a duplicate singleton is available. Initial
            # wires are distinct, and strict sorting prevents duplicates.
            if k:
                self.lt(ws[-1],result)
            ws.append(result)
        picks=[]
        for leaf in leaves:
            select=self.one_hot(len(ws))
            picks.append(select)
            for j,out in enumerate(leaf):
                for flag,wire in zip(select,ws):
                    self.add(-flag,-out,wire[j])
                    self.add(-flag,out,-wire[j])
        for a,b in combinations(picks,2):
            for l,r in zip(a,b):
                self.add(-l,-r)
        return self.n,self.clauses


def controls(solver):
    import subprocess
    import tempfile
    from pathlib import Path
    # Three distinct, prescribed nontrivial sets in five variables. The
    # overlapping third set is realizable in three steps, but not in two.
    for budget,expected in ((3,10),(2,20)):
        f=UnionCircuit(0,[])
        leaves=[[f.new() for _ in range(5)] for _ in range(3)]
        for row,mask in zip(leaves,[3,6,7]):
            for j,bit in enumerate(row):f.add(bit if mask&(1<<j) else -bit)
        n,cs=f.attach(leaves,width=5,budget=budget)
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'calibrate.cnf'
            with path.open('w') as out:
                print('p cnf',n,len(cs),file=out)
                for c in cs:print(*c,0,file=out)
            result=subprocess.run([solver,'-q','-t','3',str(path)],capture_output=True,timeout=8)
            assert result.returncode==expected,(budget,result.returncode)
            print('union-circuit control',budget,'SAT' if expected==10 else 'UNSAT')


if __name__=='__main__':
    import sys
    controls(sys.argv[1])
