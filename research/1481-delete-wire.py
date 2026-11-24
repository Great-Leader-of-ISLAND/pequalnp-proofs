"""Test exact one-gate contractions of the explicit 65-gate alarm construction."""
from collections import Counter
from functools import reduce
from pathlib import Path
from runpy import run_path

model=run_path(str(Path(__file__).with_name('1481-double-star.py')))
edges,negs=model['tests']()
cols=model['columns'](edges+negs)
expected=(1<<len(edges))-1
base=model['hood']

def circuit(omit,balanced,reverse,dual):
    gates=[]
    def op(b,i,j):
        if i==j or max(i,j)>=26+len(gates):raise ValueError('invalid input pins')
        gates.append((b,i,j))
        return len(gates)+25
    def fold(xs):
        if reverse:xs=list(reversed(xs))
        if not balanced:return reduce(lambda a,b:op(1,a,b),xs)
        while len(xs)>1:
            ys=[op(1,xs[i],xs[i+1]) for i in range(0,len(xs)-1,2)]
            if len(xs)%2:ys.append(xs[-1])
            xs=ys
        return xs[0]
    ns=([list(p for p in range(13) if l in base[p]) for l in range(13)] if dual else base)
    shore,opp=(13,0) if dual else (0,13)
    a=fold([op(0,shore+i,fold([opp+t for t in ns[i]])) for i in range(13) if i!=omit])
    b=fold([opp+t for t in ns[omit]])
    return gates,op(0,op(1,a,shore+omit),op(1,a,b))

def contract(g,z,i,r):
    def cv(x):
        if x==26+i:return r
        return x-1 if x>26+i else x
    out=[]
    for j,(op,a,b) in enumerate(g):
        if j==i:continue
        a,b=cv(a),cv(b)
        if a==b:return None
        out.append((op,a,b))
    return out,cv(z)
def screen(g,z):
    return model['evaluate'](g,cols)[z]==expected
def doubles(g,z):
    return [(p,t) for p in range(13) for t in base[p]
            if not model['blame'](g,p,13+t)[z] and not model['blame'](g,13+t,p)[z]]
def check(variants):
    counts=Counter()
    for params in variants:
        g,z=circuit(*params)
        assert len(g)==65 and screen(g,z) and doubles(g,z)
        counts['controls']+=1
        for i in range(65):
            for r in range(26+i):
                old=contract(g,z,i,r)
                if old is None:continue
                counts['legal']+=1
                if not screen(*old):continue
                counts['computes']+=1
                hits=doubles(*old)
                if hits:
                    print('exact witness', params,i,r,hits[0],old,flush=True)
                    return
    print(dict(counts),flush=True)
if __name__=='__main__':
    import sys
    variants=[(2,a,b,d) for a in (0,1) for b in (0,1) for d in (0,1)]
    check(variants[:int(sys.argv[1])] if len(sys.argv)>1 else variants)
