"""Classify all two-site repairs of chosen legal 65-gate double-alarm controls.
Delete a gate by aliasing it to an earlier wire. Replace one remaining gate
by any binary AND or OR of distinct earlier wires, and keep all other gates.
Two Boolean cofactors of the final output turn the replacement into exact
pointwise obligations. Monotonicity makes the 52 edges and 704 maximal
independent sets a complete test for function equality. Test derivatives
separately on every output-correct repair.
"""
from collections import Counter
from pathlib import Path
import argparse
import runpy
import time

env = runpy.run_path(str(Path(__file__).with_name('1481-delete-wire.py')))
cols, wanted = env['cols'], env['expected']
mask = (1 << (len(env['edges'])+len(env['negs']))) - 1

flags=[(p,t) for p in range(13) for t in env['base'][p]]
directions=[(p,13+t) for p,t in flags]+[(13+t,p) for p,t in flags]
bases=[sum((a==i)<<j for j,(a,b) in enumerate(directions)) for i in range(26)]
marked=[sum((b==i)<<j for j,(a,b) in enumerate(directions)) for i in range(26)]
def double_bits(g,z):
    x,d=bases[:],marked[:]
    for op,a,b in g:
        if op:
            x.append(x[a]|x[b])
            d.append(d[a]|d[b])
        else:
            d.append((x[a]&d[b])|(d[a]&x[b]))
            x.append(x[a]&x[b])
    return (~(d[z]|(d[z]>>52))) & ((1<<52)-1)

def cut(gates, out, index, alias):
    removed = 26+index
    def wire(x):
        return alias if x == removed else x-(x>removed)
    return [(op,wire(a),wire(b)) for k,(op,a,b) in enumerate(gates) if k!=index], wire(out)

def cofactor(gates, w, k, out, value):
    name = k+26
    if out < name:
        return w[out]
    v = w[:name] + [value]
    for op,a,b in gates[k+1:out-25]:
        v.append(v[a] | v[b] if op else v[a] & v[b])
    return v[out]

def candidates(w, n, needs, bans):
    # An OR operand must avoid every negative obligation, and each AND
    # operand must cover every positive obligation, prior to checking pairs.
    good_and = [i for i in range(n) if w[i] & needs == needs]
    good_or = [i for i in range(n) if w[i] & bans == 0]
    for op, ids in [(0,good_and),(1,good_or)]:
        for j,b in enumerate(ids):
            for a in ids[:j]:
                if op and (w[a]|w[b]) & needs == needs or not op and not (w[a]&w[b]&bans):
                    yield op,a,b

def run(variant,lo,hi):
    started=time.monotonic()
    gates,out=env['circuit'](2,(variant>>2)&1,(variant>>1)&1,variant&1)
    assert len(gates)==65 and env['screen'](gates,out)
    control_flags=set(env['doubles'](gates,out))
    baseline=sum((flag in control_flags)<<j for j,flag in enumerate(flags))
    assert baseline and baseline==double_bits(gates,out)
    counts=Counter()
    for index in range(lo,hi):
        for alias in range(26+index):
            g,z=cut(gates,out,index,alias)
            bad=[k for k,(_,a,b) in enumerate(g) if a==b]
            if len(bad)>1:continue
            w=env['model']['evaluate'](g,cols)
            for k in (bad or range(len(g))):
                counts['cofactor_pairs']+=1
                left=cofactor(g,w,k,z,0)
                right=cofactor(g,w,k,z,mask)
                if (wanted & ~right) or (left & ~wanted):continue
                needs=wanted & ~left
                bans=right & ~wanted & mask
                for repair in candidates(w,k+26,needs,bans):
                    counts['exact_repairs']+=1
                    old=g[k]
                    g[k]=repair
                    assert env['screen'](g,z)
                    fib=double_bits(g,z)
                    if fib:
                        found=[flag for j,flag in enumerate(flags) if (fib>>j)&1]
                        assert found==env['doubles'](g,z)
                        print('WITNESS',variant,index,alias,k,repair,z,found,g,flush=True)
                        return True
                    g[k]=old
        if index%8==7:
            print('prefix',index+1,dict(counts),'seconds',round(time.monotonic()-started,2),flush=True)
    print('COMPLETE',variant,lo,hi,dict(counts),'seconds',round(time.monotonic()-started,2),flush=True)
    return False

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('variant',type=int,choices=range(8))
    p.add_argument('--lo',type=int,default=0)
    p.add_argument('--hi',type=int,default=65)
    args=p.parse_args()
    assert 0<=args.lo<args.hi<=65
    run(args.variant,args.lo,args.hi)
