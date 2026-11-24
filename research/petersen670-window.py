#!/usr/bin/env python3
"""Bounded AND/OR/NOT resynthesis for Petersen-minus-one, L-meta-670.

Start from 16-gate star covers. In randomly selected windows, synthesize small
A/O/NOT expressions over earlier wires, on the exact primary-input care set
obtained by independently forcing the window root to 0 and 1. Neutral rewrites
and occasional expansions allow a later contraction across a different window.
Only a full scalar replay on all 512 assignments can accept a witness; search
timeouts and misses have no force as lower bounds.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path
import random
import time

N = 9
ROWS = 1 << N
ALL = (1 << ROWS) - 1
EDGES = ((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5))
INPUTS = [sum(1 << x for x in range(ROWS) if x & (1 << v)) for v in range(N)]
TARGET = 0
for u,v in EDGES:
    TARGET |= INPUTS[u] & INPUTS[v]
COVERS = [frozenset(c) for c in combinations(range(N), 5)
          if all(u in c or v in c for u,v in EDGES)]


def simulate(gs, forced_wire=None, forced_value=0):
    values=INPUTS.copy()
    for op,a,b in gs:
        value = (values[a] ^ ALL if op==2 else values[a] & values[b] if op else values[a] | values[b])
        values.append(forced_value if len(values)==forced_wire else value)
    return values


def cover_formula(rng):
    cover = rng.choice(COVERS)
    centers=list(sorted(cover)); rng.shuffle(centers)
    groups={p:[] for p in centers}; gs=[]
    for a,b in EDGES:
        if b in cover and (a not in cover or rng.randrange(2)):
            a,b=b,a
        groups[a].append(b)
    def add(op,a,b):
        gs.append((op,min(a,b),max(a,b)))
        return N+len(gs)-1
    def union(ws):
        ws=ws.copy()
        while len(ws)>1:
            a=ws.pop(rng.randrange(len(ws))); b=ws.pop(rng.randrange(len(ws)))
            ws.append(add(False,a,b))
        return ws[0]
    root=union([add(True,p,union(groups[p])) for p in centers])
    assert len(gs)==16 and simulate(gs)[root]==TARGET
    return gs,root


def schedule(gs,root,rng):
    # Different valid topological orders expose independent existing wires
    # to the replacement at r without permitting a combinational cycle.
    remap={i:i for i in range(N)}; pending=set(range(N,N+len(gs))); ordered=[]
    while pending:
        ready=sorted(w for w in pending if all(i in remap for i in gs[w-N][1:]))
        w=rng.choice(ready); op,a,b=gs[w-N]
        a,b=sorted((remap[a],remap[b])); remap[w]=N+len(ordered)
        ordered.append((op,a,b)); pending.remove(w)
    return ordered,remap[root]


def windows(gs, root):
    uses=[set() for _ in gs]
    for i,(_,a,b) in enumerate(gs,N):
        for u in (a,b):
            if u>=N: uses[u-N].add(i)
    result=[]
    for r in range(N,N+len(gs)):
        layer={frozenset((r,))}
        result.append((r,frozenset([r])))
        for _ in range(3):
            after=set()
            for group in layer:
                for parent in group:
                    for u in gs[parent-N][1:]:
                        if u>=N and u!=root and u not in group and uses[u-N]<=group:
                            after.add(group | {u})
            for group in sorted(after,key=lambda s:tuple(sorted(s))):
                result.append((r,group))
            layer=after
    return result


def reachable(gs,root,extra=()):
    live=set(); todo=[root,*extra]
    while todo:
        w=todo.pop()
        if w<N or w in live: continue
        live.add(w); todo.extend(gs[w-N][1:])
    remap={p:p for p in range(N)}; out=[]
    for i,(op,a,b) in enumerate(gs,N):
        if i in live:
            remap[i]=N+len(out); out.append((op,remap[a],remap[b]))
    return out,remap[root]


def patch(gs,root,r,group,term):
    out=[]; remap={p:p for p in range(N)}; identical={}
    def add(op,a,b):
        if op==2:
            if a>=N and out[a-N][0]==2: return out[a-N][1]
        elif a==b: return a
        key=(op,min(a,b),max(a,b))
        if key not in identical:
            identical[key]=N+len(out); out.append(key)
        return identical[key]
    def emit(e):
        if isinstance(e,int): return remap[e]
        op,a,b=e
        return add(op,emit(a),emit(b))
    for i,(op,a,b) in enumerate(gs,N):
        if i==r: remap[i]=emit(term)
        elif i not in group: remap[i]=add(op,remap[a],remap[b])
    return out,remap[root]


class WindowEnd(Exception): pass


class Limits:
    def __init__(self,args):
        self.deadline=time.monotonic()+args.seconds
        self.max_tests=args.tests; self.tests=0; self.local_stop=0
    def start(self,local):
        self.local_stop=min(self.max_tests,self.tests+local)
    def tick(self):
        self.tests+=1
        if self.tests>self.local_stop or (self.tests % 128==0 and time.monotonic()>=self.deadline):
            raise WindowEnd
    def done(self):
        return self.tests>=self.max_tests or time.monotonic()>=self.deadline


def candidates(gs,root,values,r,group,rng,limit,delta):
    false_output=simulate(gs,r,0)[root]; true_output=simulate(gs,r,ALL)[root]
    care=false_output ^ true_output
    pos=values[r] & care; neg=(ALL ^ values[r]) & care
    # A one-gate side plus a recursive other side covers trees of <=3 gates.
    # Split sizes are unordered because both operations commute.
    leaves=[(u,values[u]) for u in range(r) if u not in group]
    rng.shuffle(leaves)
    unary_layer=None
    def terms_with_one_gate():
        nonlocal unary_layer
        if unary_layer is None:
            unary_layer=[]
            for (a,x),(b,y) in combinations(leaves,2):
                unary_layer.extend((((True,a,b),x&y),((False,a,b),x|y)))
            unary_layer.extend(((2,a,a),ALL ^ x) for a,x in leaves)
            rng.shuffle(unary_layer)
        return unary_layer
    def synth(P,F,cost):
        if cost==0:
            for e,v in leaves:
                limit.tick()
                if v&P==P and not v&F: yield e
            return
        for child in synth(F,P,cost-1):
            yield (2,child,child)
        ops=[True,False]; rng.shuffle(ops)
        for left_cost in range((cost-1)//2+1):
            pool=leaves if left_cost==0 else terms_with_one_gate()
            for op in ops:
                for a,v in pool:
                    limit.tick()
                    if op:
                        if v&P!=P: continue
                        P1,F1=P,F&v
                    else:
                        if v&F: continue
                        P1,F1=P&~v,F
                    for rhs in synth(P1,F1,cost-1-left_cost):
                        if a!=rhs: yield (op,a,rhs)
    for cost in range(min(3,len(group)+delta)+1):
        yield from synth(pos,neg,cost)


def witness(gs,root):
    if len(gs)>15: return None
    for x in range(512):
        vals=[bool(x & (1<<i)) for i in range(9)]
        expected=any(vals[a] and vals[b] for a,b in EDGES)
        for op,a,b in gs:
            assert 0<=a<len(vals) and 0<=b<len(vals)
            vals.append(not vals[a] if op==2 else vals[a] and vals[b] if op else vals[a] or vals[b])
        if vals[root]!=expected:
            raise ValueError('candidate disagrees with graph')
    return {'gates':[{'op':('not' if op==2 else 'and' if op else 'or'),
                      'inputs':([a] if op==2 else [a,b])} for op,a,b in gs],'output':root}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--seed',type=int,default=1)
    ap.add_argument('--seconds',type=float,default=20)
    ap.add_argument('--tests',type=int,default=4_000_000)
    ap.add_argument('--window-tests',type=int,default=12_000)
    ap.add_argument('--witness',type=Path)
    args=ap.parse_args()
    if not (0<args.seconds<86400 and args.tests>0 and args.window_tests>0): ap.error('choose positive finite budgets (seconds < 86400)')
    rng=random.Random(args.seed); limit=Limits(args)
    states=choices=moves=0; smallest=16; gs=None; known=set(); count=0; not_steps=0
    while not limit.done():
        if gs is None or count>=30:
            gs,root=cover_formula(rng); known=set(); count=0; states+=1
        gs,root=schedule(gs,root,rng); values=simulate(gs)
        assert values[root]==TARGET
        opts=windows(gs,root)
        if not opts: gs=None; continue
        r,group=rng.choice(opts); delta=rng.choices([-1,0,1],[4,4,2 if len(gs)<18 else 0])[0]; choices+=1; count+=1
        limit.start(args.window_tests); neighbor=None; seen=set()
        try:
            for term in candidates(gs,root,values,r,group,rng,limit,delta):
                net,w=patch(gs,root,r,group,term)
                full=simulate(net)
                assert full[w]==TARGET, 'care-set substitution failed'
                core,core_out=reachable(net,w)
                smallest=min(smallest,len(core)); key=(tuple(core),core_out)
                if len(core)<=15:
                    result=witness(core,core_out)
                    output=json.dumps(result,separators=(',',':'))
                    if args.witness: args.witness.write_text(output+'\n')
                    print('SAT: all 512 scalar rows verified'); print(output); return
                if key in seen: continue
                seen.add(key)
                if len(core)<len(gs): neighbor=(core,core_out,key); break
                if delta>=0 and len(core)<=len(gs)+delta and key not in known and (core,core_out)!=(gs,root):
                    if neighbor is None or not rng.randrange(5): neighbor=(core,core_out,key)
                if len(seen)>=10: break
        except WindowEnd: pass
        if neighbor is not None:
            gs,root,key=neighbor; known.add(key); moves+=1; not_steps+=int(any(op==2 for op,_,_ in gs))
    report={'status':'bounded search finished without assigned witness','states_with_not':not_steps,
            'seed':args.seed,'starts':states,'windows':choices,'moves':moves,
            'truth_mask_tests':limit.tests,'smallest_seen':smallest}
    print(json.dumps(report))


if __name__=='__main__': main()
