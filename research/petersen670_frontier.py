#!/usr/bin/env python3
"""Bounded live-frontier search for L-meta-670. Default prints first-layer counts.
See petersen670-frontier.md for completeness, pruning and certificate limits."""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import time

from petersen670 import N, K, EDGES, target, counterexamples, cover_control


class Bounded(Exception):
    pass


class Search:
    def __init__(self, pair_mode, cofactor=False):
        neg = [r for r in range(1 << N) if not target(r)]
        pos = [r for r in range(1 << N) if target(r)]
        if pair_mode == 'all':
            pairs = list(product(pos,neg))
        else:
            pairs = [(q | (1 << v), q) for q in neg for v in range(N)
                     if not q & (1 << v) and target(q | (1 << v))]
            seen_pos = {p for p,_ in pairs}
            seen_neg = {q for _,q in pairs}
            pairs.extend((p,neg[0]) for p in pos if p not in seen_pos)
            pairs.extend((pos[0],q) for q in neg if q not in seen_neg)
        assert set(pos) == {p for p,_ in pairs} and set(neg) == {q for _,q in pairs}
        self.width = len(pairs)
        self.low = (1 << self.width) - 1
        self.mask = (self.low << self.width) | self.low
        self.goal = self.low << self.width
        def column(v):
            # Build little-endian packed words without repeated long-int addition.
            halves = []
            for side in (0,1):
                buf = bytearray((self.width+7)//8)
                for i,pair in enumerate(pairs):
                    if pair[side] & (1<<v): buf[i//8] |= 1<<(i%8)
                halves.append(int.from_bytes(buf,'little'))
            return (halves[0]<<self.width) | halves[1]
        self.inputs = tuple(column(v) for v in range(N))
        self.root = tuple(sorted(self.inputs))
        self.cofactor = cofactor
        self.off = tuple(self.mask ^ self.inputs[v] for v in (4,6,7))
        self.free = tuple({0,m} | {a&m for a in self.inputs} for m in self.off)

    def orient(self,w,directed):
        positive,negative = w>>self.width,w&self.low
        return (positive & ~negative) if directed else (positive ^ negative)

    def viable(self,ws,k,t):
        if len(ws)+t>k+1 or not 0<=t<=k: return False
        covered = 0
        for w in ws:
            covered |= self.orient(w,t==0)
        return covered == self.low

    def losses(self,c,pins,left):
        if not self.cofactor: return left
        new = []
        for i,m in enumerate(self.off):
            co = c&m
            # Under x_v=0 replace the gate by its constant, primary, or operand.
            lost = co in self.free[i] or any(co == (a&m) for a in pins)
            if lost and left[i]==0: return None
            new.append(left[i]-int(lost))
        return tuple(new)

    def next(self,ws,k,t,loss):
        if not k: return
        live = set(ws)
        def edits(op,pins,z,tn):
            if z in live or z in (0,self.mask): return
            ln = self.losses(z,pins,loss)
            if ln is None: return
            base = live.difference(pins)
            for retain in range(1<<len(pins)):
                size = len(base)+1+bin(retain).count('1')
                if size+tn>k: continue
                child=tuple(sorted((*base,z,*(a for i,a in enumerate(pins) if retain&(1<<i)))))
                if self.viable(child,k-1,tn):
                    yield child,tn,ln,(op,pins,z)
        if t:
            for a in ws:
                yield from edits('not',(a,),self.mask^a,t-1)
        if k>t:
            for a,b in combinations(ws,2):
                yield from edits('and',(a,b),a&b,t)
                yield from edits('or',(a,b),a|b,t)

    def witness(self,path):
        wires = {w:i for i,w in enumerate(self.inputs)}
        gates = []
        for op,pins,z in path:
            gates.append({'op':op,'inputs':[wires[a] for a in pins]})
            wires[z] = N + len(gates)-1
        c={'gates':gates,'output':wires[self.goal]}
        if counterexamples(c): raise AssertionError('full-table witness check failed')
        return c

    def known_control(self):
        # Replay the known 16-gate formula retaining exactly signals used later.
        c=cover_control()
        vals=list(self.inputs)
        last_use={}
        for j,g in enumerate(c['gates']):
            for v in g['inputs']: last_use[v]=j
            a,b=(vals[v] for v in g['inputs'])
            vals.append(a&b if g['op']=='and' else a|b)
        assert vals[c['output']]==self.goal
        ws=self.root
        # The cofactor loss budget scales to 16-13 in this calibration only.
        loss=(3,)*3 if self.cofactor else ()
        for j,g in enumerate(c['gates']):
            z=vals[N+j]
            future = {vals[v] for v in range(N+j+1) if last_use.get(v,-1)>j}
            if j==len(c['gates'])-1: future={self.goal}
            goal_ws=tuple(sorted(future))
            choices = (item for item in self.next(ws,16-j,0,loss)
                       if item[0]==goal_ws and item[3][2]==z)
            chosen=next(choices,None)
            assert chosen is not None, ('control transition missing',j)
            ws,_,loss,_=chosen
        return len(c['gates'])

    def search(self,not_counts,max_nodes,seconds,memo_max):
        end=time.monotonic()+seconds; count=0; path=[]; found=None
        # Cache only completed failures, using full keys and bounded eviction.
        @lru_cache(maxsize=memo_max)
        def visit(ws,k,t,loss):
            nonlocal count,found
            count+=1
            if count>max_nodes or time.monotonic()>=end: raise Bounded
            if self.goal in ws and t==0:
                found=self.witness(path); return True
            if not self.viable(ws,k,t):
                return False
            for ws2,t2,loss2,op in self.next(ws,k,t,loss):
                path.append(op)
                if visit(ws2,k-1,t2,loss2): return True
                path.pop()
            return False
        done=[]
        for t in not_counts:
            try:
                if visit(self.root,K,t,(2,)*3 if self.cofactor else ()):
                    return 'VERIFIED_WITNESS',done,t,count,found
            except Bounded:
                return 'BUDGET_LIMIT',done,t,count,None
            done.append(t)
        return 'NO_WITNESS_IN_COMPLETED_BUCKETS',done,None,count,None


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--pairs',choices=('boundary','all'),default='boundary')
    ap.add_argument('--cofactor',action='store_true',help='use the 13-gate L-meta-1007 deletion bound')
    ap.add_argument('--not-count',type=int,choices=range(8))
    ap.add_argument('--paper-bound',action='store_true',help='restrict to at most 3 NOTs; see separate 12-binary-gate proof')
    ap.add_argument('--search',action='store_true')
    ap.add_argument('--seconds',type=float,default=5)
    ap.add_argument('--nodes',type=int,default=2000)
    ap.add_argument('--memo',type=int,default=1000)
    ap.add_argument('--control',action='store_true')
    ap.add_argument('--witness',type=Path)
    a=ap.parse_args()
    if not (0<a.seconds<=86400 and a.nodes>0 and a.memo>=0):
        ap.error('bounded positive time and node budgets required')
    s=Search(a.pairs,a.cofactor)
    print(f'rows=512 pairs={s.width} gate_bound={K} distinct_inputs={len(set(s.inputs))} cofactor={a.cofactor}')
    if a.control:
        print('verified live transitions in size-16 positive control:',s.known_control())
    ts=list(range(4 if a.paper_bound else 8)) if a.not_count is None else [a.not_count]
    if a.paper_bound and a.not_count is not None and a.not_count>3:
        ap.error('--paper-bound conflicts with a NOT count above 3')
    if not a.search:
        for t in ts:
            counts=Counter(op for _,_,_,(op,_,_) in s.next(s.root,K,t,(2,)*3 if a.cofactor else ()))
            print('not_budget',t,'first_transitions_after_pruning',dict(sorted(counts.items())))
        return
    status,done,current,n,c=s.search(ts,a.nodes,a.seconds,a.memo)
    print(status,'complete_not_buckets',done,'current',current,'visited',n)
    if c is not None:
        result=json.dumps(c,separators=(',',':'))
        if a.witness: a.witness.write_text(result+'\n')
        print(result)


if __name__=='__main__': main()
