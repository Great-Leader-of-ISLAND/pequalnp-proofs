"""Current L-meta-1342 shard 1: at least three distinct ANDs firing on independent rows.
Every shorter circuit pads to the budget by appending empty ORs without changing the
output or its junk count. Bad reads become a fixed false port. The 40 boundary rows
are sufficient for monotone circuits; every result is replayed on all 2048 rows.
"""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
from search1343v3 import Encoding, POINTS, EDGE_ROWS, edge_value, maximal_independent, run_cadical

MIS=[r for r in range(1<<POINTS) if maximal_independent(r)]
ROWS=list(EDGE_ROWS)+MIS
assert len(EDGE_ROWS)==16 and len(MIS)==24

class ThreeJunk(Encoding):
    def either(self, xs):
        h=self.new()
        for x in xs: self.add(-x,h)
        self.add(-h,*xs)
        return h

    def __init__(self,n):
        self.nvars=0; self.clauses=[]; self.true=self.new(); self.clauses.append([self.true])
        self.gate_data=[]; self.size=n; self.bad=POINTS+n; self.omit=self.bad+1
        values=[[self.true if row>>i&1 else -self.true for i in range(POINTS)] for row in ROWS]
        at_least=[self.true,-self.true,-self.true,-self.true]
        row_pins=[[] for _ in ROWS]
        for j in range(n):
            op=self.new()
            wires=list(range(POINTS+j))+[self.bad,self.omit]
            left,lp=self.one_hot(len(wires));right,rp=self.one_hot(len(wires))
            for x,y in zip(lp,rp): self.add(-y,x)
            self.gate_data.append((op,wires,left,right))
            fire=[]
            for r,ws in enumerate(values):
                a,b,z=self.new(),self.new(),self.new()
                row_pins[r].append((a,b))
                self.mux(left,ws+[-self.true,op],a); self.mux(right,ws+[-self.true,op],b)
                self.add(-op,-z,a); self.add(-op,-z,b); self.add(-op,z,-a,-b)
                self.add(op,z,-a); self.add(op,z,-b); self.add(op,-z,a,b)
                ws.append(z)
                if r>=len(EDGE_ROWS): fire.append(z)
            junk=self.conjunction(op,self.either(fire))
            at_least=[self.true]+[self.either([at_least[k],self.conjunction(junk,at_least[k-1])])
                                 for k in (1,2,3)]
        self.add(at_least[3])
        # Compatible AND choices for two distinct maximal independent sets must
        # disagree on at least one AND. The dual holds for two different minterms.
        self.separators(row_pins,range(len(EDGE_ROWS)),False)
        self.separators(row_pins,range(len(EDGE_ROWS),len(ROWS)),True)
        # Five or fewer ANDs with at least three junk ANDs were independently
        # excluded on all negative rows (graph1342-five-and.py --capacity-only).
        threshold=[self.true]+[-self.true]*6
        for op,_,_,_ in self.gate_data:
            threshold=[self.true]+[self.either([threshold[k],self.conjunction(op,threshold[k-1])])
                                   for k in range(1,7)]
        self.add(threshold[6])
        self.osel,_=self.one_hot(POINTS+n+1)
        for r,ws in enumerate(values):
            for p,bit in zip(self.osel,ws+[-self.true]):
                self.add(-p,bit if r<len(EDGE_ROWS) else -bit)

    def pin(self,c):
        assert len(c['gates'])==self.size
        for (op,ws,ls,rs),g in zip(self.gate_data,c['gates']):
            pins=sorted((g['inputs']+[self.omit,self.omit])[:2])
            self.add(op if g['op']=='and' else -op)
            self.add(ls[ws.index(pins[0])]);self.add(rs[ws.index(pins[1])])
        self.add(self.osel[c['output']])

    def decode_three(self,model):
        val=set(model)
        def choose(flags): return next(i for i,s in enumerate(flags) if s in val)
        gs=[]
        for op,ws,ls,rs in self.gate_data:
            pins=[ws[choose(ls)],ws[choose(rs)]]
            gs.append({'op':'and' if op in val else 'or','inputs':[p for p in pins if p!=self.omit]})
        return {'gates':gs,'output':choose(self.osel)}

def replay(c):
    junk=set()
    for row in range(1<<POINTS):
        ws=[bool(row>>i&1) for i in range(POINTS)]
        for j,g in enumerate(c['gates']):
            assert g['op'] in ('and','or') and len(g['inputs'])<=2
            arguments=[ws[i] if 0<=i<len(ws) else False for i in g['inputs']]
            z=all(arguments) if g['op']=='and' else any(arguments)
            if z and g['op']=='and' and not edge_value(row): junk.add(j)
            ws.append(z)
        out=c['output']; assert (ws[out] if 0<=out<len(ws) else False)==edge_value(row)
    return junk

def live_control(clean):
    # Three live absorptions x0 OR (x0 AND xq) = x0, with nonneighbors q.
    gs=[]; src=0
    for q in (1,2,3):
        gs.append({'op':'and','inputs':[src,q]})
        d=POINTS+len(gs)-1
        gs.append({'op':'or','inputs':[src,d]});src=d+1
    def renamed(i): return src if i==0 else i if i<POINTS else i+6
    for g in clean['gates']:
        gs.append({'op':g['op'],'inputs':[renamed(i) for i in g['inputs']]})
    return {'gates':gs,'output':renamed(clean['output'])}

def main():
    p=argparse.ArgumentParser();p.add_argument('--solver',required=True);p.add_argument('--checker',required=True)
    p.add_argument('--directory',type=Path,required=True);p.add_argument('--seconds',type=int,default=920)
    a=p.parse_args(); a.directory.mkdir(parents=True,exist_ok=False); path=a.directory/'c.cnf'
    assert replay(CLEAN)==set()
    live=live_control(CLEAN);assert replay(live)=={0,2,4}
    for c,expected in ((CLEAN,'UNSAT'),(live,'SAT')):
        e=ThreeJunk(len(c['gates']));e.pin(c);e.dimacs(path)
        status,model=run_cadical(path,a.solver,20,None);assert status==expected,(status,expected)
        if status=='SAT': assert replay(e.decode_three(model))=={0,2,4}
    print('Pinned clean 22 control rejected; pinned 28-gate positive control with exactly three live junk ANDs accepted, all 2048 rows.',flush=True)
    e=ThreeJunk(21);e.dimacs(path);proof=a.directory/'shard.drat'
    print('Full 21-gate raw search over 16 edges and 24 maximal independent rows:',e.nvars,len(e.clauses),flush=True)
    status,model=run_cadical(path,a.solver,a.seconds,proof); print('Solver',status,flush=True)
    if status=='SAT':
        c=e.decode_three(model); junk=replay(c);assert len(junk)>=3
        print('WITNESS',json.dumps(c), 'JUNK',sorted(junk),flush=True)
    if status=='UNSAT':
        run=subprocess.run([a.checker,str(path),str(proof)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
        assert run.returncode==0 and b's VERIFIED' in run.stdout
        print('DRAT VERIFIED for full shard',flush=True)

CLEAN={'gates': [{'op': 'or', 'inputs': [9, 10]}, {'op': 'and', 'inputs': [0, 11]}, {'op': 'or', 'inputs': [4, 8]}, {'op': 'and', 'inputs': [1, 13]}, {'op': 'or', 'inputs': [6, 7]}, {'op': 'and', 'inputs': [3, 15]}, {'op': 'or', 'inputs': [2, 8]}, {'op': 'or', 'inputs': [17, 9]}, {'op': 'and', 'inputs': [5, 18]}, {'op': 'or', 'inputs': [6, 9]}, {'op': 'and', 'inputs': [7, 20]}, {'op': 'or', 'inputs': [4, 9]}, {'op': 'and', 'inputs': [8, 22]}, {'op': 'or', 'inputs': [2, 4]}, {'op': 'or', 'inputs': [24, 6]}, {'op': 'and', 'inputs': [10, 25]}, {'op': 'or', 'inputs': [12, 14]}, {'op': 'or', 'inputs': [27, 16]}, {'op': 'or', 'inputs': [28, 19]}, {'op': 'or', 'inputs': [29, 21]}, {'op': 'or', 'inputs': [30, 23]}, {'op': 'or', 'inputs': [31, 26]}], 'output': 32}

if __name__=='__main__': main()
