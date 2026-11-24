#!/usr/bin/env python3
"""Fixed-outside window synthesis for the thirteen Z/13 line disjunctions.

For k selected lines, the other 13-k lines each keep three paid binary ORs.
The outside circuit is emitted in full, even if no window output borrows it.
Target lines 0,1 share one point. Nine outside lines give distinct mixed
pairs a OR b between their two sets of three private points. Reorder the
first OR of each such outside line to compute exactly that mixed pair.
Inside mode exposes only raw points and paid wires supported on the union
of selected lines. Testing its 2^|union| assignments is exhaustive. All mode
exposes all raw and paid wires; its CEGAR starts with projected rows, checks
each model on all 8192 assignments, and adds genuine counterexamples.

Every window gate in the encoding is binary AND/OR or unary NOT. Normalize a
raw window forward by constant propagation and copy forwarding; a missing
pin, empty gate, invalid reference or repeated pin yields a constant or copy
in exactly the official semantics. A NOT reads only the first pin. All desired
outputs are nonconstant, so constant wires can be dropped. Pad a short window
with unused OR(x,x); output selectors can choose earlier wires. This proves
exhaustiveness for the chosen fixed outside circuit and allowed terminals.
An UNSAT outcome does not cover other outside circuits. Default lines 0,1,2,4 have no concurrent triple. Their private points are
peeled, resynthesizing the six-coordinate core and charging four recovery ORs.
"""
import argparse
from itertools import combinations_with_replacement
import json
from pathlib import Path
import subprocess
import tempfile
import time

N = 13
LINES = tuple(tuple(sorted((w+d)%N for d in (0,1,3,9))) for w in range(N))
ALL = (1 << (1 << N)) - 1
INPUTS = tuple(sum(1<<r for r in range(1<<N) if r>>v&1) for v in range(N))
TARGETS = tuple(INPUTS[a]|INPUTS[b]|INPUTS[c]|INPUTS[d] for a,b,c,d in LINES)


def outside(lines, mode, peel=False):
    union=set().union(*(LINES[w] for w in lines))
    active={v for v in union if not peel or sum(v in LINES[w] for w in lines)>=2}
    if any(not (set(LINES[w]) & active) for w in lines):
        raise ValueError('private-point peeling needs at least two intersecting lines')
    gates=[]; support=[{i} for i in range(N)]; outputs={}
    def join(a,b):
        gates.append(('or',a,b)); support.append(support[a]|support[b]); return N+len(gates)-1
    for w,vs in enumerate(LINES):
        if w in lines: continue
        if len(lines)>=2:
            left,=set(vs)&set(LINES[lines[0]]); right,=set(vs)&set(LINES[lines[1]])
        else: left=right=None
        if peel:
            a,b,c,d=sorted(vs,key=lambda u:(u not in active,u))
        elif left!=right:
            a,b=sorted((left,right)); c,d=sorted(set(vs)-{a,b})
        else:
            a,b,c,d=sorted(vs,key=lambda u:(u not in active,u))
        outputs[w]=join(join(a,b),join(c,d))
    terminals=[i for i,s in enumerate(support) if mode=='all' or s<=active]
    return gates,outputs,terminals,support,active


def raw_values(gates):
    vals=list(INPUTS)
    for gate in gates:
        op,*ins=gate
        if op not in ('or','and','not') or not 1<=len(ins)<=2: raise ValueError('invalid gate')
        if any(w<0 or w>=len(vals) for w in ins): raise ValueError('invalid backward pin')
        if op=='not':
            if len(ins)!=1: raise ValueError('NOT must be unary in the normal form')
            bit=ALL^vals[ins[0]]
        else:
            if len(ins)!=2: raise ValueError('AND/OR must be binary in the normal form')
            a,b=ins;bit=vals[a]&vals[b] if op=='and' else vals[a]|vals[b]
        vals.append(bit)
    return vals


def full_replay(gates, outs):
    if len(outs)!=N or sum(g[0]=='not' for g in gates)>1: raise ValueError('bad output or NOT count')
    vals=raw_values(gates)
    if any(w<0 or w>=len(vals) for w in outs): raise ValueError('bad output wire')
    return [vals[o]^expected for o,expected in zip(outs,TARGETS)]


def baseline(lines, outside_gates, donors, control, active):
    gates=[]; outs=[]; offset=N+len(outside_gates)
    def add(op,*ws):
        gates.append((op,*ws)); return offset+len(gates)-1
    alias=None
    if control=='borrow-not':
        if len(lines)<2: raise ValueError('borrow-not requires two or more window lines')
        for a in set(LINES[lines[0]]) & active:
            wire=None
            for b in (set(LINES[lines[1]])-set(LINES[lines[0]])) & active:
                wire=next((N+i for i,g in enumerate(outside_gates)
                           if N+i in donors and g[0]=='or' and set(g[1:])=={a,b}),None)
                if wire is not None: break
            if wire is not None: break
        else: raise ValueError('no suitable mixed paid OR for this control')
        nb=add('not',b);disjunction=add('or',a,nb)
        alias=(a,add('and',wire,disjunction))
    for i,w in enumerate(lines):
        vs=[alias[1] if alias and i==0 and v==alias[0] else v for v in LINES[w] if v in active]
        while len(vs)>1:
            vs=[add('or',vs[j],vs[j+1]) if j+1<len(vs) else vs[j] for j in range(0,len(vs),2)]
        outs.append(vs[0])
    return gates,outs


def projected(active):
    bits=sorted(active)
    return [sum(((v>>j)&1)<<i for j,i in enumerate(bits)) for v in range(1<<len(bits))]


class CNF:
    def __init__(self,lines,outside_gates,donors,size,rows,active,control=None):
        self.n=0;self.clauses=[];self.control=control;self.model=[False] if control else None
        self.one=self.var(True);self.clauses.append([self.one])
        self.ops=[];self.pins=[];self.outs=[];self.avail=list(donors);self.offset=N+len(outside_gates)
        self.fixed_values=raw_values(outside_gates);self.lines=lines
        self.targets={}
        for w in lines:
            bits=0
            for v in set(LINES[w]) & active:bits|=INPUTS[v]
            self.targets[w]=bits
        for i in range(size):
            g=control[0][i] if control else None
            op=self.choices(3,('and','or','not').index(g[0]) if g else None)[0]
            ws=self.avail+list(range(self.offset,self.offset+i))
            wanted=sorted(g[1:]) if g else []
            if g and len(wanted)==1: wanted.append(wanted[0])
            pins=[];prefix=[]
            for w in (wanted if g else (None,None)):
                bits,pre=self.choices(len(ws),ws.index(w) if g else None);pins.append(bits);prefix.append(pre)
            for lp,rp in zip(*prefix):self.add(-rp,lp)
            for a,b in zip(*pins):self.add(-op[2],-a,b)  # NOT ignores the second mux, choose same source
            for previous in self.ops:self.add(-op[2],-previous[2])
            self.ops.append(op);self.pins.append((ws,*pins))
        ws=self.avail+list(range(self.offset,self.offset+size))
        self.output_wires=ws
        for i,w in enumerate(lines):
            self.outs.append(self.choices(len(ws),ws.index(control[1][i]) if control else None)[0])
        for row in rows:self.row(row)

    def var(self,val=None):
        self.n+=1
        if self.control:
            if not isinstance(val,bool):raise ValueError('incomplete control assignment')
            self.model.append(val)
        return self.n

    def value(self,x):return self.model[abs(x)]==(x>0)

    def add(self,*xs):
        if self.one not in xs:self.clauses.append(tuple(x for x in xs if x!=-self.one))

    def choices(self,n,selected):
        flags=[];prefix=[]
        for i in range(n):
            bit=self.var(i==selected)
            if flags:
                prev=prefix[-1];p=self.var(self.value(prev) or self.value(bit) if self.control else None)
                self.add(-prev,-bit);self.add(-prev,p);self.add(-bit,p);self.add(-p,prev,bit)
            else:p=bit
            flags.append(bit);prefix.append(p)
        self.add(prefix[-1])
        return flags,prefix

    def mux(self,flags,vals):
        v=self.var(any(self.value(f) and self.value(w) for f,w in zip(flags,vals)) if self.control else None)
        for f,w in zip(flags,vals):self.add(-f,-v,w);self.add(-f,v,-w)
        return v

    def row(self,row):
        acc=[self.one if self.fixed_values[w]>>row&1 else -self.one for w in self.avail]
        for op,(_,left,right) in zip(self.ops,self.pins):
            a,b=self.mux(left,acc),self.mux(right,acc)
            if self.control:
                av,bv=self.value(a),self.value(b)
                value=(av and bv) if self.value(op[0]) else ((av or bv) if self.value(op[1]) else not av)
            else:value=None
            c=self.var(value);u,v,t=op
            self.add(-u,-c,a);self.add(-u,-c,b);self.add(-u,c,-a,-b)
            self.add(-v,c,-a);self.add(-v,c,-b);self.add(-v,-c,a,b)
            self.add(-t,-c,-a);self.add(-t,c,a)
            acc.append(c)
        for w,flags in zip(self.lines,self.outs):
            truth=bool(self.targets[w]>>row&1)
            for f,a in zip(flags,acc):self.add(-f,a if truth else -a)

    def pin(self):
        for op,(_,l,r) in zip(self.ops,self.pins):
            for group in (op,l,r):self.add(next(x for x in group if self.value(x)))
        for group in self.outs:self.add(next(x for x in group if self.value(x)))

    def decode(self,model):
        truth=set(model)
        def index(flags):
            hits=[i for i,f in enumerate(flags) if f in truth]
            if len(hits)!=1: raise ValueError('missing or ambiguous solver selection')
            return hits[0]
        gs=[]
        for op,(ws,l,r) in zip(self.ops,self.pins):
            name=('and','or','not')[index(op)];pins=[ws[index(l)],ws[index(r)]]
            gs.append((name,*(pins[:1] if name=='not' else pins)))
        return gs,[self.output_wires[index(fs)] for fs in self.outs]

    def write(self,path):
        with path.open('w',encoding='ascii') as f:
            print('p cnf',self.n,len(self.clauses),file=f)
            for c in self.clauses:print(*c,0,file=f)


def combined(lines,og,fixed,window,roots,active):
    outs=dict(fixed);gates=og+window
    for w,base in zip(lines,roots):
        for v in LINES[w]:
            if v not in active:
                gates.append(('or',base,v));base=N+len(gates)-1
        outs[w]=base
    return gates,[outs[w] for w in range(N)]


def micro_reference():
    # Exhaust all normalized programs of at most two gates on four sources,
    # including repeated binary pins, one NOT and arbitrary output.
    raw=[sum(1<<r for r in range(16) if r>>i&1) for i in range(4)];target=65534
    def children(values,not_used):
        for a,b in combinations_with_replacement(values,2):
            yield a|b,not_used;yield a&b,not_used
        if not not_used:
            for a in values:yield 65535^a,True
    tried=0
    for v,n in children(raw,False):
        assert target not in raw+[v]
        for w,_ in children(raw+[v],n):
            tried+=1;assert w!=target
    assert raw[0]|raw[1]|raw[2]|raw[3]==target
    return tried


def run_solver(binary,cnf,timeout,proof):
    cmd=[binary,'-q','-t',str(timeout),str(cnf)]
    if proof:
        if proof.exists():raise ValueError('proof path already exists')
        cmd.append(str(proof))
    try:res=subprocess.run(cmd,stdin=subprocess.DEVNULL,capture_output=True,text=True,timeout=timeout+8)
    except subprocess.TimeoutExpired:return 'UNKNOWN',[]
    statuses=[x.strip() for x in res.stdout.splitlines() if x.startswith('s ')]
    if res.returncode==10 and statuses==['s SATISFIABLE']:
        return 'SAT',[int(t) for line in res.stdout.splitlines() if line.startswith('v ') for t in line.split()[1:] if t!='0']
    if res.returncode==20 and statuses==['s UNSATISFIABLE']:return 'UNSAT',[]
    if res.returncode in (0,124) and statuses in ([],['s UNKNOWN'],['s INDETERMINATE']):return 'UNKNOWN',[]
    raise RuntimeError('CaDiCaL failed: exit '+str(res.returncode)+', status '+str(statuses))


def calibration(lines,shape,peel=False):
    og,fixed,donors,_,active=outside(lines,'inside',peel)
    g,roots=baseline(lines,og,donors,shape,active)
    enc=CNF(lines,og,donors,len(g),projected(active),active,(g,roots));enc.pin()
    assert all(any(enc.value(i) for i in cl) for cl in enc.clauses)
    model=[i if truth else -i for i,truth in enumerate(enc.model) if i]
    out=combined(lines,og,fixed,*enc.decode(model),active);assert not any(full_replay(*out))
    print('control',shape,'lines',lines,'outside',len(og),'window',len(g),'recovery',len(out[0])-len(og)-len(g),'total',len(out[0]),
          'NOTs',sum(t[0]=='not' for t in out[0]),'all 8192 rows verified')


def main():
    p=argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument('--lines',default='0,1,2,4',help='ordered comma-separated target line indices')
    p.add_argument('--borrow',choices=('inside','all'),default='inside')
    p.add_argument('--peel-private',dest='peel',action='store_true',help='separate and pay one recovery OR for each private point')
    p.add_argument('--whole-window',dest='peel',action='store_false',help='synthesize full line outputs directly')
    p.set_defaults(peel=None)
    p.add_argument('--gates',type=int,help='searched gates, additional to fixed outside and recovery gates')
    p.add_argument('--control',choices=('baseline','borrow-not'),help='pin an explicitly over-budget calibration')
    p.add_argument('--self-test',action='store_true')
    p.add_argument('--cnf',type=Path,help='DIMACS, overwritten with the latest CEGAR row set')
    p.add_argument('--solver',help='CaDiCaL executable')
    p.add_argument('--seconds',type=int,default=300,help='total solver-time wall limit')
    p.add_argument('--rounds',type=int,default=32)
    p.add_argument('--all-rows',action='store_true',help='instantiate entire truth table immediately')
    p.add_argument('--proof',type=Path,help='fresh DRAT path per round (suffix .rN)')
    p.add_argument('--witness',type=Path)
    a=p.parse_args()
    if a.self_test:
        print('one-line exact reference: no OR4 with <=2 gates;',micro_reference(),'two-gate programs tested')
        calibration([0],'baseline');calibration([0,1],'baseline');calibration([0,1],'borrow-not');calibration([0,1,2],'baseline');calibration([0,1,2,4],'baseline',True);return
    try:lines=[int(x) for x in a.lines.split(',')]
    except ValueError:p.error('invalid lines')
    if not lines or len(set(lines))!=len(lines) or any(not 0<=i<N for i in lines):p.error('distinct lines from 0 to 12 required')
    if a.seconds<1 or a.rounds<1:p.error('positive time and round limits required')
    if a.proof and not (a.solver and a.cnf):p.error('--proof needs --solver and persistent --cnf')
    peel=a.peel if a.peel is not None else len(lines)>=4
    og,fixed,donors,support,active=outside(lines,a.borrow,peel)
    recovery=sum(v not in active for w in lines for v in LINES[w])
    ctrl=baseline(lines,og,donors,a.control,active) if a.control else None
    size=a.gates if a.gates is not None else (len(ctrl[0]) if ctrl else 3*len(lines)-1-recovery)
    if size<0 or ctrl and size!=len(ctrl[0]):p.error('gate budget conflicts with calibration')
    if not (a.cnf or a.solver or ctrl):p.error('provide --cnf, --solver or --control')
    base=projected(active)
    outside_bits=sum(1<<p for p in range(N) if p not in active)
    rows=(list(range(1<<N)) if a.all_rows else
          (base if a.borrow=='inside' else sorted(set(base+[r|outside_bits for r in base]))))
    done=set(rows)
    print('window lines',lines,'paid outside gates',len(og),'free boundary wires',len(donors),
          'including paid outside wires',sum(w>=N for w in donors),'window slots',size,'recovery ORs',recovery,'total',len(og)+size+recovery,flush=True)
    enc=CNF(lines,og,donors,size,rows,active,ctrl)
    if ctrl:
        enc.pin()
        assert all(any(enc.value(i) for i in cl) for cl in enc.clauses)
        assert not any(full_replay(*combined(lines,og,fixed,*ctrl,active)))
        print('pinned calibration passes every active clause and all 8192 raw assignments',flush=True)
    if not a.cnf and not a.solver:return
    with tempfile.TemporaryDirectory() as td:
        path=a.cnf or Path(td)/'plane.cnf';deadline=time.monotonic()+a.seconds
        for k in range(1,a.rounds+1):
            enc.write(path);print('round',k,'rows',len(done),'variables',enc.n,'clauses',len(enc.clauses),flush=True)
            if not a.solver:return
            left=int(deadline-time.monotonic())
            if left<1:break
            proof=Path(str(a.proof)+'.r'+str(k)) if a.proof else None
            status,model=run_solver(a.solver,path,left,proof)
            if status=='UNSAT':
                if ctrl:raise RuntimeError('solver rejected verified positive control')
                print('UNSAT reported, fixed outside/window only; independent certificate checking still required',flush=True);return
            if status=='UNKNOWN':break
            window,roots=enc.decode(model);gates,outs=combined(lines,og,fixed,window,roots,active)
            errors=full_replay(gates,outs)
            if not any(errors):
                report={'gates':[{'op':g[0],'inputs':list(g[1:])} for g in gates],'out':outs}
                print('SAT verified all 13 outputs on all 8192 inputs, total gates',len(gates),flush=True)
                if a.witness:a.witness.write_text(json.dumps(report)+'\n')
                else:print(json.dumps(report))
                return
            fresh=set()
            for mask in errors:
                for _ in range(6):
                    if not mask:break
                    bit=mask&-mask;fresh.add(bit.bit_length()-1);mask^=bit
            if fresh&done or not fresh:raise RuntimeError('model disagrees with an encoded assignment')
            for row in sorted(fresh):enc.row(row)
            done.update(fresh)
        print('UNKNOWN: time or CEGAR round limit',flush=True)


if __name__=='__main__':main()
