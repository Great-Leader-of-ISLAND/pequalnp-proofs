#!/usr/bin/env python3
"""Render untrusted numeric DAG tables; Lean rechecks every accepted certificate and transition."""
import argparse
import collections
import json
import math
import re
from pathlib import Path

def branches(var,pairs,default):
    if not pairs:return default
    if len(pairs)==1:return pairs[0][1]
    m=len(pairs)//2
    return f'(if {var} < {pairs[m][0]} then {branches(var,pairs[:m],default)} else {branches(var,pairs[m:],default)})'

def pack(values,bits):
    assert all(0<=v<1<<bits for v in values)
    return sum(v<<(i*bits) for i,v in enumerate(values))

def packed_table(name,values):
    bits=max(1,max(values,default=0).bit_length())
    blocks=[(i//8,hex(pack(values[i:i+8],bits))) for i in range(0,len(values),8)]
    return f'def {name} (i : Nat) := let c := i/8; stored {bits} (i%8) '+branches('c',blocks,'0')+'\n'

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('trace',type=Path);p.add_argument('base',type=Path);p.add_argument('output',type=Path);p.add_argument('--samples',type=int,default=0,help='Emit diagnostic node lemmas per tag instead of the full lower bound.');p.add_argument('--block',type=int,default=24);p.add_argument('--index',action='store_true');a=p.parse_args()
    D=json.loads(a.trace.read_text())
    if not D['complete'] and not a.samples:raise ValueError('incomplete trace')
    src=a.base.read_text()
    inputs=[tuple(int(v,16) for v in rr) for rr in re.findall(r'def x[0-6] : Sig := \((0x[0-9a-f]+),(0x[0-9a-f]+)\)',src)]
    assert len(inputs)==7
    out=['import PEqualNP.CoThetaWholeBase','namespace CoThetaWholeBase.CertifiedData','open PEqualNP.CircuitLowerBounds','set_option maxRecDepth 30000','set_option maxHeartbeats 0']
    pos={};neg={}
    for i in reversed(range(256)):
        for side,table in enumerate((pos,neg)):
            row=sum(((s[side]>>i)&1)<<j for j,s in enumerate(inputs));table[row]=i
    assert len(pos)==101 and len(neg)==27 and not pos.keys()&neg.keys()
    coords=[(256+pos[r] if r in pos else neg[r]) for r in range(128)]
    out += [packed_table('rowCodes',coords),'def rowAt (r : Nat) : Row := let z := rowCodes r; (decide (z ≥ 256),Fin.ofNat 256 z)']
    values=[];mask=(1<<256)-1
    for op,u,v in D['recipes']:
        if op=='atom':s=inputs[u]
        elif op=='not':s=tuple(x^mask for x in values[u])
        else:s=tuple((x|y if op=='or' else x&y) for x,y in zip(values[u],values[v]))
        values.append(s)
    bits=(len(values)+1).bit_length()
    out.extend([packed_table('sigP',[p for p,n in values]),packed_table('sigN',[n for p,n in values]),'def s (i : Nat) : Sig := (sigP i,sigN i)'])
    def group(rs,ai,bi):
        code=[]
        for r in rs:
            side=0 if r in pos else 1;col=coords[r]%256
            xy=(((values[ai][side]>>col)&1)<<1)|((values[bi][side]>>col)&1)
            code.append(1+4*r+xy)
        assert 1<=len(code)<=4
        return pack(code,10)
    def cert(tag,data):
        if tag=='step':return 0
        if tag=='ordinary':
            wire={i:i for i in range(7)};words=[]
            for i in data:
                op,u,v=D['recipes'][i];code={'and':1,'or':2,'not':3}[op]
                words.append(code+4*wire[u]+(128*wire[v] if v is not None else 0));wire[i]=len(wire)
            return 1+4*pack(words,12)
        if tag=='tree':return 3+4*sum(1<<r for r in data)
        ai,bi,g,h=data
        return 2+4*(ai+(bi<<bits)+(group(g,ai,bi)<<(2*bits))+(group(h,ai,bi)<<(2*bits+40)))
    levels=[];prime=2147483647
    for salt in range(317,1000):
        raw=[pow((p%prime*257+n%prime+salt)%prime,3,prime) for p,n in values]
        def hashing(ws):return sum(raw[i] for i in ws)%prime
        if all(all(len(g)==len({hashing(ws) for _,ws,_,_ in g}) for g in ([s for s in layer if s[0]==t] for t in {s[0] for s in layer})) for layer in D['levels']):break
    else:raise ValueError('no hash salt')
    out.extend([f'def key (s : Sig) : Nat := (((s.1.toNat%{prime})*257+s.2.toNat%{prime}+{salt})%{prime})^3%{prime}',f'def hash (v : List Sig) := (v.foldl (fun z a => z+key a) 0)%{prime}'])
    reps=collections.defaultdict(list)
    for level,states in enumerate(D['levels']):
        k=10-level;groups=[]
        for t in range(1+max(s[0] for s in states)):
            g=sorted((s for s in states if s[0]==t),key=lambda s:hashing(s[1]))
            states_packed=[];certs=[];keys=[]
            for i,(_,ws,tag,payload) in enumerate(g):
                states_packed.append(pack([j+1 for j in ws],bits));certs.append(cert(tag,payload));keys.append(hashing(ws))
                if len(reps[tag])<a.samples:reps[tag].append((k,t,i))
            for prefix,arr in [('front',states_packed),('code',certs),('keytab',keys)]:
                out.append(packed_table(f'{prefix}_{k}_{t}',arr))
            groups.append(len(g))
        levels.append(groups);ts=list(range(len(groups)))
        for field,prefix in [('data','front'),('codes','code'),('hashes','keytab')]:
            out.append(f'def {field}{k} (t i : Nat) := '+branches('t',[(t,f'{prefix}_{k}_{t} i') for t in ts],'0'))
        out.extend([f'def count{k} (t : Nat) := if t < {len(ts)} then '+branches('t',[(t,str(n)) for t,n in enumerate(groups)],'0')+' else 0',f'def L{k} : Layer where',f'  count := count{k}',f'  state t i := (words {bits} 11 (data{k} t i)).map fun j => s (j-1)',f'  pick t v := seek (hashes{k} t) (hash v) {max(groups).bit_length()+1} 0 (count{k} t)'])
    for d,groups in reversed(list(enumerate(levels))):
        k=10-d;nxt='emptyLayer' if d+1==len(levels) else f'L{k-1}'
        out.append(f'def pass{k} (t i : Nat) := nodeTest {nxt} {k-1} t (L{k}.state t i) (readCert s {bits} rowAt (codes{k} t i))')
        if a.samples:continue
        for t,n in enumerate(groups):
            spans=[]
            for i in range(0,n,a.block):
                stop=min(n,i+a.block)
                out.append(f'private theorem blk_{k}_{t}_{i} : span (pass{k} {t}) {stop-i} {i}=true := by decide +kernel')
                spans.append((i,stop,f'span_ok blk_{k}_{t}_{i} i (by omega) (by omega)'))
            def subproof(op):
                if len(op)==1:return op[0][2]
                m=len(op)//2
                return f'if h : i < {op[m][0]} then {subproof(op[:m])} else {subproof(op[m:])}'
            out.append(f'private theorem done_{k}_{t} (i : Nat) (hi : i<{n}) : pass{k} {t} i=true := '+(subproof(spans) if spans else 'by omega'))
        out.append(f'theorem good{k} : L{k}.Valid {k} := by\n  intro t i hi\n  have ht : t < {len(groups)} := by\n    by_contra hx\n    simp [L{k},count{k},hx] at hi\n  have hc : pass{k} t i = true := by\n    interval_cases t')
        out.extend(f'    · exact done_{k}_{t} i hi' for t in range(len(groups)))
        nxtvalid=f'(emptyLayer_ok {k-1})' if nxt=='emptyLayer' else f'good{k-1}'
        out.append(f'  exact nodeTest_sound {nxtvalid} hc')
    if a.samples:
        for tag,ls in reps.items():
            for k,t,i in ls:out.append(f'theorem probe_{tag}_{k}_{t}_{i} : pass{k} {t} {i}=true := by decide +kernel')
    if not a.samples or a.index:
        for j in (0,2,3):
            out.append(f'theorem table_{j} : rootTable {j} L10 = true := by decide +kernel')
            if not a.samples:out.append(f'theorem lower_{j} (C : Circuit) (h : C.size≤10) (f : PEqualNP.MetaComplexity.FanInTwo C) : ¬∀ x : Fin 7 → Bool, C.eval (List.ofFn x ++ [!(x ({j}:Fin 7))]) = theta x := exclusion_from_layers {j} L10 good10 table_{j} C h f')
    out.append('end CoThetaWholeBase.CertifiedData')
    a.output.write_text('\n'.join(out)+'\n')
    print('rendered',a.output.stat().st_size,'bytes',len(values),'signals',levels,'salt',salt,'samples',dict(reps))
if __name__=='__main__':main()
