"""Pack a native tight-state table by sharing proofs for one differing full wire."""
from collections import defaultdict
from functools import lru_cache
from pathlib import Path
from runpy import run_path
from time import monotonic
import argparse
import json
D=Path(__file__).parent
utility=run_path(str(D/'4482-table-lean.py'))
geometry,target=utility['geometry'],utility['target']
F=run_path(str(D/'4482-one-port.py'))['F']
rows=[(z,z|1<<b) for z in range(512) if not F[z] for b in range(9) if not (z>>b&1) and F[z|1<<b]]

def low(x):return (x&-x).bit_length()-1

@lru_cache(None)
def mark(w):
    p=sum(((w>>hi)&1)<<i for i,(_,hi) in enumerate(rows))
    n=sum(((w>>lo)&1)<<i for i,(lo,_) in enumerate(rows))
    return p,n,p^n

def union(a,b):
    return a[0]|b[0],a[1]&b[1],a[2]|b[2]

def check(box,core,max_fuel=128):
    n=len(box);m=target(n,core);bits=geometry(n);fuel=0
    while m and fuel<max_fuel:
        B=low(m);es=(1<<258)-1;inside=[]
        for i,(p,q,d) in enumerate(box):
            if B>>i&1:inside.append((p,q))
            else:es&=~d
        def choose(k,p,q):
            if not p or not q:return None
            if k==len(inside):return low(p),low(q)
            a,b=inside[k]
            return choose(k+1,p&~a,q) or choose(k+1,p&a,q&b)
        hint=choose(0,es,es)
        if not hint:return None
        e,f=hint;zone=m
        for c,(p,q,d) in zip(bits,box):
            if d>>e&1 or d>>f&1:zone&=c
            if p>>e&1 and not q>>f&1:zone&=~c
        if not zone>>B&1:raise RuntimeError('non-progress in checked interval')
        m^=zone;fuel+=1
    return None if m else fuel

def pack(states,begin,limit,maxchecks,seconds):
    end=min(begin+limit,len(states));ids=range(begin,end);groups=defaultdict(list)
    for sid in ids:
        ws,core,_=states[sid]
        if core<0:continue
        for i,w in enumerate(ws):
            fixed=ws[:i]+ws[i+1:]
            # New order consists of the fixed shared wires followed by the varying wire.
            newcore=((core&((1<<i)-1))|((core>>(i+1))<<i)|(((core>>i)&1)<<(len(ws)-1)))
            groups[fixed].append((sid,w,newcore))
    keys=sorted((k for k in groups if len(groups[k])>1),key=lambda k:-len(groups[k]))
    used=set();bundles=[];calls=0;until=monotonic()+seconds
    for key in keys:
        if calls>=maxchecks or monotonic()>until:break
        candidates=[a for a in groups[key] if a[0] not in used]
        if len(candidates)<2:continue
        fixed=[mark(w) for w in key]
        for i,(sid,w,core) in enumerate(candidates[:-1]):
            if sid in used:continue
            joined=[(sid,w)];last=mark(w);fuel=0
            for other,val,_ in candidates[i+1:]:
                if calls>=maxchecks or monotonic()>until:break
                if other in used:continue
                temp=union(last,mark(val));calls+=1
                scan=check(fixed+[temp],core)
                if scan is not None:
                    joined.append((other,val));last=temp;fuel=scan
            if len(joined)>1:
                for idx,_ in joined:used.add(idx)
                bundles.append({'fixed':[hex(w) for w in key],'core':core,'fuel':fuel,
                                'members':[[idx,hex(v)] for idx,v in joined]})
            if calls>=maxchecks or monotonic()>until:break
    ungrouped=[i for i in ids if i not in used]
    return bundles,ungrouped,calls

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path);ap.add_argument('out',type=Path)
    ap.add_argument('--start',type=int,default=0);ap.add_argument('--count',type=int,default=512)
    ap.add_argument('--max-checks',type=int,default=10000);ap.add_argument('--seconds',type=int,default=60)
    a=ap.parse_args()
    if a.out.exists():ap.error('output already exists')
    seed,states=utility['load_table'](a.table)
    if not 0<=a.start<len(states) or min(a.count,a.max_checks,a.seconds)<=0:ap.error('invalid bounds')
    start=monotonic();groups,singles,calls=pack(states,a.start,a.count,a.max_checks,a.seconds)
    ids=list(range(a.start,min(len(states),a.start+a.count)))
    old=sum(states[i][2] for i in ids)
    new=sum(g['fuel'] for g in groups)+sum(states[i][2] for i in singles)
    if sorted(singles+[i for g in groups for i,v in g['members']])!=ids:raise RuntimeError('partition lost records')
    result={'seed':seed,'first':a.start,'count':len(ids),'groups':groups,'singles':singles}
    with a.out.open('x') as f:json.dump(result,f,separators=(',',':'))
    print(f'GROUP seed={seed} states={len(ids)} assigned={len(ids)-len(singles)} groups={len(groups)} '
          f'singles={len(singles)} maxGroup={max([len(g["members"]) for g in groups]+[1])} '
          f'originalRounds={old} remainingRounds={new} tried={calls} seconds={monotonic()-start:.2f}')

if __name__=='__main__':main()
