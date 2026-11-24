"""Certify equality classes, then aggregate aligned one-changing-column classes.

Records retain the original physical state IDs and a transport for every
member. The output is research data for subsequent Lean checking.
"""
from argparse import ArgumentParser
from collections import defaultdict
from functools import lru_cache
from itertools import permutations, product
from pathlib import Path
from runpy import run_path
from time import monotonic
import json
D=Path(__file__).parent
src=run_path(str(D/'4482-table-groups.py'))
reader=src['utility']['load_table']; mark=src['mark']; check=src['check']; union=src['union']
rows=src['rows']; rows_index={p:i for i,p in enumerate(rows)}
ED=((0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(5,8))
def automorphisms(seed):
    ds=[sum(i in e for e in ED) for i in range(9)]
    A=[i for i in range(9) if ds[i]==2]; B=[i for i in range(9) if ds[i]==3]
    out=[];edge=set(ED)
    for ap,bp in product(permutations(A),permutations(B)):
        m=dict(zip(A+B,ap+bp));g=tuple(m[i] for i in range(9))
        if all(tuple(sorted((g[i],g[j]))) in edge for i,j in ED):out.append(g)
    assert len(out)==12 and out[0]==tuple(range(9))
    if seed:out=[g for g in out if {g[0],g[2]}=={0,2}]
    return out

class Data:
    def __init__(self,seed,states,use_orbit):
        self.states=states
        self.perms=automorphisms(seed)
        if not use_orbit:self.perms=self.perms[:1]
        self.trans=[]
        for g in self.perms:
            rm=[sum((r>>i&1)<<g[i] for i in range(9)) for r in range(512)]
            em=[rows_index[rm[l],rm[h]] for l,h in rows]
            assert sorted(em)==list(range(258))
            chunks=[]
            for ix in range(0,258,8):
                lut=[0]*256
                for q in range(1,256):
                    bit=(q&-q).bit_length()-1
                    lut[q]=lut[q&(q-1)] | (1<<em[ix+bit] if ix+bit<len(em) else 0)
                chunks.append(lut)
            self.trans.append(chunks)
    @lru_cache(None)
    def sig(self,w,g):
        p,n,_=mark(w)
        if g:
            t=self.trans[g]
            def act(v):
                out=0
                for lut in t:
                    out|=lut[v&255];v>>=8
                return out
            p,n=act(p),act(n)
        return p,n,p^n
    def canonical(self,sid):
        ws,core,_=self.states[sid];best=None
        for g in range(len(self.perms)):
            seq=sorted(range(len(ws)),key=lambda i:self.sig(ws[i],g))
            sig=tuple(self.sig(ws[i],g) for i in seq)
            if best is None or sig<best[0]:best=(sig,g,seq)
        sig,g,seq=best
        hint=sum(((core>>i)&1)<<j for j,i in enumerate(seq))
        return sig,(sid,g,seq),hint

def aggregate(data,start,count,budget,wall):
    classes=defaultdict(list);hints=defaultdict(list)
    for sid in range(start,start+count):
        if data.states[sid][1]<0:raise ValueError(f'uncovered physical state {sid}')
        sig,member,h=data.canonical(sid);classes[sig].append(member)
        if h not in hints[sig]:hints[sig].append(h)
    cls=list(classes);keys=defaultdict(list)
    for i,sig in enumerate(cls):
        last=None
        for j,m in enumerate(sig):
            if m==last:continue
            last=m
            keys[sig[:j]+sig[j+1:]].append((i,j))
    candidates=sorted((a for a in keys if len(keys[a])>=2),key=lambda f:-sum(len(classes[cls[i]]) for i,j in keys[f]))
    used=set();groups=[];attempts=0;deadline=monotonic()+wall
    def relocate(h,j,n):
        return (h&((1<<j)-1))|((h>>(j+1))<<j)|(((h>>j)&1)<<(n-1))
    def append(fixed,group,core,fuel):
        ms=[]
        for i,j in group:
            used.add(i)
            for s,g,seq in classes[cls[i]]:
                order=seq[:j]+seq[j+1:]+[seq[j]]
                ms.append([s,g,order])
        groups.append({'core':core,'fuel':fuel,'members':ms})
    for key in candidates:
        if attempts>=budget or monotonic()>deadline:break
        v=[(i,j) for i,j in keys[key] if i not in used]
        if len(v)<2:continue
        for at,(i,j) in enumerate(v[:-1]):
            if i in used:continue
            extra=cls[i][j];n=len(key)+1;group=[(i,j)]
            core=relocate(hints[cls[i]][0],j,n);fuel=0
            def dist(it):
                q=cls[it[0]][it[1]]
                return sum(bin(a^b).count('1') for a,b in zip(extra,q))
            remaining=sorted(v[at+1:],key=dist)
            for h,t in remaining:
                if attempts>=budget or monotonic()>deadline:break
                if h in used:continue
                proposed=union(extra,cls[h][t])
                seeds=[core]+[relocate(x,t,n) for x in hints[cls[h]]]+[relocate(x,j,n) for x in hints[cls[i]]]
                for proposal in dict.fromkeys(seeds):
                    trials=check(key+(proposed,),proposal);attempts+=1
                    if trials is not None:
                        group.append((h,t));extra=proposed;core=proposal;fuel=trials;break
            if len(group)>1:append(key,group,core,fuel)
            if attempts>=budget or monotonic()>deadline:break
    # Identical projected multisets are always one group. The physical source
    # table supplies a working core, but after reordering the needed fuel is
    # recomputed rather than copied from a different ordering.
    for i,sig in enumerate(cls):
        if i in used:continue
        j=len(sig)-1;core=hints[sig][0]
        fuel=check(sig,core,1<<len(sig))
        if fuel is None:raise ValueError(f'orientation lost certificate on class {i}')
        append(sig[:-1],[(i,j)],core,fuel)
    return groups,len(classes),attempts

def audit(data,groups,start,count):
    touched=set();rounds=0;maxlen=0;totalmembers=0
    for grp in groups:
        core=grp['core'];fuel=grp['fuel'];cluster=grp['members']
        box=None
        if not cluster:raise ValueError('empty cluster')
        for sid,g,order in cluster:
            if sid in touched or not start<=sid<start+count:raise ValueError('repeated or out-of-range state')
            touched.add(sid);ws=data.states[sid][0]
            if not 0<=g<len(data.perms) or sorted(order)!=list(range(len(ws))):raise ValueError('invalid transport')
            here=[data.sig(ws[i],g) for i in order]
            if box is None:box=list(here)
            elif len(box)!=len(here):raise ValueError('unequal group widths')
            else:box=[union(x,y) for x,y in zip(box,here)]
        if not 0<=core<1<<len(box) or bin(core).count('1')!=7:raise ValueError('invalid anchor')
        got=check(box,core,fuel)
        if got!=fuel:raise ValueError('failed aggregate interval proof')
        rounds+=got;totalmembers+=len(cluster);maxlen=max(maxlen,len(cluster))
    if touched!=set(range(start,start+count)):raise ValueError('missing original states')
    return rounds,maxlen,totalmembers

def main():
    ap=ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path);ap.add_argument('out',type=Path)
    ap.add_argument('--start',type=int,default=0);ap.add_argument('--count',type=int,default=512)
    ap.add_argument('--max-checks',type=int,default=10000);ap.add_argument('--seconds',type=float,default=50)
    ap.add_argument('--orbit',action='store_true',help='align and collapse projected multisets modulo the real graph group')
    ap.add_argument('--all-alignments',action='store_true',help='search shared columns in every orbit orientation')
    ap.add_argument('--audit-only',action='store_true')
    a=ap.parse_args();beg=monotonic()
    seed,states=reader(a.table)
    if a.audit_only:
        out=json.loads(a.out.read_text());start,count=out['first'],out['count']
        if out['format'] not in (2,3) or out['seed']!=seed:raise ValueError('mismatched source')
        data=Data(seed,states,out['orbit']);groups=out['groups'];classes=out['exactClasses'];attempts=0
    else:
        if a.out.exists():ap.error('output exists')
        if not 0<=a.start<len(states) or min(a.count,a.max_checks,a.seconds)<=0:ap.error('invalid bounds')
        start=a.start;count=min(len(states)-start,a.count);data=Data(seed,states,a.orbit or a.all_alignments)
        if a.all_alignments:
            align=run_path(str(D/'4482-all-align.py'))['aggregate']
            groups,classes,attempts=align(data,start,count,a.max_checks,a.seconds,check,union)
        else:
            groups,classes,attempts=aggregate(data,start,count,a.max_checks,a.seconds)
    rounds,maxgroup,total=audit(data,groups,start,count)
    if not a.audit_only:
        info={'format':2,'seed':seed,'first':start,'count':count,'orbit':a.orbit or a.all_alignments,'allAlignments':a.all_alignments,'exactClasses':classes,'groups':groups}
        with a.out.open('x') as f:json.dump(info,f,separators=(',',':'))
    raw=sum(states[i][2] for i in range(start,start+count))
    print(f'SHARE seed={seed} count={count} exactClasses={classes} finalGroups={len(groups)} '
          f'maxGroup={maxgroup} checkedStates={total} originalRounds={raw} groupRounds={rounds} '
          f'tries={attempts} sec={monotonic()-beg:.2f}')
if __name__=='__main__':main()
