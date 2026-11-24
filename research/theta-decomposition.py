#!/usr/bin/env python3
"""Boolean decomposition obstruction for tight (fanout-zero) theta suffixes.
Return a two-block split admitting a potentially appropriate AND or OR root, or
exclude every split. The returned split is only necessary. All 128 rows used.
"""
import argparse,collections,functools,itertools,json,runpy,time
from pathlib import Path
G=runpy.run_path(str(Path(__file__).with_name('theta-first-not.py')))
W=len(G['NEG']); U=G['U'];FULL=G['PAIR'];LOW=G['LOW'];STRIPES=G['STRIPES'];HIGH=STRIPES<<(W-1)

def positive_rows(d):return (((d & (FULL^HIGH)) + (HIGH-STRIPES)) | d) & HIGH

def negative_rows(d):
    shift=W
    for _ in range((len(G['POS'])-1).bit_length()):d|=d>>shift;shift*=2
    return d&LOW

def splits(ws,t,recursive=False):
    cuts=[G['cuts'](w) for w in ws]; eqs=[FULL^(a|b) for a,b in cuts]
    choices=[]
    for i,(a,b) in enumerate(cuts):
        if not t:choices.append((a,));continue
        only=FULL
        for j,e in enumerate(eqs):
            if i!=j:only &= e
        pos,neg=bool(only&a),bool(only&b)
        if pos and neg:return None
        choices.append((a,) if pos else (b,) if neg else (a,b))
    for oriented in itertools.product(*choices):
        cover=0
        for z in oriented:cover|=z
        if cover!=FULL:continue
        masks=[FULL]
        for z in oriented:
            e=FULL^z;masks += [m&e for m in masks]
        allmask=len(masks)-1
        if recursive:
            pwords=[];nwords=[]
            for w,(a,b),oriented_w in zip(ws,cuts,oriented):
                val=w if oriented_w==a else U^w
                pwords.append(sum((1<<(j*W)) for j,r in enumerate(G['POS']) if val>>r&1))
                nwords.append(sum(1<<j for j,r in enumerate(G['NEG']) if val>>r&1))
            @functools.lru_cache(maxsize=None)
            def can(m,p,n):
                if not p or not n:return True
                if m&(m-1)==0:
                    i=m.bit_length()-1
                    return not(p&~pwords[i] or n&nwords[i])
                active=p*n
                if masks[m]&active:return False
                bit=m&-m;a=(m-1)&m
                while a:
                    if not a&bit:
                        b=m^a;aa=masks[a]&active;bb=masks[b]&active
                        pa=positive_rows(aa)>>(W-1);pb=positive_rows(bb)>>(W-1)
                        if not pa&pb and can(a,pb,n) and can(b,pa,n):return True
                        na=negative_rows(aa);nb=negative_rows(bb)
                        if not na&nb and can(a,p,nb) and can(b,p,na):return True
                    a=(a-1)&m
                return False
            ok=can(allmask,STRIPES,LOW);can.cache_clear()
            if ok:return ('recursive-compatible',allmask)
            continue
        for side in range(1,(allmask+1)//2):
            a,b=masks[side],masks[allmask^side]
            if not positive_rows(a)&positive_rows(b):return ('OR',side)
            if not negative_rows(a)&negative_rows(b):return ('AND',side)
    return None

def controls():
    f=G['F'];xx=G['X'];edge=[xx[u]&xx[v] for u,v in G['E']];x,y,z=edge[0],0,0
    for a in edge[1:4]:y|=a
    for a in edge[4:]:z|=a
    neq=U^f;half=(x|y)&f
    formulas=[([x,y,z],0,lambda a,b,c:a|b|c),([U^x,y,z],1,lambda a,b,c:(U^a)|b|c),
              ([f|xx[0],f|(U^xx[0])],0,lambda a,b:a&b),
              ([half|(neq&xx[1]),half|(neq&(U^xx[1])),z],0,lambda a,b,c:(a&b)|c)]
    for vals,t,calc in formulas:
        assert calc(*vals)==f
        assert splits(vals,t,True) is not None
    print('four planted read-once formulas verified on every input and accepted by recursion')

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('levels',type=Path);p.add_argument('--control',action='store_true');p.add_argument('--recursive',action='store_true');p.add_argument('--seconds',type=float,default=1);p.add_argument('--limit',type=int,default=10000);p.add_argument('--stage',type=int,default=2);a=p.parse_args();
    if a.control:controls()
    d=json.loads(a.levels.read_text());vals=[]
    for op,u,v in d['recipes']:
        vals.append(G['X'][u] if op=='atom' else U^vals[u] if op=='not' else vals[u]&vals[v] if op=='and' else vals[u]|vals[v])
    # Interleave t buckets for a reproducible balanced bounded sample.
    grouped=collections.defaultdict(list);k=10-a.stage
    for t,vs in d['levels'][a.stage]:
        if len(vs)+t==k+1:grouped[t].append(vs)
    done=collections.Counter();bad=collections.Counter();start=time.monotonic()
    for i in range(max(map(len,grouped.values()),default=0)):
        for t,L in sorted(grouped.items()):
            if i>=len(L):continue
            if sum(done.values())>=a.limit or time.monotonic()-start>=a.seconds:break
            done[t]+=1;bad[t]+=splits([vals[n] for n in L[i]],t,a.recursive) is None
        else:continue
        break
    print('audited',dict(done),'no disjoint AND/OR root',dict(bad),'wall_seconds',round(time.monotonic()-start,3))
if __name__=='__main__':main()
