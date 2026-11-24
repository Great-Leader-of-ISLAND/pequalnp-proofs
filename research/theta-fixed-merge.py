#!/usr/bin/env python3
"""Read-once exclusion by two forced conflicting restrictions of one signal pair.
The kept pair's lowest common gate fixes its interaction whenever neither signal
is masked. Other signals need only be constant within each restriction group.
Returns two sample blocks, both inconsistent with any constant or unary output.
"""
import argparse,collections,itertools,json,runpy,time
from pathlib import Path
G=runpy.run_path(str(Path(__file__).with_name('theta-first-not.py')));U=G['U'];UNARY=(0,15,12,3,10,5)

def find_merge(ws):
    vals=[0]*128
    for j,w in enumerate(ws):
        for r in range(128):vals[r]|=(w>>r&1)<<j
    y=[G['target'](r) for r in range(128)]
    for a,b in itertools.combinations(range(len(ws)),2):
        select=(1<<a)|(1<<b); groups={}
        for r,s in enumerate(vals):
            group=groups.setdefault(s&~select,[0,0]);cell=((s>>a&1)<<1)|(s>>b&1);group[y[r]]|=1<<cell
        force0=force1=0;used=[]
        for g,(n,p) in groups.items():
            if any((v & n)==0 and (p & ~v)==0 for v in UNARY):continue
            if force1 & n or force0 & p:
                prev=next(k for k,n0,p0 in used if p0 & n or n0 & p)
                def corners(block):
                    bycell={}
                    for r,s in enumerate(vals):
                        if s&~select==block:
                            cell=((s>>a&1)<<1)|(s>>b&1);bycell.setdefault(cell,r)
                    return sorted(bycell.values())
                return a,b,corners(prev),corners(g)
            force0|=n;force1|=p;used.append((g,n,p))
    return None

def verify(ws,wit):
    a,b,g,h=wit; assert a!=b
    def allowed(rows):
        assert 1<=len(rows)<=4
        for i,w in enumerate(ws):
            if i!=a and i!=b:assert len({(w>>r)&1 for r in rows})==1
        pos=neg=0
        for r in rows:
            xy=(((ws[a]>>r)&1)<<1)|((ws[b]>>r)&1)
            if G['target'](r):pos|=1<<xy
            else:neg|=1<<xy
        result={v for v in range(16) if not v&neg and not pos&~v}
        assert result.isdisjoint(UNARY)
        return result
    assert allowed(g).isdisjoint(allowed(h))

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('levels',type=Path);p.add_argument('--seconds',type=float,default=1);p.add_argument('--limit',type=int,default=10000);p.add_argument('--stage',type=int,default=2);a=p.parse_args();d=json.loads(a.levels.read_text());ws=[]
    for op,u,v in d['recipes']:ws.append(G['X'][u] if op=='atom' else U^ws[u] if op=='not' else ws[u]&ws[v] if op=='and' else ws[u]|ws[v]);
    groups=collections.defaultdict(list)
    for t,ids in d['levels'][a.stage]:
        if len(ids)+t==11-a.stage:groups[t].append(ids)
    done=collections.Counter();bad=collections.Counter();start=time.monotonic()
    for i in range(max(map(len,groups.values()),default=0)):
        for t,S in sorted(groups.items()):
            if i>=len(S):continue
            if time.monotonic()-start>a.seconds or sum(done.values())>=a.limit:break
            done[t]+=1;v=[ws[j] for j in S[i]];wit=find_merge(v)
            if wit is not None:verify(v,wit);bad[t]+=1
        else:continue
        break
    print('examined',dict(done),'forced conflicting pair',dict(bad),'seconds',round(time.monotonic()-start,3))
if __name__=='__main__':main()
