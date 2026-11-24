"""Align fixed n-1 columns under every allowed genuine graph automorphism.

Plugs into 4482-share-table.py's exact archive reader and independent auditor.
Only disjoint groups are accepted; previously unselected states fall back to
their own accepted interval obstruction.
"""
from collections import defaultdict
from time import monotonic

def aggregate(data,start,count,budget,wall,check,union):
    classes=defaultdict(list);by_sid={}
    for sid in range(start,start+count):
        ws,core,r=data.states[sid]
        if core<0:raise ValueError('missing source anchor')
        views={}
        for g in range(len(data.perms)):
            seq=sorted(range(len(ws)),key=lambda i:data.sig(ws[i],g))
            vals=tuple(data.sig(ws[i],g) for i in seq)
            if vals in views:continue
            hint=sum(((core>>i)&1)<<j for j,i in enumerate(seq))
            views[vals]=(g,seq,hint)
        classes[min(views)].append(sid);by_sid[sid]=views
    cls=list(classes);index=defaultdict(dict)
    for cid,k in enumerate(cls):
        rep=classes[k][0]
        for vals,(_,_,hint) in by_sid[rep].items():
            prev=None
            for j,s in enumerate(vals):
                if s==prev:continue
                prev=s;fixed=vals[:j]+vals[j+1:];n=len(vals)
                rearranged=(hint&((1<<j)-1))|((hint>>(j+1))<<j)|(((hint>>j)&1)<<(n-1))
                # Only one occurrence of a class can be used by a fixed-key
                # cluster. Repeated actual input indices always stay present.
                index[fixed].setdefault(cid,(vals,j,rearranged))
    eligible=sorted((k for k,v in index.items() if len(v)>=2),
                    key=lambda k:-sum(len(classes[cls[c]]) for c in index[k]))
    used=set();groups=[];trials=0;until=monotonic()+wall
    def finish(rows,anchor,fuel):
        members=[]
        for cid,vals,j in rows:
            used.add(cid)
            for sid in classes[cls[cid]]:
                g,seq,_=by_sid[sid][vals]
                members.append([sid,g,seq[:j]+seq[j+1:]+[seq[j]]])
        groups.append({'core':anchor,'fuel':fuel,'members':members})
    for fixed in eligible:
        if trials>=budget or monotonic()>until:break
        cand=[(c,*item) for c,item in index[fixed].items() if c not in used]
        if len(cand)<2:continue
        for at,(c,vals,j,initial) in enumerate(cand[:-1]):
            if c in used:continue
            group=[(c,vals,j)];anchor=initial;extra=vals[j];fuel=None
            def distance(x):
                other=x[1][x[2]]
                return sum(bin(a^b).count('1') for a,b in zip(extra,other))
            for d,other,q,alt in sorted(cand[at+1:],key=distance):
                if trials>=budget or monotonic()>until:break
                if d in used:continue
                combined=union(extra,other[q])
                for h in dict.fromkeys((anchor,alt,initial)):
                    trials+=1;res=check(fixed+(combined,),h)
                    if res is not None:
                        fuel=res;anchor=h;extra=combined;group.append((d,other,q));break
            if len(group)>1:finish(group,anchor,fuel)
            if trials>=budget or monotonic()>until:break
    for cid,vals in enumerate(cls):
        if cid in used:continue
        sid=classes[vals][0];g,seq,h=by_sid[sid][vals];fuel=check(vals,h,1<<len(vals))
        if fuel is None:raise ValueError('exact projected class lost its original obstruction')
        finish([(cid,vals,len(vals)-1)],h,fuel)
    return groups,len(classes),trials
