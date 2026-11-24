"""Search a restricted family with shared OR supports and >=3 live interior dirty ANDs."""
from itertools import combinations
import json
from search1343v3 import EDGES, EDGE_ROWS, POINTS
from graph1342_three_junk import MIS, replay

def library():
    checks=list(EDGE_ROWS)+MIS; pos=(1<<len(EDGES))-1
    sides=tuple((p,) for p in range(POINTS))+tuple(combinations(range(POINTS),2))
    def signature(S):
        mask=sum(1<<v for v in S)
        return sum((bool(m&mask))<<i for i,m in enumerate(checks))
    sig={s:signature(s) for s in sides}
    dictionary={}
    # No artificial boundary on the width of the neighbor OR in a clean star.
    for v in range(POINTS):
        nbr=sorted(x if y==v else y for x,y in EDGES if v in (x,y))
        for k in range(1,len(nbr)+1):
            for b in combinations(nbr,k):
                a=(v,); sig.setdefault(b,signature(b))
                v1,v2=sorted((a,b)); name=('star',v1,v2)
                dictionary[name]=(sig[a]&sig[b],[('s',v1),('s',v2)])
    # Every proper two-factor conjunction is dirty; the complete term is clean.
    for a,b,c in combinations(sides,3):
        A,B,C=sig[a],sig[b],sig[c]
        q=A&B&C
        if not q or q&~pos or not all(x&~pos for x in (A&B,A&C,B&C)):continue
        for i,j,k in ((a,b,c),(a,c,b),(b,c,a)):
            name=('guard',i,j,k);dictionary[name]=(q,[('m',i,j),('s',k)])
    return dictionary

def solve(budget_junk):
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import coo_matrix
    d=library(); names=[]; idx={}; costs=[]; lines=[]; lo=[]; hi=[]
    def variable(key,cost):
        if key not in idx:
            idx[key]=len(names);names.append(key);costs.append(cost)
        return idx[key]
    def constrain(coef, lb, ub):
        lines.append(coef);lo.append(lb);hi.append(ub)
    linking=set(); owners={}
    def dependency(origin,dep):
        if dep[0]=='s' and len(dep[1])==1: return
        pair=(origin,dep)
        if pair in linking: return
        linking.add(pair)
        i=idx[origin]; j=variable(dep,1);constrain({i:1,j:-1},-np.inf,0)
        if dep[0]=='m':
            owners.setdefault(dep,[]).append(i)
            dependency(dep,('s',dep[1]));dependency(dep,('s',dep[2]))
        elif len(dep[1])>2:
            dependency(dep,('s',dep[1][:-1]))
    covering=[{} for _ in EDGES]
    for term,(mask,deps) in d.items():
        i=variable(term,2)
        for dep in deps: dependency(term,dep)
        for e in range(len(EDGES)):
            if mask>>e&1: covering[e][i]=1
    for cov in covering: constrain(cov,1,np.inf)
    for mid,uses in owners.items():
        line={i:-1 for i in uses};line[idx[mid]]=1;constrain(line,-np.inf,0)
    constrain({idx[m]:1 for m in owners},budget_junk,np.inf)
    if budget_junk==0:
        for m in owners:constrain({idx[m]:1},0,0)
    entries=[(row,col,val) for row,coef in enumerate(lines) for col,val in coef.items()]
    rr,cc,vv=zip(*entries);mat=coo_matrix((np.array(vv,dtype=float),(rr,cc)),shape=(len(lines),len(names))).tocsc()
    print('guard requirement',budget_junk,'variables',len(names),'stars',sum(t[0]=='star' for t in d),'guarded terms',sum(t[0]=='guard' for t in d),'candidate junk middles',len(owners),flush=True)
    sol=milp(np.array(costs,dtype=float),integrality=np.ones(len(names)),bounds=Bounds(0,1),
             constraints=LinearConstraint(mat,lo,hi),options={'time_limit':150,'mip_rel_gap':0})
    print('HiGHS',sol.status,sol.message,'incumbent_gate_count',None if sol.fun is None else sol.fun-1,
          'lower_bound',None if getattr(sol,'mip_dual_bound',None) is None else sol.mip_dual_bound-1,flush=True)
    if sol.x is None:return
    chosen={key for key,i in idx.items() if sol.x[i]>.5}
    gs=[];memo={}
    def put(op,i,j):
        gs.append({'op':op,'inputs':[i,j]});return POINTS+len(gs)-1
    def make(k):
        if k in memo:return memo[k]
        if k[0]=='s':
            S=k[1];v=S[0] if len(S)==1 else put('or',make(('s',S[:-1])),S[-1])
        elif k[0] in ('m','star'):v=put('and',make(('s',k[1])),make(('s',k[2])))
        else:v=put('and',make(('m',k[1],k[2])),make(('s',k[3])))
        memo[k]=v;return v
    outputs=[make(k) for k in d if k in chosen];o=outputs[0]
    for i in outputs[1:]:o=put('or',o,i)
    circuit={'gates':gs,'output':o}; junk=replay(circuit);assert len(junk)>=budget_junk
    assert len(gs)<=round(sol.fun)-1
    print('independently replayed',len(gs),'gates with',len(junk),'junk ANDs over 2048 rows',flush=True)
    if budget_junk and len(gs)<=21:print('WITNESS',json.dumps(circuit),flush=True)
if __name__=='__main__':
    solve(0);solve(3)
