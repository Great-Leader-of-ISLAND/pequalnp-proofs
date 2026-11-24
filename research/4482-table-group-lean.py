"""Replay one contiguous group block from a real tight-state sharing experiment."""
from pathlib import Path
from runpy import run_path
from functools import reduce
from argparse import ArgumentParser
import json,re
D=Path(__file__).parent
g=run_path(str(D/'4482-table-groups.py'));mark=g['mark'];union=g['union']
u=g['utility']
def main():
    a=ArgumentParser(description=__doc__)
    a.add_argument('table',type=Path);a.add_argument('groups',type=Path);a.add_argument('out',type=Path)
    a.add_argument('--start',type=int,default=0);a.add_argument('--count',type=int,default=4)
    args=a.parse_args()
    if args.out.exists() or not re.fullmatch(r'[A-Z][A-Za-z0-9_]*\.lean',args.out.name):a.error('output must be a new Lean module')
    seed,states=u['load_table'](args.table)
    doc=json.loads(args.groups.read_text());version=doc.get('format',1)
    share=run_path(str(D/'4482-share-table.py')) if version==2 else None
    state_data=share['Data'](seed,states,doc['orbit']) if share else None
    allgroups=doc['groups']; groups=allgroups[args.start:args.start+args.count]
    if seed!=doc['seed'] or args.start<0 or args.count<1 or len(groups)!=args.count:a.error('seed or group range mismatch')
    out=['import PEqualNP.CoGroupBlock4482',f'namespace {args.out.stem}',
         'open CoBitBlock4482 CoGroupBlock4482','set_option maxHeartbeats 0','set_option maxRecDepth 200000']
    shapes=set();marked={};masks=set();member_count=0
    def ref(sig):
        if sig not in marked:
            p,q,_=sig;i=len(marked);marked[sig]=i;out.append(f'def w{i} : Mark := ({hex(p)},{hex(q)})')
        return f'w{marked[sig]}' 
    for gi,group in enumerate(groups,args.start):
        core=group['core'];fuel=group['fuel']
        if version==2:
            fixed=None;members=[];seen=set()
            for sid,perm,order in group['members']:
                if sid in seen:raise ValueError('duplicate original state')
                seen.add(sid);ws=states[sid][0]
                if sorted(order)!=list(range(len(ws))) or not 0<=perm<len(state_data.perms):
                    raise ValueError('wrong physical permutation')
                sig=[state_data.sig(ws[i],perm) for i in order]
                if fixed is not None and sig[:-1]!=fixed:raise ValueError('mismatched common columns')
                fixed=sig[:-1];members.append(sig[-1])
        else:
            fixed=tuple(int(s,16) for s in group['fixed'])
            entries=[(sid,int(v,16)) for sid,v in group['members']]
            if len(set(s for s,_ in entries))!=len(entries):raise ValueError('duplicate state ID')
            for sid,w in entries:
                if tuple(sorted(fixed+(w,)))!=states[sid][0]:raise ValueError('group does not describe actual state')
            fixed=list(map(mark,fixed));members=[mark(w) for _,w in entries]
        n=len(fixed)+1;member_count+=len(members)
        boxes=[f'exactBox ({ref(w)})' for w in fixed]
        p,q,d=reduce(union,members)
        if g['check'](fixed+[(p,q,d)],core,fuel)!=fuel:raise ValueError('actual aggregate interval did not verify')
        out.append(f'def extra{gi} : Box := ⟨{hex(p)},{hex(q)},{hex(d)}⟩');boxes.append(f'extra{gi}')
        vals=[ref(w) for w in members]
        if n not in shapes:
            shapes.add(n)
            for j,mask in enumerate(u['geometry'](n)):
                out.append(f'def g{n}_{j} : BitVec {1<<n} := {hex(mask)}')
        if (n,core) not in masks:
            masks.add((n,core));out.append(f'def m{n}_{core} : BitVec {1<<n} := {hex(u["target"](n,core))}')
        cols=','.join(f'⟨{b},g{n}_{j}⟩' for j,b in enumerate(boxes))
        out.append(f'theorem fit{gi} : ['+','.join(vals)+f'].all (fits extra{gi})=true := by decide +kernel')
        out.append(f'theorem verify{gi} : checkGroup ([{cols}] : List (BCol {1<<n})) {fuel} m{n}_{core}=true := by decide +kernel')
        out.append(f'#print axioms verify{gi}')
    out+=[f'end {args.out.stem}',''];text='\n'.join(out)
    with args.out.open('x') as f:f.write(text)
    print('seed',seed,'groups',len(groups),'real_states',member_count,'utf8',len(text.encode()))
if __name__=='__main__':main()
