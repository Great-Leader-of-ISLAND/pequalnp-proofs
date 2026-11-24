"""Render a packed random-access Lean graph and check every integer field against V1."""
import argparse,bisect,re
from pathlib import Path
from runpy import run_path
D=Path(__file__).parent
R=run_path(str(D/'4482-junction-unpack.py'))['Reader']

def packcol(data,width):
    if width==0 or any(not 0<=x<1<<width for x in data):raise ValueError('column overflow')
    return [sum(x<<(width*j) for j,x in enumerate(data[i:i+64])) for i in range(0,len(data),64)]

def field(col,k,i):return col[i//64]>>(k*(i%64))&((1<<k)-1)
def width(n):return max(1,n.bit_length())

def cgraph(blob):
    if blob[:8]!=b'CT4482J1':raise ValueError('requires V1 reference export')
    r=R(blob[8:]);seed,n,slen,plen=(r.number() for _ in range(4))
    s,p=r.sub(slen),r.sub(plen);shape=[(s.number(),s.number()) for _ in range(n)]
    pred=[(i-p.number(),p.number()) for i in range(1,n)]
    routes=[[r.number() for j in range(q)] if k&1 else [] for k,q in shape]
    if not s.done() or not p.done() or not r.done():raise ValueError('unread bytes')
    ids=width(n-1);edgeBits=width(sum(map(len,routes)));ls=width(max(q+1 for k,q in shape if not k&1))
    rows=[(k>>1)|((0 if k&1 else q+1)<<3) for k,q in shape]
    floors=[];rule=[];seen=[]
    for i,(parent,encoded) in enumerate(pred,1):
        if not 0<=parent<i:raise ValueError('nontopological initial occurrence')
        if floors and floors[-1][1]==parent:floors[-1]=(i,parent)
        else:floors.append((i,parent))
        g=encoded&15;c=encoded>>4;op=c%8;a,b=divmod(c//8,16)
        rank=b*(b-1)//2+a
        if not 0<=a<b or rank>=64:raise ValueError('rank exceeds nine bits')
        rule.append(((rank*8+op)<<4)|g)
    if any(j>=k for (_,j),(_,k) in zip(floors,floors[1:])):raise ValueError('non-BFS parent runs')
    ends=[];arcs=[]
    for i,((kind,_),rr) in enumerate(zip(shape,routes)):
        if kind&1:
            arcs.extend(rr);ends.append((i,len(arcs)))
    cols={
       'rows':(3+ls,rows),'actions':(13,rule),
       'parentRuns':(2*ids,[(i<<ids)|p for i,p in floors]),
       'exitRuns':(ids+edgeBits,[(i<<edgeBits)|e for i,e in ends]),
       'arcs':(ids+4,arcs)}
    banks={name:packcol(v,k) for name,(k,v) in cols.items()}
    def f(name,i):return field(banks[name],cols[name][0],i)
    for val,(w,xs) in cols.items():
        if any(f(val,i)!=x for i,x in enumerate(xs)):raise ValueError('field replay')
    # Replay random access with the very lower_bound queries used in Lean.
    last=[i for i,_ in floors];sortedParents=[i for i,_ in ends]
    for i,((kind,q),scores) in enumerate(zip(shape,routes)):
        if f('rows',i)%8!=kind>>1 or (f('rows',i)>>3)!=(0 if kind&1 else q+1):raise ValueError('row')
        if i:
            pi=bisect.bisect_left(last,i)
            if (f('parentRuns',pi)&((1<<ids)-1))!=pred[i-1][0]:raise ValueError('parent')
            val=f('actions',i-1);g=val%16;rank,flags=divmod(val//16,8)
            b=1
            while (b+1)*b//2<=rank:b+=1
            a=rank-b*(b-1)//2
            if ((((16*a+b)*8+flags)<<4)|g)!=pred[i-1][1]:raise ValueError('first action')
        pos=bisect.bisect_left(sortedParents,i)
        if pos<len(ends) and (f('exitRuns',pos)>>edgeBits)==i:
            lo=(f('exitRuns',pos-1)&((1<<edgeBits)-1)) if pos else 0
            hi=f('exitRuns',pos)&((1<<edgeBits)-1)
            out=[f('arcs',j) for j in range(lo,hi)]
        else:out=[]
        if out!=scores:raise ValueError('exits')
    return seed,n,ids,edgeBits,len(floors),len(ends),cols,banks

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('archive',type=Path);p.add_argument('out',type=Path)
    a=p.parse_args();module=a.out.stem
    if a.out.exists() or not re.fullmatch('[A-Z][A-Za-z0-9_]*',module):p.error('fresh Lean module required')
    root,n,ids,edgeBits,par,inn,cols,banks=cgraph(a.archive.read_bytes())
    lines=['import PEqualNP.CoJunctionFixed4482','namespace '+module,'open CoJunctionFixed4482']
    for tag,(w,_) in cols.items():
        lines.append('def '+tag+' : Column := ⟨'+str(w)+',#['+','.join(map(hex,banks[tag]))+']⟩')
    lines+=['def graph : Graph := ⟨'+','.join(map(str,(n,ids,edgeBits,par,inn)))+
            ',rows,actions,parentRuns,exitRuns,arcs⟩','end '+module,'']
    text='\n'.join(lines)
    with a.out.open('x') as f:f.write(text)
    print(f'FIXED_GRAPH_OK root={root} states={n} internals={inn} parentRuns={par} UTF8={len(text.encode())}')
if __name__=='__main__':main()
