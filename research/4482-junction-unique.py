"""Check simplified single-wire loss tests against every actual move on a supplied graph."""
from pathlib import Path
from runpy import run_path
import argparse
D=Path(__file__).parent
src=run_path(str(D/'4482-junction-audit.py'))
mark,top=src['mark'],src['TOP']

def choices(ws,k):
    marks=[mark(w) for w in ws];u=[]
    for i in range(len(ws)):
        alone=top
        for j,m in enumerate(marks):
            if i!=j:alone&=~m[2]
        u.append(alone)
    for i,a in enumerate(ws):
        for j in range(i+1,len(ws)):
            b=ws[j]
            for op in (0,1):
                if (a|b if op else a&b) in ws:continue
                can_a=not u[i]&(marks[j][1] if op else ~marks[j][0])
                can_b=not u[j]&(marks[i][1] if op else ~marks[i][0])
                for drop in range(4):
                    new=len(ws)+1-(drop&1)-((drop>>1)&1)
                    if new<=6+k-1 and (not drop&1 or can_a) and (not drop&2 or can_b):
                        yield ((16*i+j)*2+op)*4+drop

def check(ws,k):
    original=[code for code,_ in src['moves'](ws,k)]
    fast=list(choices(ws,k))
    if fast!=original:raise ValueError((set(fast)^set(original),k))
    return len(fast)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('graph',nargs='?',type=Path)
    a=p.parse_args()
    if a.graph:
        seed,records,_=src['read_graph'](a.graph)
        todo=[(ws,k) for ws,k,leaf in records if leaf<0]
        mode=f'archive{seed}'
    else:
        raw=tuple(sum((r>>i&1)<<r for r in range(512)) for i in range(9))
        todo=[]
        for xs in [raw,raw+(raw[0]|raw[2],)]:
            key=tuple(sorted(xs));todo.append((key,7))
            todo.extend((tuple(sorted(ws)),6) for _,ws in list(src['moves'](key,7))[:12])
        mode='bounded_roots_and_children'
    total=sum(check(ws,k) for ws,k in todo)
    print(f'PRIVATE_EQ mode={mode} nodes={len(todo)} surviving={total}')
if __name__=='__main__':main()
