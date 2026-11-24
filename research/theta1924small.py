"""Pack an explicitly selected subfamily of theta row pairs for Lean's kernel."""
from pathlib import Path
import re
from theta1924front import POS,NEG,X
import argparse

def emit(base,mask):
    chosen=[(p,n) for i,p in enumerate(POS) for j,n in enumerate(NEG)
            if mask>>(i*len(NEG)+j)&1]
    def pack(z):
        p=sum((z>>a&1)<<i for i,(a,b) in enumerate(chosen))
        n=sum((z>>b&1)<<i for i,(a,b) in enumerate(chosen))
        return '('+hex(p)+','+hex(n)+')'
    s=base.read_text().replace('abbrev Width := 2727',f'abbrev Width := {len(chosen)}')
    q=s.index('def raw : List Wire := [')
    u=s.index('\ndef col',q)
    s=s[:q]+'def raw : List Wire := ['+',\n'.join(pack(z) for z in X)+']\n'+s[u:]
    zero=next(i for i,(p,n) in enumerate(chosen) if n==0)
    s=s.replace('def empty : Row := (false,0)',f'def empty : Row := (false,{zero})')
    q=s.index('def privateIndex (j')
    u=s.index('\ntheorem private_row',q)
    private=[next(i for i,(p,n) in enumerate(chosen) if p^n==1<<v) for v in range(7)]
    s=s[:q]+'def privateIndex (j : Fin 7) : Fin Width := match j.val with\n'+'\n'.join(
        f'  | {v if v<6 else "_"} => {i}' for v,i in enumerate(private))+'\n'+s[u:]
    return s,pack

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--mask',required=True)
    p.add_argument('--base',required=True,type=Path)
    p.add_argument('--out',required=True,type=Path)
    p.add_argument('--probes',type=Path)
    args=p.parse_args()
    s,packed=emit(args.base,int(args.mask,0))
    args.out.write_text(s)
    if args.probes:
        import theta1924probes as pr
        pr.dfs(10,tuple(sorted(X)))
        args.probes.write_text('namespace CoThetaBits\n'+'\n'.join(f'def probe{k} : List Wire := ['+
            ',\n'.join(packed(z) for z in ws)+']' for k,ws in sorted(pr.probes.items()))+
            '\nend CoThetaBits\n')
