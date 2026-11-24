"""Exact finite read-once LCA certificates and bounded labeled-formula enumeration.

The input is the stdout of 3004-fixed-bank.cpp. Use --all-source before compiling
the unmodified upstream checker to get a separate version printing every leaf.
"""
import argparse
import ast
from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import re
import sys
import time

HERE = Path(__file__).resolve().parent
raw = (HERE/'3004-single-raw-bank.py').read_text().splitlines()
WIRE = ast.literal_eval(next(line[2:] for line in raw if line.startswith('W=')))
ROWS = [sum(1 << j for j, x in enumerate(WIRE) if x >> i & 1) for i in range(58)]
assert len(WIRE) == 14 and len(set(ROWS)) == 58
FULL = (1 << 58) - 1

def ids(m):
    while m:
        u = m & -m
        yield u.bit_length()-1
        m -= u

def count(m):
    return bin(m).count('1')

def op_witness(positive, negative, mask):
    # Each dictionary key is a pair of labels. Row IDs refer to the fixed 58 input rows.
    def collect(pivots, opposite, diff):
        result = {}
        for pivot in pivots:
            labels = {}
            for other in opposite:
                v = diff(pivot,other) & mask
                if v and v & (v-1) == 0:
                    labels.setdefault(v.bit_length()-1,other)
            for i,j in combinations(sorted(labels),2):
                result.setdefault((i,j),(pivot,labels[i],labels[j]))
        return result
    must_or = collect(negative,positive,lambda n,p: ROWS[p] & ~ROWS[n])
    must_and = collect(positive,negative,lambda p,n: ROWS[p] & ~ROWS[n])
    return must_or,must_and

class Limit(Exception):
    pass

def exact_multiset(leaves, must_or, must_and, target, deadline, cap):
    """All binary trees on these occurrences. A cap produces UNKNOWN, never NO."""
    indices = {}
    for j,v in enumerate(leaves):
        indices[v] = indices.get(v,0) | (1<<j)
    def constraints(edges):
        return [(indices[a],indices[b]) for a,b in edges
                if count(indices[a])==count(indices[b])==1]
    ro,ra=constraints(must_or),constraints(must_and)
    ground=(1<<len(leaves))-1
    inspected=0
    @lru_cache(None)
    def visit(mask):
        nonlocal inspected
        if not mask & (mask-1):
            return {WIRE[leaves[mask.bit_length()-1]]}
        result=set()
        left=(mask-1)&mask
        while left:
            right=mask^left
            if left<right:
                def split(pair):
                    a,b=pair
                    return bool((a&left and b&right) or (a&right and b&left))
                allow_and=not any(split(pair) for pair in ro)
                allow_or=not any(split(pair) for pair in ra)
                if allow_and or allow_or:
                    la=visit(left); rb=visit(right)
                    for x in la:
                        for y in rb:
                            inspected+=1
                            if inspected%1024==0 and (inspected>cap or time.monotonic()>deadline):
                                raise Limit
                            if allow_and:
                                z=x&y; result.add(z)
                                if z==target and mask==ground:
                                    return {target}
                            if allow_or:
                                z=x|y; result.add(z)
                                if z==target and mask==ground:
                                    return {target}
            left=(left-1)&mask
        return result
    if target not in visit(ground):return None
    def decode(mask,w):
        if mask & (mask-1)==0:
            v=leaves[mask.bit_length()-1]
            assert WIRE[v]==w
            return v
        left=(mask-1)&mask
        while left:
            right=mask^left
            if left<right:
                def split(pair):
                    a,b=pair
                    return bool((a&left and b&right) or (b&left and a&right))
                allow_and=not any(split(pair) for pair in ro)
                allow_or=not any(split(pair) for pair in ra)
                if allow_and or allow_or:
                    for x in visit(left):
                        for y in visit(right):
                            if allow_and and (x&y)==w:
                                return ('&',decode(left,x),decode(right,y))
                            if allow_or and (x|y)==w:
                                return ('|',decode(left,x),decode(right,y))
            left=(left-1)&mask
        raise AssertionError('missing formula despite successful inclusion')
    tree=decode(ground,target)
    def validate(t):
        if isinstance(t,int):return WIRE[t],0
        a,n=validate(t[1]);b,m=validate(t[2])
        return (a&b if t[0]=='&' else a|b),n+m+1
    assert validate(tree)==(target,len(leaves)-1)
    return tree

def test(p,bad,k,seconds,cap):
    target=p|(bad<<21)
    pos=list(ids(target)); neg=list(ids(FULL^target))
    mandatory={}
    minimal=set()
    for i in pos:
        for j in neg:
            d=ROWS[i]&~ROWS[j]
            if not d: return 'impossible-order',None
            if not d&(d-1): mandatory.setdefault(d.bit_length()-1,(i,j))
            minimal.add(d)
    minimal=tuple(d for d in minimal if not any(e!=d and e&d==e for e in minimal))
    K=k+1
    if len(mandatory)>K:return 'too-many-inputs',mandatory
    forced=sum(1<<v for v in mandatory)
    extra=list(ids(((1<<len(WIRE))-1)^forced))
    dead=time.monotonic()+seconds
    n_support=0; n_dynamic=0; first_conflict=None
    for t in range(min(K-len(mandatory),len(extra))+1):
        for more in combinations(extra,t):
            vertices=sorted([*mandatory,*more]); support=forced|sum(1<<v for v in more)
            if not vertices or any(d&support==0 for d in minimal):continue
            n_support+=1
            ro,ra=op_witness(pos,neg,support)
            conflicts=sorted(ro.keys() & ra.keys())
            for dup in combinations_with_replacement(vertices,K-len(vertices)):
                hit=next((pair for pair in conflicts if not any(v in dup for v in pair)),None)
                if hit is not None:
                    if first_conflict is None:first_conflict=(hit,ro[hit],ra[hit])
                    continue
                n_dynamic+=1
                if time.monotonic()>dead:return 'unresolved-limit',(n_support,n_dynamic)
                try:
                    tree=exact_multiset(vertices+list(dup),ro,ra,target,dead,cap)
                    if tree is not None:return 'bank-column-realizable',tree
                except Limit:return 'unresolved-limit',(n_support,n_dynamic)
    if n_support==1 and len(mandatory)==K and first_conflict is not None:
        return 'eight-forced-lca' if K==8 else 'all-forced-lca',(sorted(mandatory.items()),first_conflict)
    return ('formula-exhausted' if n_dynamic else 'support-lca-exhausted'),(n_support,n_dynamic,first_conflict)

def check_log(lines,k,seconds,cap):
    pending=[];checked=0; discarded=0; complete=False; total=None; stats=Counter()
    for line in lines:
        m=re.search(r'\bREMAIN (\d+) (\d+) (\d+)',line)
        if m: pending.append(tuple(map(int,m.groups())))
        m=re.search(r'\bBANK_COMPILED (\d+) (COMPLETE|INCOMPLETE) .*remaining=(\d+)',line)
        if not m:continue
        if int(m[1])==k:
            complete=(m[2]=='COMPLETE');total=int(m[3])
            for r,p,a in pending:
                reason,data=test(p,a,k,seconds,cap);stats[reason]+=1;checked+=1
                if reason not in ('unresolved-limit','bank-column-realizable'):discarded+=1
                print('BANK_LEAF',k,r,p,a,reason,data)
        pending=[]
    print('BANK_LEAF_TOTAL',k,'expected',total,'checked',checked,'discarded',discarded,
          'scope_complete',complete and total==checked,'excluded_entire_window',complete and checked==discarded==total,
          'reasons',dict(stats),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser(__doc__)
    ap.add_argument('--k',type=int,default=7)
    ap.add_argument('--seconds',type=float,default=.35,help='exact DP seconds per terminal')
    ap.add_argument('--cap',type=int,default=100000,help='pair combinations per multiset')
    ap.add_argument('--log',type=Path)
    ap.add_argument('--all-source',type=Path,help='emit a separate C++ verifier printing all k=7 leaves')
    args=ap.parse_args()
    if args.all_source:
        src=(HERE/'3004-fixed-bank.cpp').read_text()
        old='if(leaves<4)cout<<"REMAIN "'
        assert src.count(old)==1 and args.all_source.resolve()!=(HERE/'3004-fixed-bank.cpp').resolve()
        args.all_source.write_text(src.replace(old,'if(k==7||leaves<4)cout<<"REMAIN "'))
    else:
        with args.log.open() if args.log else sys.stdin as lines:
            check_log(lines,args.k,args.seconds,args.cap)
