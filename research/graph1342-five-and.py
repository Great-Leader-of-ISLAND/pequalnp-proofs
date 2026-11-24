"""Exact negative-row obstruction for G: <=5 ANDs, >=3 junk ANDs; free OR.
Run: python3 graph1342-five-and.py [--capacity-only]. No dependencies.
The optional mode omits the early fair-share bound and obtains the same empty
third level using just the capacity of individual orientation prefixes.
"""
import argparse
import itertools

EDGES = ((0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9))

def independent(r):
    return all(not (r >> u & 1 and r >> v & 1) for u,v in EDGES)

ROWS = [r for r in range(1<<11) if independent(r) and
        all(r >> v & 1 or not independent(r | (1<<v)) for v in range(11))]
ALL = (1<<len(ROWS))-1
PC = bytearray(65536)
for i in range(1,len(PC)):
    PC[i] = PC[i>>1] + (i&1)

def count(mask):
    return PC[mask&65535]+PC[mask>>16]

def extend(pool, added):
    # A larger union can never return to <=16 rows. Keep small unions even
    # when not yet large enough to serve as one of the two chosen ports.
    return pool | {q|added for q in pool if count(q|added)<=16}

def prefixes(pool, groups, depth, sizes, capacity_only):
    ports = sorted(q for q in pool if count(q)>=8)
    for p,q in itertools.combinations(ports,2):
        junk = p&q
        if not junk:
            continue
        left_only, right_only = p^junk,q^junk
        if min(count(left_only),count(right_only))<8:
            continue
        if not capacity_only:
            equal = ALL^(p^q)
            if sum(count(g)+count(g&equal) for g in groups)+(3-depth)>32:
                continue
        new_groups = [g & allowed for g in groups
                      for allowed in (ALL^left_only, ALL^right_only)]
        if any(count(g) > (1<<(5-depth)) for g in new_groups):
            continue
        sizes[depth-1]+=1
        if depth<3:
            prefixes(extend(pool,junk),new_groups,depth+1,sizes,capacity_only)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--capacity-only',action='store_true')
    args=ap.parse_args()
    assert len(ROWS)==24
    pool={0}
    for v in range(11):
        col=sum(1<<i for i,r in enumerate(ROWS) if r>>v&1)
        pool=extend(pool,col)
    sizes=[0,0,0]
    prefixes(pool,[ALL],1,sizes,args.capacity_only)
    print('maximal independent rows:',len(ROWS))
    print('first, second, third junk prefixes:',*sizes)
    assert sizes[-1]==0

if __name__=='__main__':
    main()
