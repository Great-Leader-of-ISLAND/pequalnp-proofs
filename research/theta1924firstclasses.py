"""Compute theta automorphism orbit representatives after mathematical root tests."""
from itertools import combinations
from theta1924front import PERMS,X,ALL
from theta1924treesize import summarize

# Exhausted six-coordinate signed minor results, cap 10 (strong-minor log).
MINOR={(0,1):(9,6),(0,2):(6,9),(0,3):(6,10),(0,4):(8,8),(2,3):(9,7),
       (3,4):(8,9),(3,5):(8,8),(3,6):(9,8)}
PAIR={(0,1):4,(0,2):5,(0,3):5,(0,4):4,(2,3):5,(3,4):7,(3,5):5,(3,6):5}

def action(i,j,op,p):
    a,b=p[i],p[j]
    if a>b:a,b=b,a;op=(0,1,3,2)[op]
    return a,b,op

def passes(i,j,op):
    orb=min(tuple(sorted((p[i],p[j]))) for p in PERMS)
    # Both raw inputs have at least two readers. Absorbing zero produces one
    # extra constant-path loss beyond the two raw readers.
    if (op in (0,2) and i>=2) or (op in (0,3) and j>=2):return False
    if PAIR[orb]>=7:return False
    # Every identification removes the first gate, permitting at most 9.
    if max(MINOR[orb])>=10:return False
    # This specified identification makes the first gate constant (rather than
    # an alias), and therefore also deletes an additional eventual consumer.
    anti=int(op<2)
    if MINOR[orb][anti]>=9:return False
    return True

if __name__=='__main__':
    orbit=set();total=0;allcases=0
    for ij,(i,j) in enumerate(combinations(range(7),2)):
        for op in range(4):
            if not passes(i,j,op):continue
            allcases+=1
            key=min(action(i,j,op,p) for p in PERMS)
            if key in orbit:continue
            orbit.add(key)
            a,b=X[i],X[j]
            z=(a&b,a|b,a&(ALL^b),b&(ALL^a))[op]
            x,_=summarize(9,tuple(sorted((*X,z))))
            total+=x
            print('first',4*ij+op,'pair',i,j,'op',op,'unfolded',x,flush=True)
    print('root survivors',allcases,'representatives',len(orbit),'total remaining unfolded',total)
