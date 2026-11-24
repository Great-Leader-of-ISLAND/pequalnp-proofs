"""Verify the exact Heawood bit table and all covers of its nonincident two-vertex deletions."""
from itertools import combinations
from collections import Counter
W=[95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
def size(x):return bin(x).count('1')
rows=[sum((w>>i&1)<<v for v,w in enumerate(W)) for i in range(58)]
E=rows[:21]
assert len(set(E))==21 and all(size(e)==2 and e&127 and e>>7 for e in E)
I={m for m in range(1<<14) if all((m&e)!=e for e in E)}
maximal={m for m in I if all(m|1<<i not in I for i in range(14) if not m>>i&1)}
assert maximal==set(rows[21:]) and len(maximal)==37
pairs=0
for p in range(7):
 for l in range(7,14):
    mask=(1<<p)|(1<<l)
    if mask in E:continue
    es=[e for e in E if not mask&e]
    yes=[i for i in range(14) if not mask>>i&1]
    covers={sum(1<<i for i in S) for S in combinations(yes,6)
            if all(any(e>>i&1 for i in S) for e in es)}
    assert len(es)==15 and covers=={127&~mask,(127<<7)&~mask}
    assert all(sum(bool(e>>i&1) for e in es)>=2 for i in yes)
    pairs+=1
print('21 edge rows, 37 maximal independent rows, 458 independent inputs; 28 nonincident pairs:',pairs)
print('For all 28, the only six-vertex covers after deleting the endpoints are the two shores.')
