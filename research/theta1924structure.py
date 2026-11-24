"""Small graph-only tests for raw gate fanout cases of signed size-ten theta."""
from itertools import combinations,product
from theta1924 import target,evaluate_gate
V=tuple(range(7))


def sub(vertices):
    return [sum(1<<v for v in choice) for k in range(len(vertices)+1)
            for choice in combinations(sorted(vertices),k)]


def main():
    allparts=[]
    triangle=[]
    for D in combinations(V,3):
        rest=set(V)-set(D)
        rows=sub(rest)
        ds=sub(D)
        parts=[]
        for mask in rows:
            x={v for v in rest if mask&(1<<v)}
            y=rest-x
            if target(mask) or target(sum(1<<v for v in y)):
                continue
            if all(len({tuple(target(d|a|b) for b in sub(y)) for a in sub(x)})<=2 for d in ds):
                parts.append((D,tuple(sorted(x)),tuple(sorted(y))))
        allparts+=parts
        cofactor=[tuple(target(d|z) for z in rows) for d in ds]
        for ops in product(range(4),repeat=3):
            codes=[tuple(evaluate_gate(op,bool(d&1<<a),bool(d&1<<b))
                         for (a,b),op in zip(combinations(D,2),ops)) for d in ds]
            if len(set(zip(codes,cofactor)))==len(set(codes)):
                triangle.append((D,ops))
    assert len(allparts)==44
    viable={d for d,x,y in allparts}
    coded={d for d,ops in triangle}
    assert len(coded)==7 and not viable&coded
    for a,b in combinations(V,2):
        pair=sub((a,b)); rest=sub(set(V)-{a,b})
        assert len({tuple(target(d|z) for z in rest) for d in pair})==4
    print(f'{len(allparts)} one-shared partitions; {len(viable)} repeated triples; '
          f'{len(coded)} raw triangle code triples; intersection empty. '
          'All 21 pair projections have four distinct cofactors.')


if __name__=='__main__':
    main()
