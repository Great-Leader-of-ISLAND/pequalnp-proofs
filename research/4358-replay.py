"""Read a C++ witness artifact and validate every physical condition in the 4358 counterexample."""
import argparse
import json
from itertools import combinations
from pathlib import Path

ids = (1, 12, 4, 15, 26, 35, 46, 36)
edges = tuple(divmod(e, 10) for e in ids)


def evaluate(gates, inputs):
    bank = list(inputs)
    for kind, a, b in gates:
        assert kind in (0, 1) and 0 <= a < len(bank) and 0 <= b < len(bank)
        bank.append((bank[a] and bank[b]) if kind else (bank[a] or bank[b]))
    return bank


def check(w):
    g, h = w['gates'], w['x4_shifted_gates']
    s, t = w['source_pair']
    assert len(g) == len(h) == 11 and min(s,t) >= 0
    out = w['output']
    assert 0 <= out < 18 and w['shifted_output'] == out + 1
    changed = 0
    for i, ((op,a,b),(op2,c,d)) in enumerate(zip(g,h)):
        assert op == op2
        for side,(orig,new) in enumerate(((a,c),(b,d))):
            assert new == orig+1 or (new == 0 and orig in (s,t))
            if new == 0:
                changed |= 1 << (2*i+side)
    assert changed == w['changed_pin_mask']
    assert sum(op == 0 and 2 in (a,b) for op,a,b in g) == w['or_readers_of_2'] < 2
    cols = [[False]*64, [True]*64] + [[bool(r>>i&1) for r in range(64)] for i in range(6)]
    fresh = []
    gate_columns = [[] for _ in g]
    for row in range(128):
        x = [bool(row>>i&1) for i in range(7)]
        f = any(x[a] and x[b] for a,b in edges)
        raw = evaluate(g,x)
        assert raw[out] == f
        assert evaluate(h,[True]+x)[out+1] == (f or x[0] or x[3])
        if not x[2]:
            for acc,val in zip(gate_columns,raw[7:]):
                acc.append(val)
    for i,col in enumerate(gate_columns):
        if col not in cols:
            cols.append(col)
            fresh.append(i)
    assert len(fresh) == w['fresh_cofactor_columns'] and len(fresh) >= 8
    chosen = fresh[:8]
    # Export the concrete 8-gate map plus actual six-input row numbers distinguishing its columns.
    pair_rows = {(i,j):next(k for k in range(64) if gate_columns[i][k] != gate_columns[j][k])
                 for i,j in combinations(chosen,2)}
    assert len(pair_rows) == 28
    print('Validated both physical circuits on all 128 rows. Direct OR readers', w['or_readers_of_2'])
    print('Official eight gate-index map',chosen)
    print('Distinct-column witnesses (i,j,row)',[(i,j,row) for (i,j),row in pair_rows.items()])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('artifact',type=Path)
    args = parser.parse_args()
    check(json.loads(args.artifact.read_text()))
