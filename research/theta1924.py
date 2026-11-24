"""Exact decision experiment for normalized signed AND/OR circuits for theta(2,3,3)."""
import argparse
import itertools
import json
from pathlib import Path

EDGES = ((0, 2), (1, 2), (0, 3), (3, 4), (1, 4), (0, 5), (5, 6), (1, 6))
OPS = ("and", "or", "left_only", "right_only")


def evaluate_gate(op, left, right):
    return (left and right, left or right, left and not right, right and not left)[op]


def target(row):
    return any((row >> a) & (row >> b) & 1 for a, b in EDGES)


def evaluate(circuit, row):
    values = [bool(row & (1 << i)) for i in range(7)]
    for a, b, op in circuit:
        values.append(evaluate_gate(op, values[a], values[b]))
    return values[-1]


def control():
    # (A AND (C OR D OR F)) OR (B AND (C OR E OR G)) OR DE OR FG.
    gates = [(2, 3, 1), (3, 4, 0), (2, 4, 1), (5, 6, 0),
             (5, 7, 1), (6, 9, 1), (8, 10, 1), (0, 11, 0),
             (1, 12, 0), (14, 15, 1), (13, 16, 1)]
    return gates


class Encoding:
    def __init__(self, size, fixed=None):
        self.nvars = 0
        self.clauses = []
        self.nodes = []
        self.values = []
        for i in range(size):
            n = 7 + i
            left = [self.fresh() for _ in range(n-1)]
            right = [self.fresh() for _ in range(n)]
            ops = [self.fresh() for _ in OPS]
            self.nodes.append((left, right, ops))
            for choices in (left, right, ops):
                self.onehot(choices)
            for a in range(n-1):
                for b in range(a+1):
                    self.add(-left[a], -right[b])
            # Choose topological order by nondecreasing maximum source index.
            # The ready gate with the smallest maximum can always run first.
            if i:
                last_right = self.nodes[i-1][1]
                for a in range(len(last_right)):
                    for b in range(a):
                        self.add(-last_right[a], -right[b])
            if fixed:
                a, b, op = fixed[i]
                self.add(left[a])
                self.add(right[b])
                self.add(ops[op])
            vals = []
            for row in range(1, 128):
                lp = self.fresh()
                rp = self.fresh()
                out = self.fresh()
                vals.append(out)
                for port, choices in ((lp, left), (rp, right)):
                    for idx, sel in enumerate(choices):
                        if idx < 7:
                            self.add(-sel, port if row & (1 << idx) else -port)
                        else:
                            wire = self.values[idx-7][row-1]
                            self.add(-sel, -wire, port)
                            self.add(-sel, wire, -port)
                for op, enable in enumerate(ops):
                    for aa, bb in itertools.product((False,True), repeat=2):
                        self.add(-enable, -lp if aa else lp, -rp if bb else rp,
                                 out if evaluate_gate(op, aa, bb) else -out)
                if i == size-1:
                    self.add(out if target(row) else -out)
            self.values.append(vals)
        # All seven inputs are essential. Each must appear at least once.
        for idx in range(7):
            self.add(*(p[idx] for left,right,_ in self.nodes for p in (left,right) if idx<len(p)))

    def fresh(self):
        self.nvars += 1
        return self.nvars

    def add(self, *lits):
        self.clauses.append(lits)

    def onehot(self, choices):
        self.add(*choices)
        for a, b in itertools.combinations(choices, 2):
            self.add(-a, -b)

    def write(self, path):
        with path.open('w') as f:
            f.write(f'p cnf {self.nvars} {len(self.clauses)}\n')
            for clause in self.clauses:
                f.write(' '.join(map(str, clause)) + ' 0\n')

    def decode(self, path):
        model = set()
        for row in path.read_text().splitlines():
            if row.startswith('v '):
                model.update(int(t) for t in row[2:].split() if int(t)>0)
        def chosen(selectors):
            hit = [i for i, v in enumerate(selectors) if v in model]
            assert len(hit)==1, hit
            return hit[0]
        circuit = [tuple(map(chosen, data)) for data in self.nodes]
        assert all(evaluate(circuit, row)==target(row) for row in range(128))
        print(json.dumps({"circuit": circuit, "rows_checked": 128}), flush=True)


def selftest():
    assert [b for _,b,_ in control()] == sorted(b for _,b,_ in control())
    assert all(evaluate(control(), row)==target(row) for row in range(128))
    # Every normalize-at-zero De Morgan operation is represented. Check all
    # possible source phases and the new output phase on four bit inputs.
    vals = list(itertools.product((False,True), repeat=2))
    tables = {tuple(evaluate_gate(op, a, b) for a,b in vals) for op in range(4)}
    for inc_a,inc_b,join in itertools.product((False,True), repeat=3):
        raw = tuple((a^inc_a)|(b^inc_b) if join else (a^inc_a)&(b^inc_b) for a,b in vals)
        assert tuple(x^raw[0] for x in raw) in tables
    # Verify vertex-cover number and the two-context LCA obstruction.
    independent = [r for r in range(128) if not target(r)]
    assert max(bin(s).count('1') for s in independent)==3
    for a,b in EDGES:
        sig = lambda s: tuple(target(s | (x<<a) | (y<<b)) for x,y in vals)
        assert sig(0)==(0,0,0,1)
        assert any(not (s & ((1<<a)|(1<<b))) and sig(s)==(0,1,1,1) for s in independent)
    # On an assignment of the other variables, the two leaf-to-LCA
    # subformulas and outer positive context are each a monotone unary function.
    uf = [(0,0),(0,1),(1,1)]
    for p,n,outer,join in itertools.product(uf,uf,uf,(False,True)):
        combine = (lambda x,y: x|y) if join else (lambda x,y: x&y)
        original = [outer[combine(p[x],n[1-x])] for x in (0,1)]
        if original[0]<=original[1]:
            assert original == [outer[combine(p[x],n[int(join)])] for x in (0,1)]
    print('All 128 control rows, eight phase normalizations, graph obstructions and read-twice identities verified.')


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--size', type=int, default=10)
    parser.add_argument('--write', type=Path)
    parser.add_argument('--decode', type=Path)
    parser.add_argument('--control', action='store_true')
    args=parser.parse_args()
    selftest()
    if args.write or args.decode:
        enc=Encoding(11 if args.control else args.size, control() if args.control else None)
        if args.write: enc.write(args.write)
        if args.decode: enc.decode(args.decode)
