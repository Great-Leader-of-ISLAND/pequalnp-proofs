"""Bounded independent CNF check on a known 23-gate witness; no SAT solver."""
from itertools import combinations
from pathlib import Path
import importlib.util

p = Path(__file__).with_name('search1343v2.py')
spec = importlib.util.spec_from_file_location('enc1343', p)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
m.GATES = 23
m.BAD, m.OMIT = 34, 35


def cover_formula():
    cover = next(frozenset(c) for c in combinations(range(11), 7)
                 if all(a in c or b in c for a,b in m.EDGES))
    groups = {p: [] for p in sorted(cover)}
    for a,b in m.EDGES:
        c,d = (a,b) if a in cover else (b,a)
        groups[c].append(d)
    gates = []
    def gate(op, a, b):
        gates.append((op, a, b))
        return 10+len(gates)
    def union(wires):
        w = wires[0]
        for v in wires[1:]:
            w = gate(False, w, v)
        return w
    final = union([gate(True, c, union(neighbors)) for c,neighbors in groups.items()])
    assert len(gates) == 22 and final == 32
    return gates


def reordered(gates, inputs):
    remap = {v:i for i,v in enumerate(inputs)}
    pending = dict(enumerate(gates, 11))
    ordered = [(True, 0, 1)]
    while pending:
        ready = [(max(remap[a],remap[b]), min(remap[a],remap[b]), not op, w) for w,(op,a,b) in pending.items()
                 if a in remap and b in remap]
        high,low,neg,w = min(ready)
        remap[w] = 11+len(ordered)
        ordered.append((not neg,low,high))
        del pending[w]
    return ordered


class Annotated(m.Encoding):
    def separators(self, row_pins, indices, and_gate):
        if not hasattr(self,'dirty_ids'):
            self.dirty_ids = list(self.clauses[-1])
            self.sep_blocks = []
        start = self.nvars + len(indices)*m.GATES + 1
        self.sep_blocks.append((start, indices, and_gate))
        super().separators(row_pins, indices, and_gate)

    def canonical_cone(self, prefixes):
        self.dummy_start = self.nvars+1
        super().canonical_cone(prefixes)


def check(shard):
    enc = Annotated(shard, 'normal')
    gates = reordered(cover_formula(), enc.input_order)
    assignments = {enc.true}
    def put(var, bit):
        assert (-var if bit else var) not in assignments
        assignments.add(var if bit else -var)
    for j,((kind,a,b),(op,wires,left,right)) in enumerate(zip(gates,enc.gate_data)):
        put(op,kind)
        put(enc.dummy_start+j, j==0)
        for i,w in enumerate(wires):
            put(left[i],w==a)
            put(right[i],w==b)
    rows = list(m.EDGE_ROWS)+[x for x in range(2048) if m.maximal_independent(x)]
    operands=[]
    for bits in rows:
        vals=[bool(bits & (1<<p)) for p in enc.input_order]
        pairs=[]
        for j,(kind,a,b) in enumerate(gates):
            x,y=vals[a],vals[b]
            pairs.append((x,y))
            vals.append(x and y if kind else x or y)
            if bits==enc.dirty_row:
                put(enc.dirty_ids[j],kind and vals[-1])
        assert vals[-1] == m.edge_value(bits)
        operands.append(pairs)
    for var,indices,kind in enc.sep_blocks:
        for r,s in combinations(indices,2):
            for j,(op,_,_) in enumerate(gates):
                x,y=operands[r][j]; u,v=operands[s][j]
                put(var, op==kind and x!=y and u!=v and x!=u)
                var+=1
    # With all choices and separator witnesses specified, the remaining
    # Tseitin variables are uniquely determined by ordinary unit propagation.
    open_clauses=enc.clauses
    while open_clauses:
        pending=[]
        before=len(assignments)
        for clause in open_clauses:
            if any(v in assignments for v in clause):
                continue
            remaining=[v for v in clause if -v not in assignments]
            assert remaining, (shard,clause)
            if len(remaining)==1:
                assignments.add(remaining[0])
            else:
                pending.append(remaining)
        assert not pending or len(assignments)>before, (shard,len(pending))
        open_clauses=pending
    model=enc.decode(assignments)
    assert len(model['gates'])==23
    print(f'shard {shard}: known 23-gate witness satisfies all {len(enc.clauses)} clauses and 2048 inputs')


if __name__ == '__main__':
    for shard in (14,15):
        check(shard)
