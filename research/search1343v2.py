#!/usr/bin/env python3
"""Exact SAT search for pequalnp L-meta-1343/14 or L-meta-1342/15.

In raw mode, any shorter circuit pads to 21 gates with dangling nullary ORs, keeping the
original output and dirty gate. Each gate selects two unordered pins. OMIT is
removed from the decoded pin list (AND identity true, OR identity false).
BAD is a real positive wire index past the final list, hence always false.
This represents zero, one, or two inputs, repeats, and every forward/out-of-
bounds read. The output may select a primary input, any gate, or BAD. Every
model is a real Lean circuit. No fanout, liveness or minimum-size assumption.

For normal mode, propagate constant and copy gates, merge identical binary
operation/operand pairs, and discard gates outside the output cone. The
nonconstant, nonprojection edge function still has a genuine output gate. If
21 gates survive, the original dirty gate survives. Otherwise prepend unused
ANDs on two true vertices of the selected row until there are 21 gates. SAT
numbers these vertices 0,1 internally, and decoding restores the official
vertex numbers. The dummy prefix is therefore dirty and uses the smallest
possible fanin pair. Its gates can share that pair with genuine gates.

All genuine gates are ancestors of the output. Sort their topological order by
(max parent index, min parent index, operation with AND first): if consecutive
keys are inverted, the second cannot read the first. Swapping and renumbering
these two strictly decreases the entire sequence lexicographically, because
all earlier keys stay fixed. The final output cannot participate in such a
swap: its preceding genuine gate is an ancestor and could only be its direct
parent. A finite minimum therefore has sorted keys and still ends in the
output. Equal keys in the genuine portion would describe the very same
expression, removed by the preceding duplicate elimination. Dummy/genuine
key ties are permitted. No dummy feeds any later gate.

For two distinct maximal false rows, assume every AND admits a single chosen
operand preserving its gate value at both rows. Replacing each AND by this
operand gives an OR-only circuit (with possible constants) dominating the
original and false at both rows. It is false on their union, which contains
an edge by maximality. Thus some AND has operand values 01 on one row and 10
on the other. Dually, projecting OR gates on two distinct true edge rows
gives an AND-only minorant true on both, hence on their independent
intersection, a contradiction. Constant and omitted pins pose no problem:
their values in each fixed circuit are independent of the test row.

The monotone edge function is fixed by its minimal true and maximal false
assignments. A witness is independently run on the full truth table.
"""
import argparse
import json
from itertools import combinations
import multiprocessing
from pathlib import Path
import subprocess
import tempfile

POINTS, GATES = 11, 21
BAD, OMIT = POINTS + GATES, POINTS + GATES + 1
EDGES = ((0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7),
         (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9))
EDGE_ROWS = tuple((1 << a) | (1 << b) for a, b in EDGES)
SHARDS = {14: ('L-meta-1343', (1, 2, 6, 9)), 15: ('L-meta-1342', (0, 1, 5, 6))}


def edge_value(bits):
    return any(bits & edge == edge for edge in EDGE_ROWS)


def maximal_independent(bits):
    return not edge_value(bits) and all(
        bits & (1 << p) or edge_value(bits | (1 << p)) for p in range(POINTS))


class Encoding:
    def __init__(self, shard, mode):
        self.shard = shard
        self.dirty_row = sum(1 << p for p in SHARDS[shard][1])
        self.input_order = list(range(POINTS))
        if mode == 'normal':
            first = SHARDS[shard][1][:2]
            self.input_order = list(first) + [p for p in self.input_order if p not in first]
        self.nvars = 0
        self.clauses = []
        self.true = self.new()
        self.clauses.append([self.true])
        negatives = [bits for bits in range(1 << POINTS) if maximal_independent(bits)]
        assert len(EDGE_ROWS) == 16 and len(negatives) == 24 and self.dirty_row in negatives
        rows = list(EDGE_ROWS) + negatives
        dirty_at = rows.index(self.dirty_row)
        values = [[self.true if bits & (1 << p) else -self.true for p in self.input_order]
                  for bits in rows]
        self.gate_data = []
        pin_prefixes = []
        row_pins = [[] for _ in rows]
        dirty_choices = []
        for j in range(GATES):
            is_and = self.new()
            wires = list(range(POINTS + j))
            if mode == 'raw':
                wires += [BAD, OMIT]
            left, left_prefix = self.one_hot(len(wires))
            right, right_prefix = self.one_hot(len(wires))
            # left index <= right index, so exchanging two commutative pins
            # does not duplicate a circuit. Equal pin indices remain possible.
            if mode == 'raw':
                for lprefix, rprefix in zip(left_prefix, right_prefix):
                    self.add(-rprefix, lprefix)
            else:
                self.add(-right_prefix[0])
                for lprefix, rprefix in zip(left_prefix, right_prefix[1:]):
                    self.add(-rprefix, lprefix)
            self.gate_data.append((is_and, wires, left, right))
            pin_prefixes.append((left_prefix, right_prefix))
            for r, current in enumerate(values):
                available = current + [-self.true, is_and] if mode == 'raw' else current
                a, b, out = self.new(), self.new(), self.new()
                row_pins[r].append((a, b))
                self.mux(left, available, a)
                self.mux(right, available, b)
                # AND branch: out iff a AND b. OR branch: out iff a OR b.
                self.add(-is_and, -out, a)
                self.add(-is_and, -out, b)
                self.add(-is_and, out, -a, -b)
                self.add(is_and, out, -a)
                self.add(is_and, out, -b)
                self.add(is_and, -out, a, b)
                current.append(out)
                if r == dirty_at:
                    witness = self.new()
                    self.add(-witness, is_and)
                    self.add(-witness, out)
                    dirty_choices.append(witness)
        self.add(*dirty_choices)
        self.separators(row_pins, range(len(EDGE_ROWS)), False)
        self.separators(row_pins, range(len(EDGE_ROWS), len(rows)), True)
        if mode == 'normal':
            self.canonical_cone(pin_prefixes)
            self.outputs, self.output_sel = [POINTS + GATES - 1], [self.true]
            for r, current in enumerate(values):
                self.add(current[-1] if r < len(EDGE_ROWS) else -current[-1])
        else:
            self.outputs = list(range(POINTS + GATES)) + [BAD]
            self.output_sel, _ = self.one_hot(len(self.outputs))
            for r, current in enumerate(values):
                for pick, candidate in zip(self.output_sel, current + [-self.true]):
                    self.add(-pick, candidate if r < len(EDGE_ROWS) else -candidate)

    def separators(self, row_pins, rows, require_and):
        # mixed[row][j] says that gate j has the required operation and its
        # two operands differ on this row. Given two mixed rows, opposite
        # orientations are equivalent to the first operand changing value.
        mixed = {}
        for r in rows:
            mixed[r] = []
            for j, (a, b) in enumerate(row_pins[r]):
                op = self.gate_data[j][0]
                kind = op if require_and else -op
                flag = self.new()
                self.add(-flag, kind)
                self.add(-flag, a, b)
                self.add(-flag, -a, -b)
                self.add(-kind, -a, b, flag)
                self.add(-kind, a, -b, flag)
                mixed[r].append(flag)
        for r, s in combinations(rows, 2):
            witnesses = []
            for j in range(GATES):
                bit_r, bit_s = row_pins[r][j][0], row_pins[s][j][0]
                w = self.new()
                self.add(-w, mixed[r][j])
                self.add(-w, mixed[s][j])
                self.add(-w, bit_r, bit_s)
                self.add(-w, -bit_r, -bit_s)
                witnesses.append(w)
            self.add(*witnesses)

    def same_choice(self, previous, current):
        # Domains grow by one; current may have a source outside previous.
        equal = self.new()
        for a, b in zip(previous, current):
            self.add(-a, -b, equal)
            self.add(-equal, -a, b)
        return equal

    def canonical_cone(self, prefixes):
        dummy = [self.new() for _ in range(GATES)]
        self.add(-dummy[-1])
        for j, (op, _, left, right) in enumerate(self.gate_data):
            self.add(-dummy[j], op)
            self.add(-dummy[j], left[0])
            self.add(-dummy[j], right[1])
            if j < GATES - 1:
                users = []
                for _, _, later_l, later_r in self.gate_data[j+1:]:
                    users.extend((later_l[POINTS+j], later_r[POINTS+j]))
                self.add(dummy[j], *users)
                for user in users:
                    self.add(-dummy[j], -user)
            if j == 0:
                continue
            self.add(-dummy[j], dummy[j-1])
            prev_op, _, prev_l, prev_r = self.gate_data[j-1]
            prev_lp, prev_rp = prefixes[j-1]
            lp, rp = prefixes[j]
            # Maximum parent is the right pin since left < right. Ties are
            # resolved by the left pin and then by AND before OR.
            for old, new in zip(prev_rp, rp):
                self.add(-new, old)
            same_max = self.same_choice(prev_r, right)
            for old, new in zip(prev_lp, lp):
                self.add(-same_max, -new, old)
            same_min = self.same_choice(prev_l, left)
            self.add(-same_max, -same_min, prev_op, -op)
            # Between genuine gates, same parent pair forces different ops.
            # A dummy predecessor may use exactly the same key.
            self.add(dummy[j-1], -same_max, -same_min, -prev_op, -op)
            self.add(dummy[j-1], -same_max, -same_min, prev_op, op)

    def new(self):
        self.nvars += 1
        return self.nvars

    def add(self, *lits):
        if self.true not in lits:
            self.clauses.append([lit for lit in lits if lit != -self.true])

    def one_hot(self, size):
        # prefix[i] means that a choice with index <= i was made.
        choices = [self.new() for _ in range(size)]
        prefixes = [choices[0]]
        for choice in choices[1:]:
            prev, here = prefixes[-1], self.new()
            self.add(-prev, here)
            self.add(-choice, here)
            self.add(-prev, -choice)
            self.add(-here, prev, choice)
            prefixes.append(here)
        self.add(prefixes[-1])
        return choices, prefixes

    def mux(self, selections, values, out):
        for sel, value in zip(selections, values):
            self.add(-sel, -out, value)
            self.add(-sel, out, -value)

    def dimacs(self, path):
        with path.open('w', encoding='ascii') as f:
            f.write(f'p cnf {self.nvars} {len(self.clauses)}\n')
            for clause in self.clauses:
                f.write(' '.join(map(str, clause)) + ' 0\n')

    def decode(self, model):
        model = set(model)
        def pick(selectors, wires):
            chosen = [w for sel, w in zip(selectors, wires) if sel in model]
            if len(chosen) != 1:
                raise ValueError('incomplete or inconsistent SAT model: expected exactly one pin')
            return chosen[0]
        def official_index(p):
            return self.input_order[p] if p < POINTS else p
        gates = []
        for op, wires, left, right in self.gate_data:
            if (op in model) == (-op in model):
                raise ValueError('missing or inconsistent operation bit')
            pins = [pick(left, wires), pick(right, wires)]
            gates.append({'op': 'and' if op in model else 'or',
                          'inputs': [official_index(p) for p in pins if p != OMIT]})
        circuit = {'gates': gates, 'output': official_index(pick(self.output_sel, self.outputs))}
        verify(circuit, self.shard)
        return circuit


def verify(circuit, shard):
    dirty_row = sum(1 << p for p in SHARDS[shard][1])
    gates, out = circuit['gates'], circuit['output']
    if len(gates) > GATES or not isinstance(out, int) or out < 0:
        raise ValueError('invalid circuit size or output index')
    for bits in range(1 << POINTS):
        wires = [bool((bits >> p) & 1) for p in range(POINTS)]
        dirty = False
        for gate in gates:
            pins = gate['inputs']
            if gate['op'] not in ('and', 'or') or len(pins) > 2 or any(
                    not isinstance(p, int) or p < 0 for p in pins):
                raise ValueError('invalid gate')
            args = [wires[p] if p < len(wires) else False for p in pins]
            bit = all(args) if gate['op'] == 'and' else any(args)
            dirty |= gate['op'] == 'and' and bit
            wires.append(bit)
        if (wires[out] if out < len(wires) else False) != edge_value(bits):
            raise ValueError(f'circuit disagrees at input mask {bits}')
        if bits == dirty_row and not dirty:
            raise ValueError(f'circuit misses official shard {shard}')


def pysat_worker(path, solver, pipe):
    try:
        from pysat.formula import CNF
        from pysat.solvers import Solver
        with Solver(name=solver, bootstrap_with=CNF(from_file=path).clauses) as sat:
            verdict = sat.solve()
            pipe.send(('SAT', sat.get_model()) if verdict is True else
                      ('UNSAT', []) if verdict is False else ('UNKNOWN', []))
    except Exception as exc:
        pipe.send(('ERROR', str(exc)))
    finally:
        pipe.close()


def run_pysat(path, solver, timeout):
    recv, send = multiprocessing.Pipe(duplex=False)
    proc = multiprocessing.Process(target=pysat_worker, args=(str(path), solver, send))
    proc.start()
    send.close()
    try:
        if timeout and not recv.poll(timeout):
            return 'UNKNOWN', []
        verdict, model = recv.recv()
        if verdict == 'ERROR':
            raise RuntimeError(model)
        return verdict, model
    finally:
        recv.close()
        if proc.is_alive():
            proc.terminate()
        proc.join()


def run_cadical(path, binary, timeout, proof):
    # External CaDiCaL emits a DRAT certificate when a proof pathname is given.
    cmd = [binary, '-q']
    if timeout:
        cmd += ['-t', str(timeout)]
    cmd.append(str(path))
    if proof:
        if proof.exists():
            raise ValueError('proof path already exists')
        cmd.append(str(proof))
    try:
        proc = subprocess.run(cmd, text=True, capture_output=True,
                              timeout=timeout + 15 if timeout else None)
    except subprocess.TimeoutExpired:
        return 'UNKNOWN', []
    lines = proc.stdout.splitlines()
    status = [line.strip() for line in lines if line.startswith('s ')]
    if proc.returncode == 10 and status == ['s SATISFIABLE']:
        return 'SAT', [int(tok) for line in lines if line.startswith('v ') for tok in line.split()[1:] if tok != '0']
    if proc.returncode == 20 and status == ['s UNSATISFIABLE']:
        return 'UNSAT', []
    if proc.returncode in (0, 124) and status in ([], ['s UNKNOWN'], ['s INDETERMINATE']):
        return 'UNKNOWN', []
    raise RuntimeError(f'CaDiCaL exit {proc.returncode}, status {status}: {proc.stderr[-500:]}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--shard', choices=(14, 15), type=int, default=14)
    parser.add_argument('--mode', choices=('normal', 'raw'), default='normal')
    parser.add_argument('--dimacs', type=Path, help='write deterministic CNF, including when solving')
    solver = parser.add_mutually_exclusive_group()
    solver.add_argument('--pysat', metavar='SOLVER', help='PySAT backend, for example cadical195')
    solver.add_argument('--cadical', metavar='PATH', help='external CaDiCaL binary')
    parser.add_argument('--timeout', type=int, default=0, help='solver wall seconds, zero means unlimited')
    parser.add_argument('--proof', type=Path, help='external CaDiCaL proof output path')
    parser.add_argument('--witness', type=Path, help='write the verified SAT circuit as JSON')
    args = parser.parse_args()
    if args.timeout < 0 or (args.proof and not args.cadical):
        parser.error('negative timeout or proof request without external CaDiCaL')
    if not (args.dimacs or args.pysat or args.cadical):
        parser.error('choose --dimacs, --pysat, or --cadical')
    enc = Encoding(args.shard, args.mode)
    gap, dirty = SHARDS[args.shard]
    print(f'{gap} shard={args.shard}/25 dirty={dirty} graph={EDGES}', flush=True)
    print(f'encoding=v2 mode={args.mode} rows=16+24 size=21 vars={enc.nvars} clauses={len(enc.clauses)}', flush=True)
    with tempfile.TemporaryDirectory() as tmp:
        path = args.dimacs or Path(tmp) / f'shard{args.shard}.cnf'
        enc.dimacs(path)
        if args.cadical:
            verdict, model = run_cadical(path, args.cadical, args.timeout, args.proof)
        elif args.pysat:
            verdict, model = run_pysat(path, args.pysat, args.timeout)
        else:
            print('ENCODED')
            return
        if verdict == 'SAT':
            circuit = enc.decode(model)
            result = json.dumps(circuit, separators=(',', ':'))
            if args.witness:
                args.witness.write_text(result + '\n', encoding='utf-8')
            print(f'SAT; independently verified all 2048 inputs and shard {args.shard}')
            print(result)
        else:
            print(verdict)


if __name__ == '__main__':
    main()
