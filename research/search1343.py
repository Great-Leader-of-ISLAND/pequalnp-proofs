#!/usr/bin/env python3
"""Exact SAT search for pequalnp L-meta-1343/14 or L-meta-1342/15.

In raw mode, any shorter circuit pads to 21 gates with dangling nullary ORs, keeping the
original output and dirty gate. Each gate selects two unordered pins. OMIT is
removed from the decoded pin list (AND identity true, OR identity false).
BAD is a real positive wire index past the final list, hence always false.
This represents zero, one, or two inputs, repeats, and every forward/out-of-
bounds read. The output may select a primary input, any gate, or BAD. Every
model is a real Lean circuit. No fanout, liveness or minimum-size assumption.

In normal mode all 21 gates have two distinct earlier wires and the final
wire is the output. This preserves SAT and UNSAT for EACH selected dirty
row: first propagate constants and bypass empty, unary, repeated and invalid
reads (invalid reads are false); drop gates after the output. The graph edge
function is neither a constant nor a projection. If this removes no gate
from a size-21 circuit, the original dirty gate is still present. Otherwise
at most 20 gates remain (also true for a smaller original). Prepend enough
unused gates to reach 21, each AND of two distinct true inputs of the selected
row. Shift the old gate indices and keep the old final output. These unused
ANDs restore dirtiness even if all old dirty gates were removed. No gate is
required to feed a later gate. Every normal model is itself a raw circuit.

The monotone edge function is fixed by its minimal true and maximal false
assignments. A witness is independently run on the full truth table.
"""
import argparse
import json
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
        self.nvars = 0
        self.clauses = []
        self.true = self.new()
        self.clauses.append([self.true])
        negatives = [bits for bits in range(1 << POINTS) if maximal_independent(bits)]
        assert len(EDGE_ROWS) == 16 and len(negatives) == 24 and self.dirty_row in negatives
        rows = list(EDGE_ROWS) + negatives
        dirty_at = rows.index(self.dirty_row)
        values = [[self.true if bits & (1 << p) else -self.true for p in range(POINTS)]
                  for bits in rows]
        self.gate_data = []
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
            for r, current in enumerate(values):
                available = current + [-self.true, is_and] if mode == 'raw' else current
                a, b, out = self.new(), self.new(), self.new()
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
        if mode == 'normal':
            self.outputs, self.output_sel = [POINTS + GATES - 1], [self.true]
            for r, current in enumerate(values):
                self.add(current[-1] if r < len(EDGE_ROWS) else -current[-1])
        else:
            self.outputs = list(range(POINTS + GATES)) + [BAD]
            self.output_sel, _ = self.one_hot(len(self.outputs))
            for r, current in enumerate(values):
                for pick, candidate in zip(self.output_sel, current + [-self.true]):
                    self.add(-pick, candidate if r < len(EDGE_ROWS) else -candidate)

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
        gates = []
        for op, wires, left, right in self.gate_data:
            if (op in model) == (-op in model):
                raise ValueError('missing or inconsistent operation bit')
            pins = [pick(left, wires), pick(right, wires)]
            gates.append({'op': 'and' if op in model else 'or',
                          'inputs': [p for p in pins if p != OMIT]})
        circuit = {'gates': gates, 'output': pick(self.output_sel, self.outputs)}
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
    if proc.returncode in (0, 124) and status in ([], ['s UNKNOWN']):
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
    print(f'mode={args.mode} rows=16+24 size=21 vars={enc.nvars} clauses={len(enc.clauses)}', flush=True)
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
