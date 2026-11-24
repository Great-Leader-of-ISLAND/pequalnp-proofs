"""Exact semantic-first-NOT search for the nine-input Petersen-minus-one step.

The reference's raw model permits omitted, invalid and repeated pins, dead
wires, early output and all suffix orders. Wire 9 is NOT(x0): on row 0
any OR is false and any nonempty AND with a real pin is false. A nullary
AND would instead be constant true. The other possibilities are distinguished
by setting only x0 or all inputs except x0. Thus a circuit in this shard has
a first NOT reading x0 (a discarded second pin has no effect). The first gate
cannot be absent, because then the default wire is always false.
"""
import argparse
from pathlib import Path
import json
import time
import petersen670 as ref


def encode(bound):
    model = ref.Encoding('raw', bound=bound, symmetry=False)
    ops, ls, rs, left, right = model.gs[0]
    model.add(ops[2]); model.add(left[ls.index(0)]); model.add(right[rs.index(model.omit)])
    # Count effective reader gates, so one binary reading both signed wires is one event.
    readers = []
    for _, ls, rs, left, right in model.gs[1:]:
        selected = [left[ls.index(a)] for a in (0,9)] + [right[rs.index(a)] for a in (0,9)]
        read = model.var()
        for pin in selected: model.add(-pin,read)
        model.add(-read,*selected)
        for earlier in readers: model.add(-read,-earlier)
        readers.append(read)
    return model


def prefix_control():
    original = ref.cover_control()
    def shift(i): return 10 if i == 0 else i + 2*int(i >= ref.N)
    return {'gates': [{'op': 'not', 'inputs': [0]}, {'op': 'not', 'inputs': [9]}] + [
        {'op': g['op'], 'inputs': [shift(i) for i in g['inputs']]} for g in original['gates']],
        'output': shift(original['output'])}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--directory', type=Path, required=True)
    parser.add_argument('--solver', required=True); parser.add_argument('--checker', required=True)
    parser.add_argument('--seconds', type=int, default=600); parser.add_argument('--control',action='store_true')
    args = parser.parse_args(); d = args.directory; d.mkdir(exist_ok=False)
    control = prefix_control()
    assert len(control['gates']) == 18 and not ref.counterexamples(control,18)
    model = encode(18 if args.control else 15)
    if args.control:
        for structure, gate in zip(model.gs,control['gates']):
            ops, ls, rs, left, right = structure
            a, *extra = sorted(gate['inputs'])
            b = extra[0] if extra else model.omit
            model.add(ops[('and','or','not').index(gate['op'])]); model.add(left[ls.index(a)]); model.add(right[rs.index(b)])
        model.add(model.osel[model.outs.index(control['output'])])
    for row in ref.seed_rows('frontier'): model.add_row(row)
    end = time.monotonic() + args.seconds
    for n in range(513):
        cnf = d/'current.cnf'; proof=d/f'round{n}.drat'; model.dimacs(cnf)
        (d/'rows.json').write_text(json.dumps(model.rows))
        print('round',n,'rows',len(model.rows),'variables',model.top,'clauses',len(model.clauses),flush=True)
        try:
            verdict, values = ref.run_cadical(args.solver,cnf,proof,ref.budget(end),not args.control)
            if verdict=='UNSAT':
                assert not args.control, 'known 17-gate control rejected'
                ok = ref.verify_proof(args.checker,cnf,proof,ref.budget(end),d/'check.log')
                print('DRAT-VERIFIED on this encoded instance' if ok else 'UNCHECKED'); return
            if verdict!='SAT': print('UNKNOWN'); return
        except TimeoutError:
            print('UNKNOWN: budget reached'); return
        c = model.decode(values); assert c['gates'][0] == {'op':'not','inputs':[0]}
        bad = ref.counterexamples(c,18 if args.control else 15)
        assert not (set(bad)&set(model.rows))
        if not bad:
            print('PASS known 17-gate control, 512 inputs' if args.control else 'WITNESS verified all 512 inputs')
            if not args.control: (d/'witness.json').write_text(json.dumps(c))
            return
        for row in ref.refine(bad,8): model.add_row(row)

if __name__=='__main__': main()
