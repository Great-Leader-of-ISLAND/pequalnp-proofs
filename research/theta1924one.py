"""Restrict signed theta encoding to an ordinary AND/OR circuit with one available NOT."""
import argparse
import itertools
import json
from pathlib import Path
import theta1924 as base
from theta1924guards import Guarded


class SingleNot(Guarded):
    def __init__(self, size, fixed=None, first=None):
        super().__init__(size, fixed, first)
        if fixed is None and first is None:
            identity=(0,1,2,3,4,5,6)
            swap_arms=(0,1,2,5,6,3,4)
            reverse_arms=(1,0,2,4,3,6,5)
            rotations=(identity,swap_arms,reverse_arms,tuple(swap_arms[x] for x in reverse_arms))
            assert all({tuple(sorted((perm[a],perm[b]))) for a,b in base.EDGES}
                       ==set(base.EDGES) for perm in rotations)
            left,right,_=self.nodes[0]
            for a,b in itertools.combinations(range(7),2):
                orbit=[tuple(sorted((perm[a],perm[b]))) for perm in rotations]
                if (b,a)!=min((y,x) for x,y in orbit):
                    self.add(-left[a],-right[b])
        if fixed is None:
            # Ready nodes sharing their maximum input index are independent.
            # Break their ties by the smaller input index, also at the raw layer.
            for i in range(1,size):
                pl,pr,_=self.nodes[i-1]
                al,ar,_=self.nodes[i]
                for b in range(1,len(pr)):
                    for a in range(b):
                        for c in range(a):
                            self.add(-pr[b],-ar[b],-pl[a],-al[c])
        # Variables inside the base encoding always denote the signal whose
        # value at all-zero input is zero. t_j recovers an actual circuit
        # signal by xoring that normalized result with its all-zero value.
        source=[self.fresh() for _ in range(7+size-1)]
        self.onehot(source)
        self.source=source
        self.actual_gates=[]
        phases=[]
        sample=list(itertools.product((False,True),repeat=2))
        tables=[tuple(base.evaluate_gate(k,a,b) for a,b in sample) for k in range(4)]
        for i,(left,right,ops) in enumerate(self.nodes):
            effective=[]
            flips=[]
            for choices in (left,right):
                phase=self.fresh()
                flip=self.fresh()
                eff=self.fresh()
                flips.append(flip)
                effective.append(eff)
                for j,selected in enumerate(choices):
                    # A complemented use is permitted only from the selected
                    # global source. A forward reference cannot be selected.
                    self.add(-selected,-flip,source[j])
                    if j<7:
                        self.add(-selected,-phase)
                    else:
                        prior=phases[j-7]
                        self.add(-selected,-prior,phase)
                        self.add(-selected,prior,-phase)
                for p,f in sample:
                    self.add(-phase if p else phase,-flip if f else flip,
                             eff if p^f else -eff)
            join=self.fresh()
            self.actual_gates.append((join,*flips))
            t=self.fresh()
            phases.append(t)
            for j,ea,eb in itertools.product((False,True),repeat=3):
                def operation(a,b):
                    return ((a^ea) or (b^eb)) if j else ((a^ea) and (b^eb))
                actual_zero=operation(False,False)
                table=tuple(operation(a,b)^actual_zero for a,b in sample)
                option=tables.index(table)
                guard=(-join if j else join, -effective[0] if ea else effective[0],
                       -effective[1] if eb else effective[1])
                self.add(*guard,ops[option])
                self.add(*guard,t if actual_zero else -t)
        self.add(-phases[-1])


    def decode(self, path):
        super().decode(path)
        model={int(v) for row in path.read_text().splitlines() if row.startswith('v ')
               for v in row[2:].split() if int(v)>0}
        def index(options):
            found=[i for i,v in enumerate(options) if v in model]
            assert len(found)==1
            return found[0]
        source=index(self.source)
        actual=[]
        wires=list(range(7))
        inv=None
        for (left,right,_),(join,fa,fb) in zip(self.nodes,self.actual_gates):
            pins=[]
            for selector,flip in ((left,fa),(right,fb)):
                idx=index(selector)
                if flip in model:
                    assert idx==source
                    if inv is None:
                        inv=7+len(actual)
                        actual.append(('not',wires[idx],None))
                    pins.append(inv)
                else:
                    pins.append(wires[idx])
            wires.append(7+len(actual))
            actual.append(('or' if join in model else 'and',*pins))
        for row in range(128):
            vals=[bool(row & (1<<i)) for i in range(7)]
            for op,a,b in actual:
                vals.append(not vals[a] if op=='not' else
                            (vals[a] or vals[b]) if op=='or' else (vals[a] and vals[b]))
            assert vals[-1]==base.target(row)
        print(json.dumps({'ordinary_circuit':actual,'inverters':int(inv is not None),
                          'rows_checked':128}),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--size',type=int,default=10)
    parser.add_argument('--write',type=Path)
    parser.add_argument('--decode',type=Path)
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument('--control',action='store_true')
    mode.add_argument('--neg-control',action='store_true')
    parser.add_argument('--first',nargs=2,type=int)
    args=parser.parse_args()
    base.selftest()
    fixed=base.control() if args.control else None
    if args.neg_control:
        fixed=base.control()[:-1]+[(13,16,3),(13,17,1)]
        assert all(base.evaluate(fixed,r)==base.target(r) for r in range(128))
    e=SingleNot(len(fixed) if fixed else args.size,fixed,args.first)
    if args.write:e.write(args.write)
    if args.decode:e.decode(args.decode)
