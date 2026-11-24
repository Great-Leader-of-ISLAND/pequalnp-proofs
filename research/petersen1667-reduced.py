"""Additional exact simplifications for the normalized Petersen suffix encoding.

If a binary gate reads both B and one of B's direct arguments a, then it is
an alias of B or a (by associativity/idempotence or absorption) when B is
binary, and is constant when B is NOT(a). A NOT of NOT is an alias as well.
Substitute the alias or propagate the constant. The fixed first gate is
retained, and padding is allowed after it. Hence some normalized minimum
suffix satisfies every added local clause. Keep raw mode untouched. The
actual scalar and CNF positive controls use the subclass too.
"""
import petersen1667 as base

class Reduced(base.Encoding):
    def __init__(self, mode, *args, **kwargs):
        super().__init__(mode,*args,**kwargs)
        if mode!='normal': return
        # Slots are topological. Finite raw operands in every sorted binary
        # gate have different pins, with the larger wire in the right slot.
        for i,(iops,ipins,irpins,il,ir) in enumerate(self.gs):
            # Indices 0 and 1 are also essential in the tail: on x1=0,
            # x4 alone witnesses the x0 derivative, and symmetrically x2.
            for a in (0,1): self.add(-ir[irpins.index(base.N)],-il[ipins.index(a)])
            for j,(jops,jpins,jrpins,jl,jr) in enumerate(self.gs[:i]):
                wire=base.N+j+1
                self.add(-iops[2],-il[ipins.index(wire)],-jops[2])
                right_gate=ir[irpins.index(wire)]
                for a in range(wire):
                    left_a=il[ipins.index(a)]
                    self.add(-right_gate,-left_a,-jl[jpins.index(a)])
                    self.add(-right_gate,-left_a,-jr[jrpins.index(a)])
        for a in (0,1):
            self.add(*(selector[pins.index(a)] for _,ls,rs,left,right in self.gs for selector,pins in ((left,ls),(right,rs))))

if __name__=='__main__':
    base.Encoding=Reduced
    base.main()
