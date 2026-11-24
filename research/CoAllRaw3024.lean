import PEqualNP.CoConeOrder3024
import PEqualNP.CoPaid3143

namespace CoAllRaw3024
open CoThetaNine CoConeOrder3024 CoAO3143Restriction

def seed : Wire Input := fun r => vtx 0 r || vtx 2 r

def inverse (p : Fin 11) : Wire Input :=
  if h : p.val<9 then fun r => !(vtx ⟨p.val,h⟩ r)
  else if p.val=9 then fun r => !(seed r) else con true

def label (p : Fin 11) (j : Fin 13) : Wire Input :=
  if h : j.val<9 then vtx ⟨j.val,h⟩
  else if j.val=9 then seed else if j.val=10 then inverse p else con (decide (j.val=12))

def lowRow (i : Fin 9) : Input := row (![20,1,9,4,1,1,2,4,8] i)
def highRow (i : Fin 9) : Input := row ((lowRow i).val ||| (1 <<< i.val))

/-- Every raw input must be used, even with both the free OR and a free negative pin.
    The two explicit assignments for each input keep OR(0,2) unchanged. -/
theorem all_raw (p : Fin 11) {k S} (run : Cone ans k S)
    (initial : ∀ w∈S, ∃ j, w=label p j) (i : Fin 9) : vtx i ∈ S := by
  classical
  have marks : ∀ i : Fin 9, ans (highRow i)=true ∧ ans (lowRow i)=false := by decide +kernel
  have stable : ∀ (p : Fin 11) (i : Fin 9) (j : Fin 13), j.val≠i.val →
    label p j (highRow i)=true → label p j (lowRow i)=true := by decide +kernel
  obtain ⟨one,zero⟩ := marks i
  by_contra absent
  have bad := ordered run (highRow i) (lowRow i) (by
    intro w hw on
    obtain ⟨j,rfl⟩ := initial w hw
    apply stable p i j _ on
    intro eq
    have bound : j.val<9 := by rw [eq]; exact i.isLt
    have same : label p j=vtx i := by
      unfold label
      rw [dif_pos bound]
      exact congrArg vtx (Fin.ext eq)
    exact absent (same ▸ hw)) one
  exact Bool.false_ne_true (zero.symm.trans bad)

#print axioms CoAllRaw3024.all_raw
end CoAllRaw3024
