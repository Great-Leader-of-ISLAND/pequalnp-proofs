import PEqualNP.CoNine3024Guard

namespace CoNine3024.Canon

def le (a b : Atom) := decide (a.full.toNat≤b.full.toNat)

def order (s : State) : State := ⟨s.wires.mergeSort le,s.spent⟩

theorem perm (s : State) : (order s).wires.Perm s.wires := by
  exact List.mergeSort_perm _ _

@[simp] theorem spent (s : State) : (order s).spent=s.spent := rfl

def run (keep : Nat → State → Bool) (g : Geometry) : Nat → State → Bool
  | 0,s => live g s
  | k+1,s => live g s || (keep (k+1) s && safe s &&
    (children g k s).any (fun t => run keep g k (order t)))

/-- Each successor canonically sorts its full truth words. The semantic circuit
only needs its complete live wire set and the corresponding charge vector. -/
inductive Path (keep : Nat → State → Bool) (g : Geometry) : Nat → State → Prop
  | stop {k s} (endOK : live g s=true) : Path keep g k s
  | gate {k s t} (ok : keep (k+1) s=true) (paid : safe s=true)
      (edge : t∈children g k s) (tail : Path keep g k (order t)) : Path keep g (k+1) s

theorem complete {keep g k s} (h : Path keep g k s) : run keep g k s=true := by
  induction h with
  | @stop k s yes => cases k <;> simp [run,yes]
  | gate ok paid step tail ih =>
    simp only [run,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inr ⟨⟨ok,paid⟩,List.any_eq_true.mpr ⟨_,step,ih⟩⟩

end CoNine3024.Canon
