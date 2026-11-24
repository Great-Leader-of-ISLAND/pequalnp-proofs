import PEqualNP.CoNine3024Data

namespace CoNine3024
def guardSearch (keep : Nat → State → Bool) (g : Geometry) : Nat → State → Bool
  | 0,s => live g s
  | k+1,s => live g s || (keep (k+1) s && safe s && (children g k s).any (guardSearch keep g k))

inductive GuardPath (keep : Nat → State → Bool) (g : Geometry) : Nat → State → Prop
  | stop {k s} (endOK : live g s=true) : GuardPath keep g k s
  | gate {k s t} (extra : keep (k+1) s=true) (paid : safe s=true) (next : t∈children g k s)
      (tail : GuardPath keep g k t) : GuardPath keep g (k+1) s

theorem guard_complete {keep g k s} (p : GuardPath keep g k s) : guardSearch keep g k s=true := by
  induction p with
  | @stop k s eq => cases k <;> simp [guardSearch,eq]
  | gate extra paid next tail ih =>
    simp only [guardSearch,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inr ⟨⟨extra,paid⟩,List.any_eq_true.mpr ⟨_,next,ih⟩⟩
end CoNine3024
