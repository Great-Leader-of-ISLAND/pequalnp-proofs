import PEqualNP.Co4358Reflection
import PEqualNP.Co4358OrbitData
import PEqualNP.Co4358ColorJumpTable
namespace CoNum4358.Tiny.Splice
open CoAO3143
open CoNum4358.WordRows
set_option maxRecDepth 65536

def orbitItem (check : Nat → Nat → Bool) (k i : Nat) :=
  let ref := (Orbits.tier (k+1)).val i
  if ref==0 then check k i else
    let j := ref-1
    let source := stored (k+1) i
    let target := stored (k+1) j
    decide (j<i) && source.1==target.1 && (source.2.map Reflection.wire).isPerm target.2

theorem orbit_complete {k : Nat} {check : Nat → Nat → Bool}
    (actual : ∀ i,check k i=true → ¬Trace (k+1) (stored (k+1) i).1 (stored (k+1) i).2.toFinset)
    (data : ∀i<(BicolorBase.tier (k+1)).total,orbitItem check k i=true) : Layer (k+1) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have checked := data i hi
    unfold orbitItem at checked
    dsimp only at checked
    split at checked
    · exact actual i checked
    · simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.isPerm_iff] at checked
      obtain ⟨⟨before,quota⟩,per⟩ := checked
      have no := ih _ before (by omega)
      intro h
      have reflected := Reflection.trace h
      have identical : ((stored (k+1) i).2.toFinset.image Reflection.wire)=
          (stored (k+1) ((Orbits.tier (k+1)).val i-1)).2.toFinset := by
        ext x
        have p := per.mem_iff (a:=x)
        simpa only [Finset.mem_image,List.mem_toFinset,List.mem_map] using p
      exact no (by rw [←quota,←identical]; exact reflected)

theorem orbit_layer {k : Nat} (prior : Layer k)
    (data : ∀i<(BicolorBase.tier (k+1)).total,orbitItem entry k i=true) : Layer (k+1) := by
  apply orbit_complete _ data
  intro i ok
  exact MaskFast.nodeWith_ok post sound (T:=bank (k+1) i k) prior ok

#print axioms orbit_layer
end CoNum4358.Tiny.Splice
