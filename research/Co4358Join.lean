import PEqualNP.Co4358Original
import PEqualNP.Co4358LooseLift
import PEqualNP.Co4358Price
import PEqualNP.Co4358Root

namespace CoNum4358
open CoAO3143

private theorem reading (g : Gate) : g.reads2 = (g.isOr && (g.a==2 || g.b==2)) := by
  rcases g with ⟨d,a,b⟩
  by_cases ha : a=2
  · subst a
    simp [Gate.reads2,List.contains_cons]
  · have hA : 2≠a := Ne.symm ha
    by_cases hb : b=2
    · subst b
      simp [Gate.reads2,List.contains_cons,ha,hA]
    · have hB : 2≠b := Ne.symm hb
      simp [Gate.reads2,List.contains_cons,ha,hA,hb,hB]

private theorem cost_count (gs : List Gate) :
    (gs.map charge).sum=(gs.filter Gate.reads2).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases r : g.reads2 <;> simp [charge,←reading g,r,ih,Nat.add_comm]

private theorem raw_good : ∀ w ∈ rawKW, proper w := by
  intro w hw
  have all : rawKW.all (fun x => decide (x ≠ zero ∧ x ≠ one))=true := by decide +kernel
  change w≠zero ∧ w≠one
  exact of_decide_eq_true (List.all_eq_true.mp all w hw)

private theorem output_of_count (off out : Nat) (gs : List Gate)
    (positive : 0<gs.length) (count : liveCount off out gs=gs.length) :
    out=off+gs.length-1 := by
  cases gs with
  | nil => exact (Nat.not_lt_zero _ positive).elim
  | cons u us =>
    have last := last_output off out u us count
    simp only [List.length_cons]
    omega

private theorem raw_length : rawKW.length=7 := by decide

private theorem ordered_slots (ps : List Marked) :
    ∀ g ∈ (ps.map Marked.ordered).map Prod.fst, g.a≤g.b := by
  intro g hg
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hg
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hr
  exact ordered_le t

theorem exclusion (signed : CoThetaNine.SignedLower)
    (checked : ¬Walk 11 1 rawKW rawLoose (Finset.range 7))
    (C D : PhysCircuit) (a b : Nat) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (size : C.size=11) (agrees : PEqualNP.MetaComplexity.circuitFun 7 C = CoNum4358.target)
    (links : List.Forall₂ (Shape a b) C.gates D.gates)
    (promote : ∀ x : Fin 7 → Bool, (D.wires (true::List.ofFn x)).getD (C.output+1) false =
      (CoNum4358.target x || x 0 || x 3)) :
    (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length ≥ 2 := by
  classical
  by_contra! small
  obtain ⟨p⟩ := extract signed C D a b fan size agrees links
  let gs := (p.slots.map Marked.ordered).map Prod.fst
  have len : gs.length=11 := by simpa [gs] using p.len.trans size
  have rawlen := raw_length
  have low : Price rawKW gs.length := by rw [len]; exact KWPrice.lower signed
  have hit : lookupKW (bankKW rawKW gs) C.output=CoAO3143.target := Original.hit p (fun x => congrFun agrees x)
  have tidy := all_clean low hit
  have count := no_dead low hit
  have positive : 0<gs.length := len.symm ▸ (by decide : 0<11)
  have last := output_of_count rawKW.length C.output gs positive count
  have trail := to_trail _ _ _ tidy count last
  have bound : C.output<7+p.slots.length := by rw [p.len,size]; omega
  have raised := Transfer.three_mem p (rawlen ▸ trail) bound promote
  have sorted : ∀ g∈gs,g.a≤g.b := ordered_slots p.slots
  have budget : (gs.map charge).sum≤1 := by
    rw [cost_count]
    change (((p.slots.map Marked.ordered).map Prod.fst).filter Gate.reads2).length≤1
    rw [ordered_count,←p.readers]
    omega
  obtain ⟨live,w⟩ := Routes.extract trail (by omega) rawKW rawLoose 1 rfl raw_good tidy sorted budget
    (by rw [←last]; exact hit) (by rw [←last]; exact raised)
  have cap : C.output<rawKW.length+gs.length := by omega
  have subset : need rawKW.length C.output gs ⊆ Finset.range 7 := by
    intro i hi
    apply Finset.mem_range.mpr
    exact rawlen ▸ need_bounded _ _ _ tidy cap i hi
  rw [len] at live w
  have all := Routes.all_inputs subset live
  exact checked (all ▸ w)

end CoNum4358
