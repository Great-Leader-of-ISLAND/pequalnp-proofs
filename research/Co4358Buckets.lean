import PEqualNP.Co4358Search

namespace CoNum4358
open CoAO3143

def firstRoot (a b : Nat) (d : Bool) : Bool :=
  stepOne (explore 10) 1 rawKW rawLoose (List.range 7) ⟨d,a,b⟩

def rowRoot (a : Nat) : Bool :=
  (List.range 7).any fun b => options.any fun d => firstRoot a b d

theorem excluded_of_rows (rows : ∀ a : Fin 7, rowRoot a.val=false) :
    ¬ Walk 11 1 rawKW rawLoose (Finset.range 7) := by
  intro walk
  have h := explore_complete walk (List.range 7) (by decide +kernel)
  change (admissible 11 rawKW (List.range 7) && (List.range 7).any rowRoot)=true at h
  rw [Bool.and_eq_true] at h
  obtain ⟨a,am,v⟩ := List.any_eq_true.mp h.2
  exact Bool.false_ne_true ((rows ⟨a,List.mem_range.mp am⟩).symm.trans v)

end CoNum4358
