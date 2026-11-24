import Mathlib

namespace PEqualNP.Research.CoEightReads

-- Each index specifies a true two-vertex row and a false maximal independent row.
private def root : Fin 8 → Fin 11 := ![3, 0, 4, 6, 2, 9, 1, 5]
private def mate : Fin 8 → Fin 11 := ![6, 10, 1, 3, 5, 0, 4, 2]
private def neg : Fin 8 → Finset (Fin 11) :=
  ![{1,2,6,9}, {1,3,5,10}, {0,1,3,5}, {0,3,4,5},
    {0,4,5,6}, {0,2,4,6}, {2,4,6,9}, {1,2,3,9}]

private theorem mate_mem : ∀ i, mate i ∈ neg i := by decide
private theorem incompatible : ∀ i j, i ≠ j → root i ∈ neg j ∨ root j ∈ neg i := by decide

/-- A monotone suffix with a distinguished read that separates none of eight
pairs needs at least eight further reads, whenever these reads are linear on
the positive test edges and dominate their active singleton values on false rows. -/
theorem eight_reads {m : ℕ}
    (positive negative : Fin 8 → Option (Fin m) → Prop)
    (active : Fin m → Fin 11 → Prop) (finish : (Option (Fin m) → Prop) → Prop)
    (mono : ∀ a b, (∀ w, a w → b w) → finish a → finish b)
    (yes : ∀ i, finish (positive i)) (no : ∀ i, ¬ finish (negative i))
    (distinguished : ∀ i, positive i none → negative i none)
    (edge : ∀ i w, positive i (some w) → active w (root i) ∨ active w (mate i))
    (indep : ∀ i w v, v ∈ neg i → active w v → negative i (some w)) :
    8 ≤ m := by
  classical
  have sep (i : Fin 8) : ∃ w : Fin m, positive i (some w) ∧ ¬ negative i (some w) := by
    by_contra h
    apply no i
    apply mono _ _ _ (yes i)
    intro w hw
    cases w with
    | none => exact distinguished i hw
    | some z =>
      by_contra hz
      exact h ⟨z, hw, hz⟩
  choose wire hpos hneg using sep
  have onRoot (i : Fin 8) : active (wire i) (root i) := by
    rcases edge i (wire i) (hpos i) with ha | hb
    · exact ha
    · exact (hneg i (indep i (wire i) (mate i) (mate_mem i) hb)).elim
  have inj : Function.Injective wire := by
    intro i j he
    by_contra ne
    rcases incompatible i j ne with hij | hji
    · have a : active (wire j) (root i) := he ▸ onRoot i
      exact hneg j (indep j (wire j) (root i) hij a)
    · have a : active (wire i) (root j) := he.symm ▸ onRoot j
      exact hneg i (indep i (wire i) (root j) hji a)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective wire inj

end PEqualNP.Research.CoEightReads
