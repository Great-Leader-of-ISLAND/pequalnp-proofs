import PEqualNP.CoAreas4055

namespace CoQueries4055

open CoAreas4055 CoZone4055
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The actual point queries and the all-lines-negative query imply the entire
linear-network cost, with H the edges that hit every singleton factor. -/
theorem queried_or_price (N H : I → Finset I)
    (hN : ∀ p q, p ≠ q → (N p ∩ N q).card ≤ 1) (P : Finset I)
    (pos : ∀ p∈P, 0 < (H p).card)
    (zs : List (Wire I)) (A : Finset (Wire I)) (hg : Good fuse A zs)
    (base : ∀ i w, w ∈ A → (view N i w).card ≤ 1)
    (pointQuery : ∀ p ∈ P, ∃ w ∈ A ∪ zs.toFinset,
      p ∉ w.1 ∧ w.2 ⊆ N p ∧ ∀ l ∈ H p, p ∈ w.1 ∨ l ∈ w.2)
    (allLines : ∃ w ∈ A ∪ zs.toFinset, w.2 = ∅ ∧ P ⊆ w.1) :
    (∑ p ∈ P, (H p).card) - 1 ≤ zs.length := by
  classical
  let J : Finset (Option I) := insert none (P.image some)
  let d : Option I → Nat := fun k => k.elim P.card (fun p => (H p).card)
  have req (i : Option I) (hi : i ∈ J) :
      ∃ w ∈ A ∪ zs.toFinset, d i ≤ (view N i w).card := by
    cases i with
    | none =>
      obtain ⟨w, hw, empty, supports⟩ := allLines
      exact ⟨w, hw, by simpa [d,view,empty] using Finset.card_le_card supports⟩
    | some p =>
      have hp : p ∈ P := by simpa [J] using hi
      obtain ⟨w, hw, misses, allowed, hits⟩ := pointQuery p hp
      have sub : H p ⊆ w.2 := fun l hl => (hits l hl).resolve_left misses
      exact ⟨w, hw, by simpa [d,view,allowed] using Finset.card_le_card sub⟩
  have cost := neighborhood_prices N hN zs A hg base J d req
  have ne : (none : Option I) ∉ P.image some := by simp
  change (∑ i ∈ insert none (P.image some), (d i - 1)) ≤ zs.length at cost
  rw [Finset.sum_insert ne,Finset.sum_image (fun _ _ _ _ e => Option.some.inj e)] at cost
  have bound : P.card - 1 + (∑ p ∈ P, ((H p).card-1)) ≤ zs.length := by
    simpa [d] using cost
  have total : (∑ p ∈ P, (H p).card) = (∑ p ∈ P, ((H p).card-1)) + P.card := by
    calc
      _ = ∑ p ∈ P, ((H p).card - 1 + 1) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hh := pos p hp
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  omega

end CoQueries4055
