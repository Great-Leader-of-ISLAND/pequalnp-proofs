import Mathlib

namespace CoPortPrices4482

/-- A decoder may be arbitrary. Distinct outside cofactors nevertheless
    require distinct local observed words, since the outside can be fixed
    to exactly the same input on both rows. -/
theorem distinct_words {A B : Type*} {k : ℕ} (answer : A → B → Bool)
    (word : A → Fin k → Bool) (outside : B → B) (decode : (Fin k → Bool) → B → Bool)
    (agrees : ∀ a b, decode (word a) (outside b) = answer a b)
    {a c : A} {b : B} (switches : answer a b ≠ answer c b) : word a ≠ word c := by
  intro eq
  apply switches
  rw [← agrees a b,← agrees c b,eq]

theorem type_bound {A : Type*} {p k : ℕ} (represent : Fin p → A) (word : A → Fin k → Bool)
    (sep : ∀ u v, u ≠ v → word (represent u) ≠ word (represent v)) : p ≤ 2^k := by
  have inj : Function.Injective (fun i => word (represent i)) := by
    intro u v eq
    by_contra ne
    exact sep u v ne eq
  have bound := Fintype.card_le_of_injective _ inj
  simpa using bound

def ones {k : ℕ} (f : Fin k → Bool) := Finset.univ.filter (fun i => f i=true)

private theorem strict_weight {k : ℕ} {f g : Fin k → Bool}
    (grows : ∀ i, f i = true → g i = true) (changes : f ≠ g) :
    (ones f).card < (ones g).card := by
  have sub : ones f ⊆ ones g := by
    intro i h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,grows i (Finset.mem_filter.mp h).2⟩
  apply Finset.card_lt_card
  refine lt_of_le_of_ne sub ?_
  intro same
  apply changes
  funext i
  have iff : f i = true ↔ g i = true := by
    have h : i∈ones f ↔ i∈ones g := by rw [same]
    simpa only [ones,Finset.mem_filter,Finset.mem_univ,true_and] using h
  cases a : f i <;> cases b : g i <;> simp_all

/-- A chain of raw assignments on which the outside cofactor changes requires
    a strict increase of local Hamming weight at every step. -/
theorem chain_bound {A : Type*} {p k : ℕ} (chain : ℕ → A) (word : A → Fin k → Bool)
    (grows : ∀ j < p, ∀ i, word (chain j) i = true → word (chain (j+1)) i = true)
    (changes : ∀ j < p, word (chain j) ≠ word (chain (j+1))) : p ≤ k := by
  have height (j : ℕ) (hj : j ≤ p) : j ≤ (ones (word (chain j))).card := by
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have jlt : j<p := by omega
      have rise := strict_weight (grows j jlt) (changes j jlt)
      have old := ih (by omega)
      omega
  have total : (ones (word (chain p))).card ≤ k := by
    simpa using (Finset.card_le_card (Finset.subset_univ (ones (word (chain p)))))
  exact (height p (by omega)).trans total

#print axioms type_bound
#print axioms chain_bound
end CoPortPrices4482
