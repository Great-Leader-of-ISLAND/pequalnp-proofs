import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LineDegTest

namespace CoResearch.Diagonal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def assignment {N : ℕ} (P L : Finset (Fin N)) : Fin (N+N) → Bool :=
  Fin.addCases (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))

def wire {N : ℕ} (C : Circuit) (k : ℕ) (P L : Finset (Fin N)) : Bool :=
  (C.wires (List.ofFn (assignment P L))).getD k false

lemma wire_mono {N : ℕ} (C : Circuit) (mono : Monotone2 C) (k : ℕ)
    {P P' L L' : Finset (Fin N)} (hp : P ⊆ P') (hl : L ⊆ L') :
    wire C k P L = true → wire C k P' L' = true := by
  have bit (i : Fin (N+N)) : assignment P L i = true → assignment P' L' i = true := by
    refine Fin.addCases (fun p => ?_) (fun l => ?_) i
    · simpa [assignment] using (show p ∈ P → p ∈ P' from fun h => hp h)
    · simpa [assignment] using (show l ∈ L → l ∈ L' from fun h => hl h)
  have ls : LineDegTest.Le (List.ofFn (assignment P L)) (List.ofFn (assignment P' L')) := by
    intro i hi
    by_cases h : i < N+N
    · simpa [List.getD, h] using bit ⟨i,h⟩ (by simpa [List.getD, h] using hi)
    · simp [List.getD, h] at hi
  have hh := LineDegTest.W_mono C.gates (fun g hg => (mono g hg).1) _ _ (by simp) ls
  exact hh k

lemma orient_rows {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (mono : Monotone2 C) (a b : ℕ)
    (sound : ∀ z : Fin (N+N) → Bool,
      (C.wires (List.ofFn z)).getD a false = true → (C.wires (List.ofFn z)).getD b false = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (P : Finset (Fin N)) :
    (∀ L : Finset (Fin N), wire C a P L = true → ∃ p ∈ P, ∃ l ∈ L, I p l) ∨
    (∀ L : Finset (Fin N), wire C b P L = true → ∃ p ∈ P, ∃ l ∈ L, I p l) := by
  classical
  let U : Finset (Fin N) := Finset.univ.filter (fun l => ¬∃ p ∈ P, I p l)
  have zero (ha : wire C a P U = true) (hb : wire C b P U = true) : False := by
    obtain ⟨p, l, hI, hx, hy⟩ := sound (assignment P U) ha hb
    have hp : p ∈ P := by simpa [assignment] using hx
    have hl : l ∈ U := by simpa [assignment] using hy
    exact (Finset.mem_filter.mp hl).2 ⟨p, hp, hI⟩
  have safe (k : ℕ) (h : wire C k P U ≠ true) (L : Finset (Fin N)) (hk : wire C k P L = true) :
      ∃ p ∈ P, ∃ l ∈ L, I p l := by
    by_contra hn
    have sub : L ⊆ U := by
      intro l hl
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rintro ⟨p, hp, hi⟩
      exact hn ⟨p, hp, l, hl, hi⟩
    exact h (wire_mono C mono k (Finset.Subset.rfl) sub hk)
  by_cases ha : wire C a P U = true
  · exact Or.inr (safe b (zero ha))
  · exact Or.inl (safe a ha)

end CoResearch.Diagonal

#print axioms CoResearch.Diagonal.orient_rows
