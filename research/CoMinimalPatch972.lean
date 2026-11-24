import Mathlib
import PEqualNP.Defs.DeMorganFormula

namespace CoMinimalPatch972
open PEqualNP.MetaComplexity

def positive {n : ℕ} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and f g | .or f g => positive f ∧ positive g

def containsEdge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v, G u v ∧ x u = true ∧ x v = true

def pair {n : ℕ} (u v : Fin n) (i : Fin n) : Bool := decide (i = u ∨ i = v)

theorem grows {n : ℕ} (f : DMFormula n) (hf : positive f)
    {x y : Fin n → Bool} (incl : ∀ i, x i = true → y i = true) :
    f.eval x = true → f.eval y = true := by
  induction f with
  | lit i b =>
    change b = true at hf
    subst b
    simpa [DMFormula.eval] using incl i
  | and f g ih jh =>
    simp only [DMFormula.eval, Bool.and_eq_true]
    exact fun h => ⟨ih hf.1 h.1, jh hf.2 h.2⟩
  | or f g ih jh =>
    simp only [DMFormula.eval, Bool.or_eq_true_iff]
    exact fun h => h.elim (fun a => Or.inl (ih hf.1 a)) (fun b => Or.inr (jh hf.2 b))

def lost {n : ℕ} (G : Fin n → Fin n → Prop) (f : DMFormula n) (u v : Fin n) : Prop :=
  G u v ∧ f.eval (pair u v) ≠ true

theorem repaired {n : ℕ} (G : Fin n → Fin n → Prop) (f g : DMFormula n)
    (hf : positive f) (hg : positive g)
    (small : ∀ x, f.eval x = true → containsEdge G x)
    (patch : ∀ x, g.eval x = true ↔ containsEdge (lost G f) x) :
    positive (.or f g) ∧ (DMFormula.or f g).leaves = f.leaves + g.leaves ∧
      ∀ x, (DMFormula.or f g).eval x = true ↔ containsEdge G x := by
  refine ⟨⟨hf,hg⟩,rfl,?_⟩
  intro x
  simp only [DMFormula.eval, Bool.or_eq_true_iff]
  constructor
  · rintro (yes|yes)
    · exact small x yes
    · obtain ⟨u,v,uv,hu,hv⟩ := (patch x).mp yes
      exact ⟨u,v,uv.1,hu,hv⟩
  · rintro ⟨u,v,uv,hu,hv⟩
    by_cases seen : f.eval (pair u v) = true
    · apply Or.inl
      apply grows f hf _ seen
      intro i h
      have h' : i = u ∨ i = v := of_decide_eq_true h
      rcases h' with rfl|rfl
      · exact hu
      · exact hv
    · exact Or.inr ((patch x).mpr ⟨u,v,⟨uv,seen⟩,hu,hv⟩)

theorem leaf_cost {n k : ℕ} (G : Fin n → Fin n → Prop) (f g : DMFormula n)
    (hf : positive f) (hg : positive g)
    (small : ∀ x, f.eval x = true → containsEdge G x)
    (patch : ∀ x, g.eval x = true ↔ containsEdge (lost G f) x)
    (bound : ∀ z : DMFormula n, positive z →
      (∀ x, z.eval x = true ↔ containsEdge G x) → k ≤ z.leaves) :
    k ≤ f.leaves + g.leaves := by
  obtain ⟨hpos, hs, hfun⟩ := repaired G f g hf hg small patch
  calc
    k ≤ (DMFormula.or f g).leaves := bound (.or f g) hpos hfun
    _ = _ := hs
end CoMinimalPatch972
