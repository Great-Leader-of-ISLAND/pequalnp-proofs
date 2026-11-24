import Mathlib

namespace CoPatterns1710

def Below {k : ℕ} (a b : Fin k → Bool) : Prop :=
  ∀ i, a i = true → b i = true

def PrefixMonotone {k : ℕ} (block : Fin k → (Fin k → Bool) → Bool) : Prop :=
  ∀ j a b, (∀ i, i.val < j.val → a i = true → b i = true) →
    block j a = true → block j b = true

theorem lower_pattern {k : ℕ} (block : Fin k → (Fin k → Bool) → Bool)
    (mono : PrefixMonotone block) (a actual : Fin k → Bool)
    (fixed : ∀ j, actual j = block j actual)
    (chosen : ∀ j, a j = true → block j a = true) : Below a actual := by
  have h (m : ℕ) : ∀ j : Fin k, j.val = m → a j = true → actual j = true := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro j eq on
      apply (fixed j).trans
      apply mono j a actual _ (chosen j on)
      intro i lt ai
      exact ih i.val (lt.trans_eq eq) i rfl ai
  intro i
  exact h i.val i rfl

theorem upper_pattern {k : ℕ} (block : Fin k → (Fin k → Bool) → Bool)
    (mono : PrefixMonotone block) (a actual : Fin k → Bool)
    (fixed : ∀ j, actual j = block j actual)
    (off : ∀ j, a j = false → block j a = false) : Below actual a := by
  have h (m : ℕ) : ∀ j : Fin k, j.val = m → actual j = true → a j = true := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro j eq on
      cases aj : a j with
      | true => rfl
      | false =>
        have value := (fixed j).symm.trans on
        have promoted : block j a = true := by
          apply mono j actual a _ value
          intro i lt z
          exact ih i.val (lt.trans_eq eq) i rfl z
        exact False.elim (Bool.false_ne_true ((off j aj).symm.trans promoted))
  intro i
  exact h i.val i rfl

theorem sandwich {k : ℕ} (block : Fin k → (Fin k → Bool) → Bool)
    (A : (Fin k → Bool) → Bool) (mb : PrefixMonotone block)
    (ma : ∀ a b, Below a b → A a = true → A b = true) (a z : Fin k → Bool)
    (hz : ∀ j, z j = block j z) :
    ((A a = true ∧ ∀ j, a j = true → block j a = true) → A z = true) ∧
    (A z = true → A a = true ∨ ∃ j, a j = false ∧ block j a = true) := by
  constructor
  · rintro ⟨h,cert⟩
    exact ma a z (lower_pattern block mb a z hz cert) h
  · intro h
    by_cases hit : ∃ j, a j = false ∧ block j a = true
    · exact Or.inr hit
    · apply Or.inl
      apply ma z a _ h
      apply upper_pattern block mb a z hz
      intro j aj
      cases e : block j a with
      | false => rfl
      | true => exact False.elim (hit ⟨j,aj,e⟩)
end CoPatterns1710
