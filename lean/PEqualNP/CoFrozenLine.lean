import Mathlib

namespace CoResearch.OneNot

variable {V : Type*} [Fintype V] [DecidableEq V]

def Hits (s a : Finset V) : Prop := ∃ p ∈ s, p ∈ a

theorem frozen_line_tests (s : Finset V)
    (lo hi actual : Finset V → Prop)
    (lo_mono : ∀ {a b}, a ⊆ b → lo a → lo b)
    (hi_mono : ∀ {a b}, a ⊆ b → hi a → hi b)
    (below : ∀ a, lo a → actual a)
    (above : ∀ a, actual a → hi a)
    (correct : ∀ a, actual a ↔ Hits s a) :
    ((∀ a, hi a ↔ Hits s a) ↔ ¬ hi (Finset.univ \ s)) ∧
    ((∀ a, lo a ↔ Hits s a) ↔ ∀ p ∈ s, lo {p}) := by
  classical
  constructor
  · constructor
    · intro eq h
      obtain ⟨p, hs, hc⟩ := (eq _).mp h
      exact (Finset.mem_sdiff.mp hc).2 hs
    · intro h a
      constructor
      · intro ha
        by_contra hn
        apply h (hi_mono ?_ ha)
        intro p hp
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs => hn ⟨p, hs, hp⟩⟩
      · exact fun hit => above _ ((correct _).mpr hit)
  · constructor
    · intro eq p hp
      exact (eq _).mpr ⟨p, hp, Finset.mem_singleton_self _⟩
    · intro singles a
      constructor
      · exact fun h => (correct _).mp (below _ h)
      · rintro ⟨p, hs, hp⟩
        exact lo_mono (Finset.singleton_subset_iff.mpr hp) (singles p hs)

theorem switch_line_tests (s : Finset V) (before : Finset V → Prop)
    [DecidablePred before] (lo hi : Finset V → Prop)
    (lo_mono : ∀ {a b}, a ⊆ b → lo a → lo b)
    (hi_mono : ∀ {a b}, a ⊆ b → hi a → hi b)
    (ordered : ∀ a, lo a → hi a)
    (computed : ∀ a, (if before a then lo a else hi a) ↔ Hits s a) :
    (¬ before (Finset.univ \ s) → ∀ a, hi a ↔ Hits s a) ∧
    ((∀ p ∈ s, before {p}) → ∀ a, lo a ↔ Hits s a) := by
  classical
  let f := fun a => if before a then lo a else hi a
  have low (a) : lo a → f a := by
    by_cases h : before a
    · simpa [f,h] using (show lo a → lo a from id)
    · simpa [f,h] using ordered a
  have high (a) : f a → hi a := by
    by_cases h : before a
    · simpa [f,h] using ordered a
    · simpa [f,h] using (show hi a → hi a from id)
  obtain ⟨top, bot⟩ := frozen_line_tests s lo hi f lo_mono hi_mono low high computed
  constructor
  · intro h
    apply top.mpr
    intro ha
    have actual := (computed _).mp (by simpa [h] using ha)
    obtain ⟨p, hp, hc⟩ := actual
    exact (Finset.mem_sdiff.mp hc).2 hp
  · intro h
    apply bot.mpr
    intro p hp
    have actual := (computed {p}).mpr ⟨p, hp, Finset.mem_singleton_self _⟩
    simpa [h p hp] using actual

end CoResearch.OneNot

#print axioms CoResearch.OneNot.switch_line_tests
