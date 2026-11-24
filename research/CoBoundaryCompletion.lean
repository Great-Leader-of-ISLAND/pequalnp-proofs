import Mathlib

namespace PEqualNP.Research.BoundaryCompletion

variable {α : Type*} [Fintype α] [DecidableEq α]

def Hits (edges : Finset (α × α)) (s : Finset α) : Prop :=
  ∃ e ∈ edges, e.1 ∈ s ∧ e.2 ∈ s

theorem extendNegative (F : Finset α → Prop) (s : Finset α) (hs : ¬ F s) :
    ∃ t, s ⊆ t ∧ ¬ F t ∧ ∀ a, a ∉ t → F (insert a t) := by
  classical
  suffices aux : ∀ k (r : Finset α), Fintype.card α - r.card = k → ¬ F r →
      ∃ t, r ⊆ t ∧ ¬ F t ∧ ∀ a, a ∉ t → F (insert a t) from aux _ s rfl hs
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro r hr hn
    by_cases further : ∃ a, a ∉ r ∧ ¬ F (insert a r)
    · obtain ⟨a,ha,hfa⟩ := further
      have hc : (insert a r).card = r.card + 1 := Finset.card_insert_of_notMem ha
      have hb : (insert a r).card ≤ Fintype.card α := Finset.card_le_univ _
      obtain ⟨t,hrt,hft,hmt⟩ :=
        ih (Fintype.card α - (insert a r).card) (by omega) (insert a r) rfl hfa
      exact ⟨t, fun x hx => hrt (Finset.mem_insert_of_mem hx), hft, hmt⟩
    · refine ⟨r, fun _ hx => hx, hn, ?_⟩
      intro a ha
      by_contra hfa
      exact further ⟨a, ha, hfa⟩

-- Pointwise notation records exactly which rows of a monotone realization are free.
theorem boundsFromBoundary (E : Finset (α × α)) (e₀ : α × α)
    (f : Finset α → Prop) (hmono : ∀ s t, s ⊆ t → f s → f t)
    (hp : ∀ e ∈ E, e ≠ e₀ → f {e.1,e.2})
    (hn : ∀ t, ¬ Hits E t → (∀ a, a ∉ t → Hits E (insert a t)) → ¬ f t) :
    ∀ s, (Hits (E.erase e₀) s → f s) ∧ (f s → Hits E s) := by
  classical
  intro s
  constructor
  · rintro ⟨e, he, ha, hb⟩
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp he
    apply hmono {e.1,e.2} s _ (hp e hm hne)
    intro a h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact ha
    · exact hb
  · intro hf
    by_contra hs
    obtain ⟨t,hst,hneg,hmax⟩ := extendNegative (Hits E) s hs
    exact hn t hneg hmax (hmono s t hst hf)

-- Wiring a single missing conjunction back by OR restores the full edge function.
theorem restoreEdge (E : Finset (α × α)) (e₀ : α × α) (he₀ : e₀ ∈ E)
    (f : Finset α → Prop)
    (bounds : ∀ s, (Hits (E.erase e₀) s → f s) ∧ (f s → Hits E s)) (s : Finset α) :
    (f s ∨ (e₀.1 ∈ s ∧ e₀.2 ∈ s)) ↔ Hits E s := by
  constructor
  · rintro (h | ⟨a,b⟩)
    · exact (bounds s).2 h
    · exact ⟨e₀,he₀,a,b⟩
  · rintro ⟨e,h,a,b⟩
    by_cases same : e = e₀
    · subst e
      exact Or.inr ⟨a,b⟩
    · exact Or.inl ((bounds s).1 ⟨e, Finset.mem_erase.mpr ⟨same,h⟩, a,b⟩)

end PEqualNP.Research.BoundaryCompletion
