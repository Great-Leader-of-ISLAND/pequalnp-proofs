import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research.PetersenStars

abbrev V := Fin 9
abbrev E := V × V

def remaining : Finset E :=
  {(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)}

theorem card_remaining : remaining.card = 11 := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem cover_five : ∀ s : Finset V,
    (∀ e ∈ remaining, e.1 ∈ s ∨ e.2 ∈ s) → 5 ≤ s.card := by
  decide +kernel

/-- A fixed singleton term x₀ AND x₁ and k further OR-of-neighbor star terms.
The reduction counts one gate per leaf edge in each nonempty star and k OR
joins for its k+1 term outputs. Repeated edge coverage is allowed. -/
theorem live_first_singleton_star_cost {k : ℕ} (c : Fin k → V) (g : Fin k → Finset E)
    (cover : remaining ⊆ Finset.univ.biUnion g)
    (star : ∀ i e, e ∈ g i → e.1 = c i ∨ e.2 = c i) :
    17 ≤ 1 + (∑ i, (g i).card) + k := by
  let s := Finset.univ.image c
  have hv : ∀ e ∈ remaining, e.1 ∈ s ∨ e.2 ∈ s := by
    intro e he
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (cover he)
    have hc : c i ∈ s := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    rcases star i e hi with ha | hb
    · exact Or.inl (ha ▸ hc)
    · exact Or.inr (hb ▸ hc)
  have five := cover_five s hv
  have sk : s.card ≤ k := by
    exact (Finset.card_image_le).trans (by simp)
  have edgecount := (Finset.card_le_card cover).trans (Finset.card_biUnion_le)
  rw [card_remaining] at edgecount
  omega

end PEqualNP.Research.PetersenStars
