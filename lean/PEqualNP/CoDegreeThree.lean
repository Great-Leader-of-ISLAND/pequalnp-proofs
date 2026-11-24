import Mathlib
import PEqualNP.MetaComplexity.Helpers.LocGraph

namespace PEqualNP.Research.DegreeThree

open PEqualNP.MetaComplexity.Loc
open PEqualNP.MetaComplexity.Helpers.Forest

private theorem tau_mono {n : ℕ} {G H : SimpleGraph (Fin n)} (h : H ≤ G) :
    tau H ≤ tau G := by
  obtain ⟨T, hc, he⟩ := tau_attained G
  rw [← he]
  exact tau_le H T (fun i j hij => hc i j (h hij))

-- Both vertex-cover changes are controlled by the same integer. The vertex
-- set stays fixed throughout, as in the library's gate-elimination induction.
theorem split_cover {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (N : Finset (Fin n)) (hn : ∀ w, w ∈ N ↔ G.Adj v w) :
    tau G = min (1 + tau (delV G {v})) (N.card + tau (delV G (insert v N))) := by
  classical
  apply Nat.le_antisymm
  · apply le_min
    · obtain ⟨T, ht, he⟩ := tau_attained (delV G {v})
      have hc : Cov G (insert v T) := by
        intro a b e
        by_cases ha : a = v
        · exact Or.inl (Finset.mem_insert.mpr (Or.inl ha))
        by_cases hb : b = v
        · exact Or.inr (Finset.mem_insert.mpr (Or.inl hb))
        have e' := (delV_adj G {v} a b).mpr ⟨e, by simpa using ha, by simpa using hb⟩
        rcases ht a b e' with h | h
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · exact Or.inr (Finset.mem_insert_of_mem h)
      have h1 := tau_le G _ hc
      have h2 := Finset.card_insert_le v T
      omega
    · obtain ⟨T, ht, he⟩ := tau_attained (delV G (insert v N))
      have hc : Cov G (N ∪ T) := by
        intro a b e
        by_cases ha : a ∈ N
        · exact Or.inl (Finset.mem_union_left _ ha)
        by_cases hb : b ∈ N
        · exact Or.inr (Finset.mem_union_left _ hb)
        have av : a ≠ v := fun h => hb ((hn b).mpr (h ▸ e))
        have bv : b ≠ v := fun h => ha ((hn a).mpr (h ▸ e.symm))
        have e' := (delV_adj G (insert v N) a b).mpr
          ⟨e, by simp [av, ha], by simp [bv, hb]⟩
        rcases ht a b e' with h | h
        · exact Or.inl (Finset.mem_union_right _ h)
        · exact Or.inr (Finset.mem_union_right _ h)
      have h1 := tau_le G _ hc
      have h2 := Finset.card_union_le N T
      omega
  · obtain ⟨T, ht, he⟩ := tau_attained G
    by_cases hv : v ∈ T
    · apply le_trans (min_le_left _ _)
      have hc : Cov (delV G {v}) (T.erase v) := by
        intro a b e
        obtain ⟨hab, ha, hb⟩ := (delV_adj G {v} a b).mp e
        rcases ht a b hab with h | h
        · exact Or.inl (Finset.mem_erase.mpr ⟨by simpa using ha, h⟩)
        · exact Or.inr (Finset.mem_erase.mpr ⟨by simpa using hb, h⟩)
      have h1 := tau_le _ _ hc
      have h2 := Finset.card_erase_add_one hv
      omega
    · apply le_trans (min_le_right _ _)
      have hN : N ⊆ T := by
        intro w hw
        exact (ht v w ((hn w).mp hw)).resolve_left hv
      have hc : Cov (delV G (insert v N)) (T \ N) := by
        intro a b e
        obtain ⟨hab, ha, hb⟩ := (delV_adj G (insert v N) a b).mp e
        rcases ht a b hab with h | h
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨h, fun hN => ha (Finset.mem_insert_of_mem hN)⟩)
        · exact Or.inr (Finset.mem_sdiff.mpr ⟨h, fun hN => hb (Finset.mem_insert_of_mem hN)⟩)
      have h1 := tau_le _ _ hc
      have h2 := Finset.card_sdiff_add_card_eq_card hN
      omega

theorem degree_three_price {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (N : Finset (Fin n)) (hn : ∀ w, w ∈ N ↔ G.Adj v w) (h3 : N.card = 3) :
    let small := tau (delV G (insert v N))
    let large := tau (delV G {v})
    let d := large - small
    d ≤ 3 ∧ tau G = small + min (1+d) 3 ∧ tau G - large = min 1 (3-d) := by
  dsimp only
  have hab : delV G (insert v N) ≤ delV G {v} := by
    intro a b e
    obtain ⟨h,ha,hb⟩ := (delV_adj G (insert v N) a b).mp e
    apply (delV_adj G {v} a b).mpr
    exact ⟨h, fun h => ha (Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h))),
      fun h => hb (Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h)))⟩
  have horder := tau_mono hab
  have horder2 := tau_mono (delV_le G {v})
  have h := split_cover G v N hn
  rw [h3] at h
  omega

end PEqualNP.Research.DegreeThree
