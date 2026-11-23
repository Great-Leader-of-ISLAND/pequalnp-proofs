import Mathlib
import PEqualNP.Defs.CircuitLowerBounds

namespace CoResearch.PlaneSeven

open PEqualNP.CircuitLowerBounds

def block : Finset (Fin 57) := {0, 1, 3, 13, 32, 36, 43, 52}

def line (i : Fin 57) : Finset (Fin 57) := block.image (fun t => t + i)

def overlap (d : Fin 57) : Finset (Fin 57) := block.filter (fun t => t + d ∈ block)

lemma differences : ∀ d : Fin 57, d ≠ 0 → (overlap d).card = 1 := by decide

lemma on_line (p i : Fin 57) : p ∈ line i ↔ p - i ∈ block := by
  constructor
  · intro hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    simpa using ht
  · intro hp
    exact Finset.mem_image.mpr ⟨p - i, hp, sub_add_cancel p i⟩

lemma line_size (i : Fin 57) : (line i).card = 8 := by
  unfold line
  rw [Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)]
  decide

lemma unique_intersection (i j : Fin 57) (hne : i ≠ j) : (line i ∩ line j).card = 1 := by
  have eq : line i ∩ line j = (overlap (i-j)).image (fun t => t + i) := by
    ext p
    have diff : p - i + (i - j) = p - j := by abel
    constructor
    · intro hp
      obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hp
      refine Finset.mem_image.mpr ⟨p-i, Finset.mem_filter.mpr ⟨(on_line p i).mp hi, ?_⟩, sub_add_cancel p i⟩
      rw [diff]
      exact (on_line p j).mp hj
    · intro hp
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hb, hd⟩ := Finset.mem_filter.mp ht
      refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨t, hb, rfl⟩, (on_line _ _).mpr ?_⟩
      have e : t + i - j = t + (i-j) := by abel
      simpa only [e] using hd
  rw [eq, Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)]
  exact differences _ (sub_ne_zero.mpr hne)

lemma join_points (a b : Fin 57) (hne : a ≠ b) : ∃ i, a ∈ line i ∧ b ∈ line i := by
  have hcard := differences (b-a) (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (by omega : 0 < (overlap (b-a)).card)
  obtain ⟨hb, hd⟩ := Finset.mem_filter.mp ht
  refine ⟨a-t, (on_line _ _).mpr ?_, (on_line _ _).mpr ?_⟩
  · have e : a - (a-t) = t := by abel
    rwa [e]
  · have e : b - (a-t) = t + (b-a) := by abel
    rwa [e]

def gates : List Gate := [⟨.and, []⟩]

lemma band_eval (i : Fin 57) (x : Fin 57 → Bool)
    (h : (Finset.univ.filter (fun p => x p = false)).card ≤ 7) :
    Circuit.eval ⟨gates, 57⟩ (List.ofFn x) = decide (∃ p ∈ line i, x p = true) := by
  have hit : ∃ p ∈ line i, x p = true := by
    by_contra hn
    have sub : line i ⊆ Finset.univ.filter (fun p => x p = false) := by
      intro p hp
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ p, ?_⟩
      cases hx : x p with
      | false => rfl
      | true => exact (hn ⟨p, hp, hx⟩).elim
    have hs := Finset.card_le_card sub
    rw [line_size] at hs
    omega
  simp only [hit, decide_true]
  change (List.ofFn x ++ [true]).getD 57 false = true
  rw [List.getD, List.getElem?_append_right (by simp)]
  simp

lemma gate_budget (c : ℕ) (hc : c < 399) : c * gates.length < 57 * 7 := by
  simpa [gates] using hc

end CoResearch.PlaneSeven
