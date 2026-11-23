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

-- The original existential conclusion, restricted to the verified finite range.
lemma orderSeven (c : ℕ) (hc : c < 399) : ∃ (q N : ℕ) (S : Fin N → Finset (Fin N)), 2 ≤ q ∧ N = q * q + q + 1 ∧ (∀ i : Fin N, (S i).card = q + 1) ∧ (∀ i j : Fin N, i ≠ j → (S i ∩ S j).card = 1) ∧ (∀ a b : Fin N, a ≠ b → ∃ i : Fin N, a ∈ S i ∧ b ∈ S i) ∧ ∃ w : ℕ, q * q < 8 * (w + 1) ∧ w + q < N ∧ ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin N → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : Fin N) (x : Fin N → Bool), ((Finset.univ.filter (fun p : Fin N => x p = false)).card = w ∨ (Finset.univ.filter (fun p : Fin N => x p = false)).card = w + 1) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out i⟩ (List.ofFn x) = decide (∃ v ∈ S i, x v = true)) ∧ c * gates.length < N * q := by
  refine ⟨7, 57, line, by decide, by decide, line_size, unique_intersection, join_points,
    6, by decide, by decide, gates, fun _ => 57, ?_, ?_, gate_budget c hc⟩
  · intro g hg
    simp [gates] at hg
    subst g
    exact ⟨Or.inl rfl, by decide⟩
  · intro i x hw
    exact band_eval i x (by omega)

end CoResearch.PlaneSeven

namespace CoResearch.Band

lemma distinguish {N k : ℕ} (s t : Finset (Fin N)) (p : Fin N)
    (hp : p ∈ t) (hn : p ∉ s) (hlo : s.card ≤ k) (hhi : k < N) :
    ∃ x : Fin N → Bool, (Finset.univ.filter (fun v => x v = false)).card = k ∧
      ¬ (∃ v ∈ s, x v = true) ∧ (∃ v ∈ t, x v = true) := by
  have hsub : s ⊆ Finset.univ.erase p := by
    intro v hv
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    exact hn hv
  have hc : k ≤ (Finset.univ.erase p).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨f, hsf, hfp, hcard⟩ := Finset.exists_subsuperset_card_eq hsub hlo hc
  let x : Fin N → Bool := fun v => decide (v ∉ f)
  have hf : Finset.univ.filter (fun v => x v = false) = f := by ext v; simp [x]
  refine ⟨x, hf ▸ hcard, ?_, p, hp, ?_⟩
  · rintro ⟨v, hv, ht⟩
    simpa [x, hsf hv] using ht
  · have hpn : p ∉ f := fun h => (Finset.mem_erase.mp (hfp h)).1 rfl
    simp [x, hpn]

end CoResearch.Band

#print axioms CoResearch.PlaneSeven.orderSeven
#print axioms CoResearch.Band.distinguish
