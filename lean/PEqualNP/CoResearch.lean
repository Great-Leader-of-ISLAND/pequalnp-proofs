import Mathlib
import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Outside.L_meta_529

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
namespace CoResearch.Band

open PEqualNP.CircuitLowerBounds

-- An arbitrary gate list adds exactly one wire per gate, preserving every input wire.
private def appendGate (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map (fun i => xs.getD i false))]

private lemma suffix (gs : List Gate) (xs : List Bool) :
    ∃ ys, gs.foldl appendGate xs = xs ++ ys ∧ ys.length = gs.length := by
  induction gs generalizing xs with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨ys, he, hl⟩ := ih (appendGate xs g)
    refine ⟨g.op.eval (g.inputs.map (fun i => xs.getD i false)) :: ys, ?_, by simp [hl]⟩
    simpa [appendGate, List.append_assoc] using he

lemma line_gate_count {N k : ℕ} (S : Fin N → Finset (Fin N))
    (sizes : ∀ i, 1 < (S i).card ∧ (S i).card ≤ k) (hk : k < N)
    (meet : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (gs : List Gate) (out : Fin N → ℕ)
    (correct : ∀ i (x : Fin N → Bool), (Finset.univ.filter (fun v => x v = false)).card = k →
      Circuit.eval ⟨gs, out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true)) :
    N ≤ gs.length := by
  classical
  have bounds (i : Fin N) : N ≤ out i ∧ out i < N + gs.length := by
    constructor
    · by_contra! h
      let p : Fin N := ⟨out i, h⟩
      obtain ⟨v, hv, hne⟩ := Finset.exists_mem_ne (sizes i).1 p
      obtain ⟨x, hw, hoff, hon⟩ := distinguish {p} (S i) v hv (by simpa using hne)
        (by have := sizes i; simp; omega) hk
      have hp : x p = false := by
        cases he : x p with
        | false => rfl
        | true => exact (hoff ⟨p, by simp, he⟩).elim
      obtain ⟨ys, he, _⟩ := suffix gs (List.ofFn x)
      have hf := correct i x hw
      change (gs.foldl appendGate (List.ofFn x)).getD (out i) false = _ at hf
      rw [he, List.getD, List.getElem?_append_left (by simpa using h), List.getElem?_ofFn] at hf
      have ht : x p = true := by simpa [h, hon, p] using hf
      exact Bool.false_ne_true (hp.symm.trans ht)
    · by_contra! h
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by have := sizes i; omega : 0 < (S i).card)
      obtain ⟨x, hw, _, hon⟩ := distinguish ∅ (S i) v hv (by simp) (by simp) hk
      obtain ⟨ys, he, hl⟩ := suffix gs (List.ofFn x)
      have hf := correct i x hw
      change (gs.foldl appendGate (List.ofFn x)).getD (out i) false = _ at hf
      rw [he, List.getD, List.getElem?_eq_none (by simpa [hl] using h)] at hf
      simp [hon] at hf
  have inj : Function.Injective out := by
    intro i j hij
    by_contra hne
    have uns : ¬ S j ⊆ S i := by
      intro hs
      have eq : S i ∩ S j = S j := Finset.inter_eq_right.mpr hs
      have hu := meet i j hne
      rw [eq] at hu
      have := (sizes j).1
      omega
    obtain ⟨v, hvj, hvi⟩ := Finset.not_subset.mp uns
    obtain ⟨x, hw, hi, hj⟩ := distinguish (S i) (S j) v hvj hvi (sizes i).2 hk
    have a := correct i x hw
    have b := correct j x hw
    rw [hij] at a
    rw [a] at b
    simp [hi, hj] at b
  let gate : Fin N → Fin gs.length := fun i => ⟨out i - N, by have := bounds i; omega⟩
  have hg : Function.Injective gate := by
    intro a b h
    apply inj
    have he : out a - N = out b - N := congrArg Fin.val h
    have := bounds a
    have := (bounds b).1
    omega
  simpa using Fintype.card_le_of_injective gate hg

end CoResearch.Band

#print axioms CoResearch.Band.line_gate_count

namespace CoResearch.Band

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_529_aux

lemma or_support (n : ℕ) : ∀ gs : List Gate, (∀ g ∈ gs, g.op = .or) → ∀ j : ℕ,
    ∃ s : Finset (Fin n), ∀ x : Fin n → Bool, val gs x j = decide (∃ p ∈ s, x p = true) := by
  classical
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ j
    by_cases hj : j < n
    · refine ⟨{⟨j, hj⟩}, ?_⟩
      intro x
      simp [val_nil, hj]
    · refine ⟨∅, ?_⟩
      intro x
      simp [val_nil, hj]
  | append_singleton gs g ih =>
    intro hg j
    obtain ⟨base, last⟩ : (∀ a ∈ gs, a.op = .or) ∧ g.op = .or :=
      ⟨fun a ha => hg a (by simp [ha]), hg g (by simp)⟩
    choose sets hs using ih base
    by_cases hj : j = n + gs.length
    · refine ⟨g.inputs.toFinset.biUnion sets, ?_⟩
      intro x
      rw [val_snoc, if_pos hj, last]
      apply Bool.eq_iff_iff.mpr
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, decide_eq_true_eq,
        Finset.mem_biUnion, List.mem_toFinset]
      constructor
      · rintro ⟨b, ⟨a, ha, rfl⟩, hb⟩
        rw [hs, decide_eq_true_eq] at hb
        obtain ⟨p, hp, hx⟩ := hb
        exact ⟨p, ⟨a, ha, hp⟩, hx⟩
      · rintro ⟨p, ⟨a, ha, hp⟩, hx⟩
        exact ⟨val gs x a, ⟨a, ha, rfl⟩, by rw [hs, decide_eq_true_eq]; exact ⟨p, hp, hx⟩⟩
    · exact ⟨sets j, fun x => by rw [val_snoc, if_neg hj, hs]⟩

lemma recover_support {n k : ℕ} {a b : Finset (Fin n)} (ha : a.card ≤ k) (hk : k < n)
    (on_layer : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = false)).card = k →
      decide (∃ v ∈ a, x v = true) = decide (∃ v ∈ b, x v = true)) : a = b := by
  have sub {s t : Finset (Fin n)} (hs : s.card ≤ k)
      (eq : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = false)).card = k →
        decide (∃ v ∈ s, x v = true) = decide (∃ v ∈ t, x v = true)) : t ⊆ s := by
    intro p hp
    by_contra hn
    obtain ⟨x, hw, h0, h1⟩ := distinguish s t p hp hn hs hk
    simpa [h0, h1] using eq x hw
  have hba := sub ha on_layer
  exact Finset.Subset.antisymm (sub ((Finset.card_le_card hba).trans ha) (fun x h => (on_layer x h).symm)) hba

lemma or_band_cost {n m k : ℕ} (S : Fin m → Finset (Fin n)) (hk : k < n)
    (hs : ∀ i, (S i).card ≤ k) (hm : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ) (hg : ∀ g ∈ gs, g.op = .or ∧ g.inputs.length ≤ 2)
    (correct : ∀ i (x : Fin n → Bool), (Finset.univ.filter (fun p => x p = false)).card = k →
      Circuit.eval ⟨gs, out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true)) :
    ∑ i, ((S i).card - 1) ≤ gs.length := by
  apply PEqualNP.Outside.L_meta_529 n m S hm gs out
  · exact fun g h => ⟨Or.inr (hg g h).1, (hg g h).2⟩
  · intro i x
    obtain ⟨b, hb⟩ := or_support n gs (fun g h => (hg g h).1) (out i)
    have he : S i = b := recover_support (hs i) hk (fun y hy => (correct i y hy).symm.trans (hb y))
    rw [he]
    exact hb x

end CoResearch.Band

#print axioms CoResearch.Band.or_band_cost

namespace CoResearch.Band

open PEqualNP.CircuitLowerBounds

lemma positive_cost {N k : ℕ} (s : Finset (Fin N)) (hs : 1 < s.card) (hk₀ : 0 < k)
    (hk : k < N) (gs : List Gate) (out : ℕ)
    (correct : ∀ x : Fin N → Bool, (Finset.univ.filter (fun v => x v = false)).card = k →
      Circuit.eval ⟨gs, out⟩ (List.ofFn x) = decide (∃ v ∈ s, x v = true)) :
    0 < gs.length := by
  cases gs with
  | cons g gs => simp
  | nil =>
    exfalso
    by_cases hout : out < N
    · let p : Fin N := ⟨out, hout⟩
      obtain ⟨v, hv, hne⟩ := Finset.exists_mem_ne hs p
      obtain ⟨x, hw, hoff, hon⟩ := distinguish {p} s v hv (by simpa using hne) (by simp only [Finset.card_singleton]; omega) hk
      have ht : x p = true := by simpa [Circuit.eval, Circuit.wires, List.getD, hout, p, hon] using correct x hw
      exact hoff ⟨p, by simp, ht⟩
    · obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
      obtain ⟨x, hw, _, hon⟩ := distinguish ∅ s v hv (by simp) (by simp) hk
      simpa [Circuit.eval, Circuit.wires, List.getD, hout, hon] using correct x hw

lemma large_witness {c q N w : ℕ} (hc : 399 ≤ c) (hq : 2 ≤ q) (hn : N = q*q+q+1)
    (S : Fin N → Finset (Fin N)) (size : ∀ i, (S i).card = q+1)
    (meet : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (band : q*q < 8*(w+1)) (room : w+q < N) (gs : List Gate) (out : Fin N → ℕ)
    (correct : ∀ i (x : Fin N → Bool), (Finset.univ.filter (fun v => x v = false)).card = w+1 →
      Circuit.eval ⟨gs, out i⟩ (List.ofFn x) = decide (∃ v ∈ S i, x v = true))
    (budget : c * gs.length < N*q) : c < q := by
  have hk : w+1 < N := by omega
  have he : 0 < N := by omega
  let i : Fin N := ⟨0, he⟩
  have pos := positive_cost (S i) (by rw [size]; omega) (by omega : 0 < w+1) hk gs (out i) (correct i)
  have qbig : 8 ≤ q := by
    by_contra! h
    have h7 : q ≤ 7 := by omega
    have h49 := Nat.mul_le_mul h7 h7
    have h57 : N ≤ 57 := by omega
    have maxCost := Nat.mul_le_mul h57 h7
    have ge := Nat.mul_le_mul_left c (show 1 ≤ gs.length by omega)
    simp only [Nat.mul_one] at ge
    omega
  have minband : q ≤ w := by
    have sq := Nat.mul_le_mul_right q qbig
    omega
  have cost := line_gate_count S (fun j => by rw [size]; omega) hk meet gs out correct
  by_contra! h
  have le := Nat.mul_le_mul cost h
  exact (not_lt_of_ge (by simpa only [Nat.mul_comm gs.length c] using le)) budget

end CoResearch.Band

#print axioms CoResearch.Band.large_witness
