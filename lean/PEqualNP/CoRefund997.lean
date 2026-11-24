import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research.Incidence997

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)


-- The evaluation helpers above follow the checked project lemma L-meta-988.
variable {n m : ℕ}
variable (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
variable (sep : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
variable (outputs : ∀ (i : Fin m) (x : Fin n → Bool),
  (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true))

include outputs in
private lemma singleton_output (i : Fin m) (p : Fin n) :
    value C (fun v => decide (v = p)) (o i) = true ↔ p ∈ S i := by
  rw [value, outputs]
  simp

include outputs in
private lemma nontrivial_bounds (i : Fin m) (h : 2 ≤ (S i).card) :
    n ≤ o i ∧ o i < n + C.gates.length := by
  constructor
  · by_contra! hx
    let q : Fin n := ⟨o i, hx⟩
    have sub : S i ⊆ {q} := by
      intro p hp
      have hv := (singleton_output S C o outputs i p).mpr hp
      change value C (fun v => decide (v = p)) q = true at hv
      rw [input_value] at hv
      have eqp : q = p := of_decide_eq_true hv
      simp [eqp]
    have hc := Finset.card_le_card sub
    simp at hc
    omega
  · by_contra! hx
    have hp : (S i).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hmem⟩ := hp
    have hv := (singleton_output S C o outputs i p).mpr hmem
    rw [missing_value _ _ _ hx] at hv
    contradiction

include sep outputs in
private lemma distinct_outputs {i j : Fin m} (hi : 2 ≤ (S i).card)
    (ho : o i = o j) : i = j := by
  by_contra hij
  have eqs : S i = S j := by
    ext p
    rw [← singleton_output S C o outputs i p, ho, singleton_output S C o outputs j p]
  have bound := sep i j hij
  rw [← eqs, Finset.inter_self] at bound
  omega

private noncomputable def refund (S : Fin m → Finset (Fin n)) (C : Circuit) (y : Finset (Fin n)) : Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun g : Fin C.gates.length =>
    (∃ i : Fin m, ∀ p : Fin n, value C (fun v => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
    (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
      (value C (fun v => decide (v ∈ y ∨ v = p)) (n + g) = true ↔ p ∈ S i))

include outputs in
private lemma own_refund (y : Finset (Fin n)) (i : Fin m) (hd : Disjoint (S i) y)
    (g : Fin C.gates.length) (hg : n + (g : ℕ) = o i) : g ∈ refund S C y := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ⟨i, ?_⟩, i, hd, ?_⟩
  · intro p
    rw [hg]
    exact singleton_output S C o outputs i p
  · intro p _
    rw [hg, value, outputs]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨q, hq, hy | rfl⟩
      · exact False.elim (Finset.disjoint_left.mp hd hq hy)
      · exact hq
    · intro hp
      exact ⟨p, hp, Or.inr rfl⟩

private def rowWeight (y : Finset (Fin n)) (i : Fin m) :=
  if Disjoint (S i) y then (S i).card else min y.card (S i).card

-- The precise output charges used by both measurement windows.
include sep outputs in
theorem small_row_bound (y : Finset (Fin n))
    (small : ∀ i, if Disjoint (S i) y then (S i).card ≤ 3 else min y.card (S i).card ≤ 2) :
    (∑ i : Fin m, rowWeight S y i) ≤ C.gates.length + (refund S C y).card + m := by
  classical
  let A := Finset.univ.filter fun i : Fin m => 2 ≤ rowWeight S y i
  let B := Finset.univ.filter fun i : Fin m => 3 ≤ rowWeight S y i
  have le_card (i : Fin m) : rowWeight S y i ≤ (S i).card := by
    unfold rowWeight
    split <;> omega
  have bound (i : Fin m) : rowWeight S y i ≤ 3 := by
    have hs := small i
    unfold rowWeight
    split <;> rename_i h <;> simp [h] at hs <;> omega
  have typeA (i : ↥A) : 2 ≤ (S i.val).card :=
    le_trans (Finset.mem_filter.mp i.property).2 (le_card _)
  have typeB (i : ↥B) : 2 ≤ (S i.val).card := by
    have h := (Finset.mem_filter.mp i.property).2
    have hh := le_card i.val
    omega
  let wire (i : Fin m) (h : 2 ≤ (S i).card) : Fin C.gates.length :=
    ⟨o i - n, by have hb := nontrivial_bounds S C o outputs i h; omega⟩
  have spec (i : Fin m) (h : 2 ≤ (S i).card) : n + (wire i h : ℕ) = o i := by
    have hb := nontrivial_bounds S C o outputs i h
    dsimp [wire]
    omega
  have a_bound : A.card ≤ C.gates.length := by
    let f (i : ↥A) : Fin C.gates.length := wire i.val (typeA i)
    have inj : Function.Injective f := by
      intro i j hij
      change wire i.val (typeA i) = wire j.val (typeA j) at hij
      apply Subtype.ext
      apply distinct_outputs S C o sep outputs (typeA i)
      rw [← spec i.val (typeA i), ← spec j.val (typeA j), hij]
    simpa using Fintype.card_le_of_injective f inj
  have b_in (i : ↥B) : wire i.val (typeB i) ∈ refund S C y := by
    apply own_refund S C o outputs y i.val _ _ (spec _ _)
    by_contra hd
    have hb := (Finset.mem_filter.mp i.property).2
    have hs := small i.val
    simp [rowWeight, hd] at hb hs
    omega
  have b_bound : B.card ≤ (refund S C y).card := by
    let f (i : ↥B) : ↥(refund S C y) := ⟨wire i.val (typeB i), b_in i⟩
    have inj : Function.Injective f := by
      intro i j h
      have hw : wire i.val (typeB i) = wire j.val (typeB j) := congrArg Subtype.val h
      apply Subtype.ext
      apply distinct_outputs S C o sep outputs (typeB i)
      rw [← spec i.val (typeB i), ← spec j.val (typeB j), hw]
    simpa using Fintype.card_le_of_injective f inj
  have pw (i : Fin m) : rowWeight S y i ≤
      1 + (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0) := by
    have hi := bound i
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and]
    split <;> split <;> omega
  have total := Finset.sum_le_sum (s := Finset.univ) (fun i _ => pw i)
  simp [Finset.sum_add_distrib] at total
  omega

end PEqualNP.Research.Incidence997
