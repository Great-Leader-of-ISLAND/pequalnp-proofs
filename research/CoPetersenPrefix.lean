import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research.PetersenPrefix

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem preserved (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem atEnd (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

theorem firstValue {n : ℕ} (g : Gate) (tail : List Gate) (o : ℕ) (x : Fin n → Bool) :
    (Circuit.wires ⟨g :: tail,o⟩ (List.ofFn x)).getD n false =
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
  let w := List.ofFn x
  have hl : w.length = n := by simp [w]
  change (tail.foldl step (step w g)).getD n false = _
  rw [preserved tail (step w g) n (by simp [step, hl])]
  simpa only [step, w, List.length_ofFn] using atEnd (List.ofFn x) (g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false))

theorem emptyHead {n : ℕ} (o : ℕ) (x : Fin n → Bool) :
    (Circuit.wires ⟨[],o⟩ (List.ofFn x)).getD n false = false := by
  change (List.ofFn x).getD n false = false
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp : (List.ofFn x).length ≤ n)] <;> rfl

-- With the semantic head value known, the unmodified tail can be run directly
-- on the list of old inputs followed by that one bit. All wire indices agree.
theorem semanticTail {n : ℕ} (g : Gate) (tail : List Gate) (o : ℕ) (x : Fin n → Bool)
    (b : Bool) (head : (Circuit.wires ⟨g :: tail,o⟩ (List.ofFn x)).getD n false = b) :
    Circuit.eval ⟨g :: tail,o⟩ (List.ofFn x) =
      Circuit.eval ⟨tail,o⟩ (List.ofFn x ++ [b]) := by
  have h := (firstValue g tail o x).symm.trans head
  change (tail.foldl step (List.ofFn x ++ [g.op.eval (g.inputs.map fun i =>
    (List.ofFn x).getD i false)])).getD o false = _
  rw [h]
  rfl

theorem of_tail_bound {n k : ℕ} (h f : (Fin n → Bool) → Bool)
    (hnonzero : ∃ x, h x = true)
    (tailBound : ∀ D : Circuit, FanInTwo D →
      (∀ x, D.eval (List.ofFn x ++ [h x]) = f x) → k ≤ D.size) :
    ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD n false = h x) →
      circuitFun n C = f → k + 1 ≤ C.size := by
  intro C hfan hhead hfun
  obtain ⟨gs,o⟩ := C
  cases gs with
  | nil =>
    obtain ⟨x, hx⟩ := hnonzero
    have bad := hhead x
    rw [emptyHead, hx] at bad <;> cases bad
  | cons g tail =>
    let D : Circuit := ⟨tail,o⟩
    have hf : FanInTwo D := by
      intro gate hmem
      exact hfan gate (List.mem_cons_of_mem g hmem)
    have he : ∀ x, D.eval (List.ofFn x ++ [h x]) = f x := by
      intro x
      exact (semanticTail g tail o x (h x) (hhead x)).symm.trans (congrFun hfun x)
    have hs := tailBound D hf he
    change k ≤ tail.length at hs
    change k + 1 ≤ tail.length + 1
    exact Nat.add_le_add_right hs 1

-- A finite certificate may establish this counterexample-per-tail premise on
-- any fixed subset of assignments. It suffices for either nine-input shard.
theorem of_fourteen_gate_tests (h f : (Fin 9 → Bool) → Bool) (hnonzero : ∃ x, h x = true)
    (tests : ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
      ∃ x, D.eval (List.ofFn x ++ [h x]) ≠ f x) :
    ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = h x) →
      circuitFun 9 C = f → 16 ≤ C.size := by
  apply of_tail_bound (k := 15) h f hnonzero
  intro D hfan hall
  by_contra hn
  obtain ⟨x,hx⟩ := tests D hfan (by omega)
  exact hx (hall x)

theorem not_zero_witness : ∃ x : Fin 9 → Bool, !(x 0) = true := ⟨fun _ => false, rfl⟩

theorem and_zero_one_witness : ∃ x : Fin 9 → Bool, (x 0 && x 1) = true := ⟨fun _ => true, rfl⟩

end PEqualNP.Research.PetersenPrefix
