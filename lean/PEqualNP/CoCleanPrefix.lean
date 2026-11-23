import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Research.CoCleanPrefix

/-!
For a prefix containing only AND and OR, suppose every AND is false at an
assignment and at each selected singleton. On that assignment every wire
fires exactly when it fires at one of those singletons. This establishes a
local structural lemma; it has no circuit-size conclusion.

The following wire-evaluation helpers follow the project's L-meta-693.
-/
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

private theorem getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

private theorem foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

private theorem foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

private theorem foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

private theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

private theorem wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

private theorem ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

private theorem wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

private theorem wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool := Circuit.eval ⟨gs,w⟩ (List.ofFn x)

private theorem gate_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : Fin gs.length) :
    val gs x (n+j.val) = (gs.get j).op.eval ((gs.get j).inputs.map fun k => if k < n+j.val then val gs x k else false) := by
  apply wires_gate_ofFn (C := ⟨gs, n+j.val⟩)
  simp

private theorem input_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) : val gs x p.val = x p :=
  wires_input ⟨gs, p.val⟩ x p.val p.isLt

private theorem beyond_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (h : n + gs.length ≤ j) : val gs x j = false :=
  wires_oob ⟨gs, j⟩ x j h

/-- The input having exactly one selected vertex. -/
def one {n : ℕ} (p : Fin n) (q : Fin n) : Bool := decide (q = p)

private theorem or_fires {n : ℕ} (gs : List Gate) (x : Fin n → Bool)
    (j : Fin gs.length) (hj : (gs.get j).op = .or) :
    val gs x (n + j.val) = true ↔ ∃ k ∈ (gs.get j).inputs,
      k < n + j.val ∧ val gs x k = true := by
  rw [gate_val, hj]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨k, hk, hval⟩
    by_cases hlt : k < n + j.val
    · exact ⟨k, hk, hlt, by simpa [hlt] using hval⟩
    · simp [hlt] at hval
  · rintro ⟨k, hk, hlt, hval⟩
    exact ⟨k, hk, by simpa [hlt] using hval⟩

/-- Take gs to be the prefix ending immediately before the first junk AND.
The clean hypothesis is required only at x and its selected singleton inputs.
The conclusion includes primary wires, computed wires and out-of-range wires.
It applies to OR gates of arbitrary fan-in, including empty input lists. -/
theorem prefix_fires_iff_singleton {n : ℕ} (gs : List Gate) (x : Fin n → Bool)
    (hops : ∀ j : Fin gs.length, (gs.get j).op = .and ∨ (gs.get j).op = .or)
    (hclean : ∀ j : Fin gs.length, (gs.get j).op = .and →
      val gs x (n + j.val) = false ∧
        ∀ p : Fin n, x p = true → val gs (one p) (n + j.val) = false)
    (w : ℕ) :
    val gs x w = true ↔ ∃ p : Fin n, x p = true ∧ val gs (one p) w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < n
    · let q : Fin n := ⟨w, hw⟩
      change val gs x q.val = true ↔
        ∃ p : Fin n, x p = true ∧ val gs (one p) q.val = true
      rw [input_val]
      constructor
      · intro hq
        exact ⟨q, hq, by rw [input_val]; simp [one]⟩
      · rintro ⟨p, hp, hq⟩
        rw [input_val] at hq
        have heq : q = p := of_decide_eq_true hq
        exact heq.symm ▸ hp
    by_cases far : n + gs.length ≤ w
    · have hfalse (y : Fin n → Bool) : val gs y w = false := beyond_val gs y w far
      simp [hfalse]
    let j : Fin gs.length := ⟨w - n, by omega⟩
    have hwj : n + j.val = w := by dsimp [j]; omega
    rw [← hwj]
    rcases hops j with hand | hor
    · obtain ⟨hx, hsingle⟩ := hclean j hand
      constructor
      · intro h
        rw [hx] at h
        contradiction
      · rintro ⟨p, hp, hv⟩
        rw [hsingle p hp] at hv
        contradiction
    · constructor
      · intro h
        obtain ⟨k, hk, hlt, hv⟩ := (or_fires gs x j hor).mp h
        obtain ⟨p, hp, hx⟩ := (ih k (by omega)).mp hv
        exact ⟨p, hp, (or_fires gs (one p) j hor).mpr ⟨k, hk, hlt, hx⟩⟩
      · rintro ⟨p, hp, h⟩
        obtain ⟨k, hk, hlt, hv⟩ := (or_fires gs (one p) j hor).mp h
        exact (or_fires gs x j hor).mpr ⟨k, hk, hlt, (ih k (by omega)).mpr ⟨p, hp, hv⟩⟩

end PEqualNP.Research.CoCleanPrefix
