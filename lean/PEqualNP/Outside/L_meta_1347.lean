import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1347

-- Wire semantics from the checked project lemma L-meta-693.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
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

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
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

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool := Circuit.eval ⟨gs,w⟩ (List.ofFn x)

lemma gate_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : Fin gs.length) :
    val gs x (n+j.val) = (gs.get j).op.eval ((gs.get j).inputs.map fun k => if k < n+j.val then val gs x k else false) := by
  apply wires_gate_ofFn (C := ⟨gs, n+j.val⟩)
  simp

lemma input_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) : val gs x p.val = x p :=
  wires_input ⟨gs, p.val⟩ x p.val p.isLt

lemma beyond_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (h : n + gs.length ≤ j) : val gs x j = false :=
  wires_oob ⟨gs, j⟩ x j h

lemma secondGate {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gs : List Gate) (out : Fin m → ℕ)
    (hcalc : ∀ (o : Fin m) (x : Fin n → Bool),
      val gs x (out o) = decide (∃ v ∈ S o, x v = true))
    (ι : Fin 1 → Fin gs.length)
    (hone : ∀ q : Fin gs.length, (gs.get q).op = .not → ∃ r : Fin 1, ι r = q)
    (hvar : ∀ j : Fin gs.length, ∃ x y : Fin n → Bool,
      val gs x (n + j.val) ≠ val gs y (n + j.val))
    (hcopy : ∀ j : Fin gs.length, ∀ w : ℕ, w < n + j.val → ∃ x : Fin n → Bool,
      val gs x (n + j.val) ≠ val gs x w)
    (hused : ∀ j : Fin gs.length, (∃ o : Fin m, out o = n + j.val) ∨
      ∃ b : Fin gs.length, ((gs.get b).op = .not ∧ (gs.get b).inputs.head? = some (n+j.val)) ∨
        (((gs.get b).op = .and ∨ (gs.get b).op = .or) ∧ n+j.val ∈ (gs.get b).inputs))
    (hbin : ∀ j : Fin gs.length, ((gs.get j).op = .and ∨ (gs.get j).op = .or) →
      ∃ u v : ℕ, u ≠ v ∧ (gs.get j).inputs = [u, v])
    (p : Fin n) (hnot : (gs.get (ι 0)).op = .not) (hhead : (gs.get (ι 0)).inputs.head? = some p.val)
    (a : Fin gs.length) (ha : (gs.get a).op = .and ∨ (gs.get a).op = .or)
    (hpa : p.val ∈ (gs.get a).inputs) :
    ∃ b : Fin gs.length, b ≠ a ∧ ((gs.get b).op = .and ∨ (gs.get b).op = .or) ∧
      (gs.get b).inputs.length = 2 ∧ n + (ι 0).val ∈ (gs.get b).inputs := by
  have hpi : p.val < n + (ι 0).val := by omega
  have hple : p.val < n + a.val := by omega
  have hneg (x : Fin n → Bool) : val gs x (n + (ι 0).val) = !(x p) := by
    rw [gate_val gs x (ι 0), hnot]
    cases hh : (gs.get (ι 0)).inputs with
    | nil => simp [hh] at hhead
    | cons u us =>
      have hu : u = p.val := by simpa [hh] using hhead
      subst u
      simp [GateOp.eval, hpi, input_val]
  have distinctInputs : p.val ≠ n + (ι 0).val := by omega
  have collision (hm : n + (ι 0).val ∈ (gs.get a).inputs) : False := by
    obtain ⟨u, v, _, huv⟩ := hbin a ha
    have hp : p.val = u ∨ p.val = v := by simpa [huv] using hpa
    have hn : n + (ι 0).val = u ∨ n + (ι 0).val = v := by simpa [huv] using hm
    have hshape : (gs.get a).inputs = [p.val, n + (ι 0).val] ∨
        (gs.get a).inputs = [n + (ι 0).val, p.val] := by
      rw [huv]
      rcases hp with hp | hp <;> rcases hn with hn | hn
      · exact (distinctInputs (hp.trans hn.symm)).elim
      · exact Or.inl (by rw [hp, hn])
      · exact Or.inr (by rw [hp, hn])
      · exact (distinctInputs (hp.trans hn.symm)).elim
    have heval (x : Fin n → Bool) : val gs x (n + a.val) =
        (gs.get a).op.eval [x p, if n + (ι 0).val < n + a.val then !(x p) else false] := by
      rw [gate_val gs x a]
      rcases hshape with h | h
      · simp [h, hple, input_val, hneg]
      · rcases ha with hOp | hOp <;> by_cases hlt : n + (ι 0).val < n + a.val <;>
          cases hx : x p <;> simp [h, hOp, hlt, hx, hple, input_val, hneg, GateOp.eval]
    rcases ha with ha | ha
    · have hf (x : Fin n → Bool) : val gs x (n + a.val) = false := by
        rw [heval, ha]
        by_cases hlt : n + (ι 0).val < n + a.val <;>
          cases hx : x p <;> simp [GateOp.eval, hlt, hx]
      obtain ⟨x, y, hxy⟩ := hvar a
      exact hxy ((hf x).trans (hf y).symm)
    · by_cases hlt : n + (ι 0).val < n + a.val
      · have ht (x : Fin n → Bool) : val gs x (n + a.val) = true := by
          rw [heval, ha]
          cases hx : x p <;> simp [GateOp.eval, hlt, hx]
        obtain ⟨x, y, hxy⟩ := hvar a
        exact hxy ((ht x).trans (ht y).symm)
      · obtain ⟨x, hx⟩ := hcopy a p.val hple
        apply hx
        rw [heval, ha, input_val]
        simp [GateOp.eval, hlt]
  rcases hused (ι 0) with ⟨o, ho⟩ | ⟨b, hb⟩
  · have hx := hcalc o (fun _ => false)
    rw [ho, hneg] at hx
    simp at hx
  · rcases hb with ⟨hb, hh⟩ | ⟨hb, hm⟩
    · obtain ⟨r, hr⟩ := hone b hb
      have hr0 : r = 0 := Subsingleton.elim _ _
      have hb0 : b = ι 0 := by simpa [hr0] using hr.symm
      rw [hb0, hhead] at hh
      exact (distinctInputs (Option.some.inj hh)).elim
    · obtain ⟨u, v, _, huv⟩ := hbin b hb
      exact ⟨b, fun h => collision (h ▸ hm), hb, by simp [huv], hm⟩

end PEqualNP.Outside.L_meta_1347
