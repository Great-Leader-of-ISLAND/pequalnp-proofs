import Mathlib
import PEqualNP.Defs
namespace CoSwitch3302
def f8 (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
end CoSwitch3302
-- The circuit monotonicity lemmas are from the checked L-meta-1572 (using L-meta-1353).
namespace CoSwitch3302.MonotoneWires3302
open PEqualNP.CircuitLowerBounds
-- The wire evaluation lemmas follow L-meta-1353.

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

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

abbrev AO (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma wires_mono {n : ℕ} (C : Circuit) (hAO : AO C) (x y : Fin n → Bool)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let p : Fin n := ⟨w, hw⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases h : w < n + C.size
    · let k := w - n
      have hk : k < C.gates.length := by dsimp [k]; unfold Circuit.size at h; omega
      have hwk : w = n + k := by dsimp [k]; omega
      rw [hwk]
      refine gate_mono C k hk (hAO _ (List.getElem_mem hk)).1 x y ?_
      intro r _ hr
      exact ih r (by omega)
    · rw [missing_value C x w (by omega)]
      simp


end CoSwitch3302.MonotoneWires3302
namespace CoSwitch3302
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open MonotoneWires3302

private theorem last_mono (Q : Circuit) (ao : AO Q) (ws : List Bool) (b : Bool) :
    Q.eval (ws ++ [false]) = true → Q.eval (ws ++ [b]) = true := by
  have snocList (z : Bool) : List.ofFn (Fin.snoc ws.get z) = ws ++ [z] := by
    rw [List.ofFn_succ']
    simp [Fin.snoc]
  have h : ∀ i, (Fin.snoc ws.get false : Fin (ws.length+1) → Bool) i = true →
      (Fin.snoc ws.get b : Fin (ws.length+1) → Bool) i = true := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      simp
    · simp only [Fin.snoc_castSucc]
      exact id
  have m := wires_mono Q ao (Fin.snoc ws.get false) (Fin.snoc ws.get b) h Q.output
  change Q.eval (List.ofFn (Fin.snoc ws.get false)) = true → Q.eval (List.ofFn (Fin.snoc ws.get b)) = true at m
  simpa only [snocList] using m

theorem switch_not (P Q : Circuit) (idx : Nat) (fan : FanInTwo Q)
    (actual : ∀ x : Fin 8 → Bool,
      Q.eval (P.wires (List.ofFn x) ++ [(P.wires (List.ofFn x)).getD idx false]) = f8 x)
    (zeroed : ∀ x : Fin 8 → Bool,
      Q.eval (P.wires (List.ofFn x) ++ [false]) = (f8 x || x 0 || x 3)) :
    ∃ g ∈ Q.gates, g.op = .not := by
  by_contra no
  have mono : AO Q := by
    intro g hg
    have h := (fan g hg).1
    have hn : g.op ≠ .not := fun e => no ⟨g,hg,e⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    exact ⟨h.elim Or.inl (fun h => Or.inr (h.resolve_right hn)),(fan g hg).2⟩
  let x : Fin 8 → Bool := fun i => decide (i=0)
  have noEdge : f8 x = false := by decide +kernel
  have one : Q.eval (P.wires (List.ofFn x) ++ [false]) = true := by
    rw [zeroed,noEdge]
    decide
  have high := last_mono Q mono _ ((P.wires (List.ofFn x)).getD idx false) one
  rw [actual,noEdge] at high
  exact Bool.false_ne_true high
end CoSwitch3302
