import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Research.CoMaskCircuit
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Redirect selected *input* wires to an index outside the final wire table. -/
def rewire (n : ℕ) (S : Finset ℕ) (bad i : ℕ) : ℕ :=
  if i < n ∧ i ∈ S then bad else i

def maskGate (n : ℕ) (S : Finset ℕ) (bad : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rewire n S bad)⟩

def maskCircuit (n : ℕ) (S : Finset ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (maskGate n S (n + C.gates.length)),
   rewire n S (n + C.gates.length) C.output⟩

theorem size_mask (n : ℕ) (S : Finset ℕ) (C : Circuit) :
    (maskCircuit n S C).size = C.size := by
  simp [maskCircuit, Circuit.size]

theorem monotone2_mask (n : ℕ) (S : Finset ℕ) (C : Circuit) :
    Monotone2 (maskCircuit n S C) ↔ Monotone2 C := by
  constructor
  · intro h g hg
    have hm : maskGate n S (n + C.gates.length) g ∈ (maskCircuit n S C).gates :=
      List.mem_map.mpr ⟨g, hg, rfl⟩
    simpa [maskGate] using h _ hm
  · intro h g hg
    change g ∈ C.gates.map (maskGate n S (n + C.gates.length)) at hg
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
    simpa [maskGate] using h u hu

private theorem get_snoc {α : Type} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i = l.length then a else l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hb : i < l.length
  · rw [List.getElem?_append_left hb, if_neg (Nat.ne_of_lt hb)]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by omega : l.length ≤ i)]
    by_cases he : i = l.length
    · subst i; simp
    · have hn : i - l.length ≠ 0 := by omega
      simp [he, List.getElem?_cons, hn]

private def step {α : Type} (f : GateOp → List α → α) (d : α) (w : List α) (g : Gate) :
    List α := w ++ [f g.op (g.inputs.map fun i => w.getD i d)]

/-- A fold invariant independent of the gate algebra, including for ill-founded wire references. -/
private theorem fold_sim {α : Type} (f : GateOp → List α → α) (d : α)
    (n : ℕ) (S : Finset ℕ) (bad : ℕ) (gs : List Gate) (l r : List α)
    (hlen : l.length = r.length) (hn : n ≤ l.length) (hb : l.length + gs.length ≤ bad)
    (rel : ∀ i, l.getD (rewire n S bad i) d = r.getD i d) :
    ∀ i, ((gs.map (maskGate n S bad)).foldl (step f d) l).getD (rewire n S bad i) d =
      (gs.foldl (step f d) r).getD i d := by
  induction gs generalizing l r with
  | nil => exact rel
  | cons g gs ih =>
    let a := f g.op (g.inputs.map fun i => r.getD i d)
    have pins : (maskGate n S bad g).inputs.map (fun i => l.getD i d) =
        g.inputs.map (fun i => r.getD i d) := by
      simp only [maskGate, List.map_map]
      apply List.map_congr_left
      intro i _
      exact rel i
    have left : step f d l (maskGate n S bad g) = l ++ [a] := by
      unfold step
      rw [pins] <;> rfl
    have right : step f d r g = r ++ [a] := rfl
    simp only [List.map_cons, List.foldl_cons, left, right]
    apply ih
    · simpa using hlen
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton, List.length_cons] at hb ⊢; omega
    · intro i
      have he : rewire n S bad i = l.length ↔ i = r.length := by
        by_cases hk : i < n ∧ i ∈ S
        · have hi : i < l.length := lt_of_lt_of_le hk.1 hn
          have hbad : l.length < bad := by simp only [List.length_cons] at hb; omega
          simp [rewire, hk, ← hlen, ne_of_gt hbad, ne_of_lt hi]
        · simp [rewire, hk, hlen]
      simp only [get_snoc, he, rel]

private theorem fn_get {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (d : α) :
    (List.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < n <;> simp [h]

/-- For all input assignments, selected input positions are set to false. -/
theorem eval_mask (n : ℕ) (S : Finset ℕ) (C : Circuit) (x : Fin n → Bool) :
    (maskCircuit n S C).eval (List.ofFn x) =
      C.eval (List.ofFn fun i : Fin n => if i.val ∈ S then false else x i) := by
  apply fold_sim GateOp.eval false n S (n + C.gates.length) C.gates (List.ofFn x)
    (List.ofFn fun i : Fin n => if i.val ∈ S then false else x i)
  · simp
  · simp
  · simp
  · intro i
    have hb : ¬ n + C.gates.length < n := by omega
    by_cases hi : i < n <;> by_cases hs : i ∈ S <;> simp [rewire, fn_get, hi, hs, hb]

private def deg (op : GateOp) (xs : List ℕ) : ℕ :=
  @ite ℕ (op = GateOp.and) (lineDegreeGateOpDecEq op GateOp.and) xs.sum (xs.foldr max 0)

private def init (n : ℕ) (M : Finset ℕ) : List ℕ :=
  (List.range n).map fun i => if i ∈ M then 1 else 0

private theorem init_get (n : ℕ) (M : Finset ℕ) (i : ℕ) :
    (init n M).getD i 0 = if i < n ∧ i ∈ M then 1 else 0 := by
  by_cases hi : i < n <;> by_cases hm : i ∈ M <;>
    simp [init, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi, hm]

/-- Exact output degree: disabling inputs is the same as removing their initial degrees. -/
theorem lineDeg_mask (n : ℕ) (S M : Finset ℕ) (C : Circuit) :
    (maskCircuit n S C).lineDeg n M = C.lineDeg n (M \ S) := by
  apply fold_sim deg 0 n S (n + C.gates.length) C.gates (init n M) (init n (M \ S))
  · simp [init]
  · simp [init]
  · simp [init]
  · intro i
    have hb : ¬ n + C.gates.length < n := by omega
    by_cases hi : i < n <;> by_cases hs : i ∈ S <;>
      simp [rewire, init_get, hi, hs, hb]

private theorem deg_mono (g : Gate) (l r : List ℕ) (h : ∀ i, l.getD i 0 ≤ r.getD i 0) :
    g.lineDegree l ≤ g.lineDegree r := by
  have hs (js : List ℕ) : (js.map fun i => l.getD i 0).sum ≤ (js.map fun i => r.getD i 0).sum := by
    induction js with
    | nil => exact Nat.le_refl 0
    | cons i is ih => simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add (h i) ih
  have hm (js : List ℕ) : (js.map fun i => l.getD i 0).foldr max 0 ≤
      (js.map fun i => r.getD i 0).foldr max 0 := by
    induction js with
    | nil => exact Nat.le_refl 0
    | cons i is ih => exact max_le_max (h i) ih
  unfold Gate.lineDegree
  split
  · exact hs _
  · exact hm _

private theorem degree_fold_mono (gs : List Gate) (l r : List ℕ)
    (hlen : l.length = r.length) (h : ∀ i, l.getD i 0 ≤ r.getD i 0) :
    ∀ i, (gs.foldl (step deg 0) l).getD i 0 ≤ (gs.foldl (step deg 0) r).getD i 0 := by
  induction gs generalizing l r with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp [step, hlen]
    · intro i
      change (l ++ [g.lineDegree l]).getD i 0 ≤ (r ++ [g.lineDegree r]).getD i 0
      rw [get_snoc, get_snoc, hlen]
      by_cases he : i = r.length
      · simpa [he] using deg_mono g l r h
      · simpa [he] using h i

theorem lineDeg_mono_marked (C : Circuit) (n : ℕ) (M N : Finset ℕ) (h : M ⊆ N) :
    C.lineDeg n M ≤ C.lineDeg n N := by
  apply degree_fold_mono C.gates (init n M) (init n N)
  · simp [init]
  · intro i
    by_cases hm : i ∈ M
    · simp [init_get, hm, h hm]
    · simp [init_get, hm]

theorem lineDeg_mask_le (n : ℕ) (S M : Finset ℕ) (C : Circuit) :
    (maskCircuit n S C).lineDeg n M ≤ C.lineDeg n M := by
  rw [lineDeg_mask]
  apply lineDeg_mono_marked
  intro i hi
  exact (Finset.mem_sdiff.mp hi).1

end PEqualNP.Research.CoMaskCircuit
