import PEqualNP.CoPetersenRaw

namespace PEqualNP.Research.PetersenCnf

open PEqualNP.Research.PetersenRaw
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

-- Values of signed literals after applying a single assignment.
def holds (cl : List Bool) : Prop := true ∈ cl

def sel {n : ℕ} (p i : Fin n) : Bool := decide (i = p)

def oneHot {n : ℕ} (flags : Fin n → Bool) : Prop :=
  (∃ i, flags i = true) ∧
  ∀ i j, i ≠ j → holds [!(flags i), !(flags j)]

private theorem oneHot_sel {n : ℕ} (p : Fin n) : oneHot (sel p) := by
  refine ⟨⟨p, by simp [sel]⟩, ?_⟩
  intro i j hij
  by_cases hi : i = p
  · subst i
    have hj : j ≠ p := Ne.symm hij
    simp [holds, sel, hj]
  · simp [holds, sel, hi]

def muxOK {n : ℕ} (pick src : Fin n → Bool) (out : Bool) : Prop :=
  ∀ i, holds [!(pick i), !(src i), out] ∧ holds [!(pick i), src i, !out]

private theorem mux_selected {n : ℕ} (p : Fin n) (src : Fin n → Bool) :
    muxOK (sel p) src (src p) := by
  intro i
  by_cases hi : i = p
  · subst i
    cases h : src p <;> simp [sel, holds, h]
  · simp [sel, holds, hi]

def opValue (op : Fin 3) (a b : Bool) : Bool :=
  if op = 0 then a && b else if op = 1 then a || b else !a

def truthClauses (isAnd isOr isNot a b z : Bool) : Prop :=
  holds [!isAnd,!z,a] ∧ holds [!isAnd,!z,b] ∧ holds [!isAnd,z,!a,!b] ∧
  holds [!isOr,z,!a] ∧ holds [!isOr,z,!b] ∧ holds [!isOr,!z,a,b] ∧
  holds [!isNot,!z,!a] ∧ holds [!isNot,z,a]

private theorem truth_selected (op : Fin 3) (a b : Bool) :
    truthClauses (sel op 0) (sel op 1) (sel op 2) a b (opValue op a b) := by
  fin_cases op <;> cases a <;> cases b <;> unfold truthClauses holds <;> decide

structure Bits (m r : ℕ) where
  op : Fin 3 → Bool
  left : Pin m → Bool
  right : Pin m → Bool
  aval : Sig r
  bval : Sig r
  out : Sig r

def structOK {m r : ℕ} (v : Bits m r) : Prop :=
  oneHot v.op ∧ oneHot v.left ∧ oneHot v.right ∧
  holds [!(v.op 2), v.right (missing m)] ∧
  ∀ i j : Pin m, j < i → holds [!(v.left i), !(v.right j)]

-- At each index p, readPin is a constant, a previous row literal, or the
-- isAnd flag for a missing operand. There is no mux on a SAT-valued index.
def layer {r : ℕ} (s : List (Sig r)) (v : Bits s.length r) : Prop :=
  structOK v ∧ ∀ z,
    muxOK v.left (fun p => readPin (row s z) (v.op 0) p) (v.aval z) ∧
    muxOK v.right (fun p => readPin (row s z) (v.op 0) p) (v.bval z) ∧
    truthClauses (v.op 0) (v.op 1) (v.op 2) (v.aval z) (v.bval z) (v.out z)

def forCode {r : ℕ} (s : List (Sig r)) (c : Code s.length) : Bits s.length r where
  op := sel c.1
  left := sel c.2.1
  right := sel c.2.2
  aval := fun z => readPin (row s z) (sel c.1 0) c.2.1
  bval := fun z => readPin (row s z) (sel c.1 0) c.2.2
  out := fun z => evalCode c (row s z)

private theorem legal_order {m : ℕ} (c : Code m) (h : Legal c) :
    c.2.1 ≤ c.2.2 := by
  by_cases hn : c.1 = 2
  · have hr : c.2.2 = missing m := by simpa [Legal, hn] using h
    rw [hr]
    change c.2.1.val ≤ m + 1
    have hi := c.2.1.isLt
    omega
  · simpa [Legal, hn] using h

private theorem struct_selected {r : ℕ} (s : List (Sig r)) (c : Code s.length)
    (hc : Legal c) : structOK (forCode s c) := by
  refine ⟨oneHot_sel _, oneHot_sel _, oneHot_sel _, ?_, ?_⟩
  · by_cases hn : c.1 = 2
    · have hr : c.2.2 = missing s.length := by simpa [Legal, hn] using hc
      simp [holds, forCode, sel, hn, hr]
    · have hn' : (2 : Fin 3) ≠ c.1 := Ne.symm hn
      simp [holds, forCode, sel, hn']
  · intro i j hji
    by_cases hi : i = c.2.1
    · have hj : j ≠ c.2.2 := by
        intro hj
        rw [hi, hj] at hji
        exact (not_lt_of_ge (legal_order c hc)) hji
      simp [holds, forCode, sel, hj]
    · simp [holds, forCode, sel, hi]

private theorem eval_identity {m : ℕ} (c : Code m) (w : List Bool) :
    evalCode c w = opValue c.1 (readPin w (sel c.1 0) c.2.1)
      (readPin w (sel c.1 0) c.2.2) := by
  obtain ⟨op, a, b⟩ := c
  fin_cases op <;> rfl

theorem codeModel {r : ℕ} (s : List (Sig r)) (c : Code s.length) (hc : Legal c) :
    layer s (forCode s c) := by
  refine ⟨struct_selected s c hc, ?_⟩
  intro z
  refine ⟨mux_selected c.2.1 _, mux_selected c.2.2 _, ?_⟩
  change truthClauses (sel c.1 0) (sel c.1 1) (sel c.1 2) _ _ (evalCode c (row s z))
  rw [eval_identity]
  exact truth_selected _ _ _

-- One common output selector for all rows, including the false OOB output.
def terminal {r : ℕ} (s : List (Sig r)) (t : Sig r) (flags : Fin (s.length+1) → Bool) : Prop :=
  oneHot flags ∧ ∀ z i, holds [!(flags i), if t z then (row s z).getD i.val false
      else !((row s z).getD i.val false)]

private theorem endModel {r : ℕ} (s : List (Sig r)) (t : Sig r) (h : Ends s t) :
    ∃ flags, terminal s t flags := by
  obtain ⟨o, ho⟩ := h
  refine ⟨sel o, oneHot_sel o, ?_⟩
  intro z i
  by_cases hi : i = o
  · subst i
    rw [ho z]
    cases ht : t z <;> simp [holds, sel, ht]
  · simp [holds, sel, hi]

-- Dynamic presentation of a fixed-length CNF. The length of s is fixed by
-- the layer index. Only its Boolean entries depend on the assignment. Each
-- existential allocates disjoint choice, operand and output variables.
def FormulaSat {r : ℕ} : ℕ → List (Sig r) → Sig r → Prop
  | 0, s, t => ∃ flags, terminal s t flags
  | k+1, s, t => ∃ v : Bits s.length r, layer s v ∧ FormulaSat k (s ++ [v.out]) t

private theorem ends_append {r : ℕ} (s : List (Sig r)) (v t : Sig r) (h : Ends s t) :
    Ends (s ++ [v]) t := by
  obtain ⟨o, ho⟩ := h
  by_cases hi : o.val < s.length
  · refine ⟨⟨o.val, by simp⟩, ?_⟩
    intro z
    have hrow : o.val < (row s z).length := by simpa [row] using hi
    have happ : row (s ++ [v]) z = row s z ++ [v z] := by simp [row]
    change (row (s ++ [v]) z).getD o.val false = t z
    rw [happ, List.getD_eq_getElem?_getD, List.getElem?_append_left hrow]
    exact ho z
  · refine ⟨⟨(s ++ [v]).length, Nat.lt_succ_self _⟩, ?_⟩
    intro z
    have hrow : (row s z).length ≤ o.val := by simpa [row] using (Nat.le_of_not_gt hi)
    have hrow' : (row (s ++ [v]) z).length ≤ (s ++ [v]).length := by simp [row]
    have hz := ho z
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hrow] at hz
    change (row (s ++ [v]) z).getD (s ++ [v]).length false = t z
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hrow']
    exact hz

private theorem padModel {r : ℕ} (k : ℕ) (s : List (Sig r)) (t : Sig r)
    (h : Ends s t) : FormulaSat k s t := by
  induction k generalizing s with
  | zero => exact endModel s t h
  | succ k ih =>
    let c : Code s.length := (1, missing _, missing _)
    have hc : Legal c := by simp [Legal, c]
    refine ⟨forCode s c, codeModel s c hc, ?_⟩
    exact ih _ (ends_append s _ t h)

theorem reach_model {r : ℕ} (k : ℕ) (s : List (Sig r)) (t : Sig r)
    (h : Reach k s t) : FormulaSat k s t := by
  induction k generalizing s with
  | zero => exact endModel s t h
  | succ k ih =>
    rcases h with hs | ⟨c, hc, hr⟩
    · exact padModel (k+1) s t hs
    · exact ⟨forCode s c, codeModel s c hc, ih _ hr⟩

theorem raw_model {r : ℕ} (k : ℕ) (s : List (Sig r)) (t : Sig r) (D : Circuit)
    (hfan : FanInTwo D) (hsize : D.size ≤ k) (hrows : ∀ z, D.eval (row s z) = t z) :
    FormulaSat k s t := reach_model k s t (raw_reaches k s t D hfan hsize hrows)

theorem of_cnf_exclusion {r n : ℕ} (k : ℕ) (xs : Fin r → Fin n → Bool)
    (head f : (Fin n → Bool) → Bool)
    (no : ¬ FormulaSat k (initial xs head) (fun z => f (xs z))) :
    ∀ D : Circuit, FanInTwo D → D.size ≤ k →
      ∃ x, D.eval (List.ofFn x ++ [head x]) ≠ f x :=
  of_finite_exclusion k xs head f (fun h => no (reach_model _ _ _ h))


-- Python's raw one_hot uses the first flag directly as cumulative bit zero;
-- each adjacent pair then contributes these four clauses. A unit clause ends
-- the chain. For n > 0 this describes exactly the emitted prefix template.
def prefixFlag {n : ℕ} (p i : Fin n) : Bool := decide (p.val ≤ i.val)

def cumulative {n : ℕ} (pick pre : Fin n → Bool) : Prop :=
  (∀ i, i.val = 0 → pre i = pick i) ∧
  (∀ i, i.val + 1 = n → holds [pre i]) ∧
  ∀ i j, j.val = i.val + 1 →
    holds [!(pre i),pre j] ∧ holds [!(pick j),pre j] ∧
    holds [!(pre i),!(pick j)] ∧ holds [!(pre j),pre i,pick j]

private theorem prefix_chosen {n : ℕ} (p : Fin n) :
    cumulative (sel p) (prefixFlag p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have eq : (p.val ≤ i.val) ↔ (i = p) := by
      constructor
      · intro hp
        apply Fin.ext
        omega
      · rintro rfl
        exact le_rfl
    simp only [prefixFlag, sel, eq]
  · intro i hi
    have hp := p.isLt
    have hle : p.val ≤ i.val := by omega
    simp [holds, prefixFlag, hle]
  · intro i j hij
    by_cases h1 : p.val ≤ i.val
    · have h2 : p.val ≤ j.val := by omega
      have h3 : j ≠ p := by intro he; obtain rfl := he; omega
      simp [holds, prefixFlag, sel, h1, h2, h3]
    · by_cases h3 : j = p
      · subst j
        simp [holds, prefixFlag, sel, h1]
      · have h2 : ¬p.val ≤ j.val := by
          intro hp
          apply h3
          apply Fin.ext
          omega
        simp [holds, prefixFlag, sel, h1, h2, h3]

private theorem selector_repr {n : ℕ} {f : Fin n → Bool} (h : oneHot f) :
    ∃ p, f = sel p := by
  obtain ⟨⟨p,hp⟩,hm⟩ := h
  refine ⟨p, ?_⟩
  funext i
  by_cases hi : i = p
  · subst i
    simp [sel, hp]
  · cases hval : f i with
    | false => simp [sel, hi]
    | true =>
      have hf := hm i p hi
      simp [holds, hp, hval] at hf

def prefixStruct {m r : ℕ} (v : Bits m r) : Prop :=
  oneHot v.op ∧ holds [!(v.op 2),v.right (missing m)] ∧
    ∃ pl pr : Pin m → Bool, cumulative v.left pl ∧ cumulative v.right pr ∧
      ∀ i, holds [!(pr i),pl i]

private theorem prefixStruct_model {m r : ℕ} (v : Bits m r) (hv : structOK v) :
    prefixStruct v := by
  obtain ⟨ops, ls, rs, hn, horder⟩ := hv
  obtain ⟨l, hl⟩ := selector_repr ls
  obtain ⟨r, hr⟩ := selector_repr rs
  have hlr : l ≤ r := by
    by_contra! hlt
    have hf := horder l r hlt
    simp [holds, hl, hr, sel] at hf
  refine ⟨ops, hn, prefixFlag l, prefixFlag r, ?_, ?_, ?_⟩
  · rw [hl]
    exact prefix_chosen l
  · rw [hr]
    exact prefix_chosen r
  · intro i
    by_cases hri : r.val ≤ i.val
    · have hli : l.val ≤ i.val := Nat.le_trans hlr hri
      simp [holds, prefixFlag, hli]
    · simp [holds, prefixFlag, hri]

-- This formula uses the cumulative bits of the raw Python implementation.
-- Wire numbering, clause serialization, removal of constants by add(), and
-- any use of normal-mode symmetry or pruning are separate obligations.
def PrefixSat {r : ℕ} : ℕ → List (Sig r) → Sig r → Prop
  | 0, s, t => ∃ flags pre : Fin (s.length+1) → Bool, cumulative flags pre ∧
      ∀ z i, holds [!(flags i), if t z then (row s z).getD i.val false
        else !((row s z).getD i.val false)]
  | k+1, s, t => ∃ v : Bits s.length r, prefixStruct v ∧ (∀ z,
      muxOK v.left (fun p => readPin (row s z) (v.op 0) p) (v.aval z) ∧
      muxOK v.right (fun p => readPin (row s z) (v.op 0) p) (v.bval z) ∧
      truthClauses (v.op 0) (v.op 1) (v.op 2) (v.aval z) (v.bval z) (v.out z)) ∧
      PrefixSat k (s ++ [v.out]) t

theorem prefix_model {r : ℕ} (k : ℕ) (s : List (Sig r)) (t : Sig r)
    (h : FormulaSat k s t) : PrefixSat k s t := by
  induction k generalizing s with
  | zero =>
    obtain ⟨flags, hf, hz⟩ := h
    obtain ⟨p, rfl⟩ := selector_repr hf
    exact ⟨_, prefixFlag p, prefix_chosen p, hz⟩
  | succ k ih =>
    obtain ⟨v, hv, ht⟩ := h
    exact ⟨v, prefixStruct_model v hv.1, hv.2, ih _ ht⟩

theorem raw_prefix_model {r : ℕ} (k : ℕ) (s : List (Sig r)) (t : Sig r) (D : Circuit)
    (hfan : FanInTwo D) (hsize : D.size ≤ k) (hrows : ∀ z, D.eval (row s z) = t z) :
    PrefixSat k s t := prefix_model k s t (raw_model k s t D hfan hsize hrows)

theorem of_prefix_exclusion {r n : ℕ} (k : ℕ) (xs : Fin r → Fin n → Bool)
    (head f : (Fin n → Bool) → Bool)
    (no : ¬ PrefixSat k (initial xs head) (fun z => f (xs z))) :
    ∀ D : Circuit, FanInTwo D → D.size ≤ k →
      ∃ x, D.eval (List.ofFn x ++ [head x]) ≠ f x :=
  of_cnf_exclusion k xs head f (fun h => no (prefix_model _ _ _ h))

end PEqualNP.Research.PetersenCnf
