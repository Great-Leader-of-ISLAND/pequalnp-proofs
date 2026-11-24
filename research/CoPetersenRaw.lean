import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research.PetersenRaw
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

abbrev Pin (m : ℕ) := Fin (m + 2)
abbrev Code (m : ℕ) := Fin 3 × Pin m × Pin m
abbrev Sig (r : ℕ) := Fin r → Bool

def clip (m i : ℕ) : Pin m := ⟨min i m, by omega⟩
def missing (m : ℕ) : Pin m := ⟨m+1, by omega⟩

def readPin {m : ℕ} (w : List Bool) (empty : Bool) (p : Pin m) : Bool :=
  if p.val = m+1 then empty else w.getD p.val false

private theorem readMissing (m : ℕ) (w : List Bool) (d : Bool) :
    readPin w d (missing m) = d := by simp [readPin, missing]

private theorem readClip {m : ℕ} (w : List Bool) (hw : w.length = m) (d : Bool) (i : ℕ) :
    readPin w d (clip m i) = w.getD i false := by
  subst m
  have hne : min i w.length ≠ w.length + 1 := by omega
  simp only [readPin, clip, hne, if_false]
  by_cases hi : i < w.length
  · rw [min_eq_left (by omega : i ≤ w.length)]
  · rw [min_eq_right (by omega : w.length ≤ i)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (le_refl w.length),
      List.getElem?_eq_none (by omega : w.length ≤ i)]

def binary {m : ℕ} (op : Fin 3) (a b : Pin m) : Code m := (op, min a b, max a b)
def unary {m : ℕ} (a : Pin m) : Code m := (2, a, missing m)

def Legal {m : ℕ} (c : Code m) : Prop :=
  if c.1 = 2 then c.2.2 = missing m else c.2.1 ≤ c.2.2

def evalCode {m : ℕ} (c : Code m) (w : List Bool) : Bool :=
  if c.1 = 0 then readPin w true c.2.1 && readPin w true c.2.2
  else if c.1 = 1 then readPin w false c.2.1 || readPin w false c.2.2
  else !(readPin w false c.2.1)

private theorem andValue {m : ℕ} (a b : Pin m) (w : List Bool) :
    evalCode (binary 0 a b) w = (readPin w true a && readPin w true b) := by
  by_cases h : a ≤ b
  · simp [evalCode, binary, min_eq_left h, max_eq_right h]
  · have h' := le_of_not_ge h
    simp [evalCode, binary, min_eq_right h', max_eq_left h', Bool.and_comm]

private theorem orValue {m : ℕ} (a b : Pin m) (w : List Bool) :
    evalCode (binary 1 a b) w = (readPin w false a || readPin w false b) := by
  by_cases h : a ≤ b
  · simp [evalCode, binary, min_eq_left h, max_eq_right h]
  · have h' := le_of_not_ge h
    simp [evalCode, binary, min_eq_right h', max_eq_left h', Bool.or_comm]

private theorem notValue {m : ℕ} (a : Pin m) (w : List Bool) :
    evalCode (unary a) w = !(readPin w false a) := by simp [evalCode, unary]

def encodeGate (m : ℕ) (g : Gate) : Code m :=
  let a := match g.inputs with | i :: _ => clip m i | [] => missing m
  let b := match g.inputs with | _ :: j :: _ => clip m j | _ => missing m
  match g.op with
  | .and => binary 0 a b
  | .or => binary 1 a b
  | _ => unary a

theorem legal_encode (m : ℕ) (g : Gate) : Legal (encodeGate m g) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [Legal, encodeGate, binary, unary, min_le_max]

private theorem shortShape (ls : List ℕ) (h : ls.length ≤ 2) :
    ls = [] ∨ (∃ a, ls = [a]) ∨ ∃ a b, ls = [a,b] := by
  cases ls with
  | nil => exact Or.inl rfl
  | cons a xs =>
    cases xs with
    | nil => exact Or.inr (Or.inl ⟨a,rfl⟩)
    | cons b ys =>
      cases ys with
      | nil => exact Or.inr (Or.inr ⟨a,b,rfl⟩)
      | cons z zs => simp only [List.length_cons] at h; omega

theorem eval_encode (m : ℕ) (g : Gate) (w : List Bool) (hw : w.length = m)
    (hop : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    evalCode (encodeGate m g) w = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at hop
  change ins.length ≤ 2 at hlen
  rcases shortShape ins hlen with h | ⟨a,h⟩ | ⟨a,b,h⟩ <;> subst ins <;>
    rcases hop with h | h | h <;> subst op <;>
    simp [encodeGate, andValue, orValue, notValue, readMissing, readClip w hw, GateOp.eval]

def row {r : ℕ} (s : List (Sig r)) (z : Fin r) : List Bool := s.map (fun a => a z)

def extend {r : ℕ} (s : List (Sig r)) (c : Code s.length) : List (Sig r) :=
  s ++ [fun z => evalCode c (row s z)]

private theorem row_extend {r : ℕ} (s : List (Sig r)) (c : Code s.length) (z : Fin r) :
    row (extend s c) z = row s z ++ [evalCode c (row s z)] := by
  simp [row, extend]

-- The final index s.length is the single out-of-bounds output reading false.
def Ends {r : ℕ} (s : List (Sig r)) (target : Sig r) : Prop :=
  ∃ o : Fin (s.length+1), ∀ z, (row s z).getD o.val false = target z

-- The quantifiers defining Reach are finite, including the legal next gate.
def Reach {r : ℕ} : ℕ → List (Sig r) → Sig r → Prop
  | 0, s, target => Ends s target
  | k+1, s, target => Ends s target ∨ ∃ c : Code s.length,
      Legal c ∧ Reach k (extend s c) target

private def endsDec {r : ℕ} (s : List (Sig r)) (t : Sig r) : Decidable (Ends s t) := by
  unfold Ends
  infer_instance

private def legalDec {m : ℕ} (c : Code m) : Decidable (Legal c) := by
  unfold Legal
  split <;> infer_instance

-- A constructive finite search. A failed concrete check supplies the premise
-- of of_finite_exclusion. Large pools may instead use a proved pruning scheme.
def reachDec {r : ℕ} (k : ℕ) (s : List (Sig r)) (t : Sig r) : Decidable (Reach k s t) :=
  match k with
  | 0 => endsDec s t
  | k+1 =>
    letI : Decidable (Ends s t) := endsDec s t
    letI : ∀ c : Code s.length, Decidable (Legal c) := fun c => legalDec c
    letI : ∀ c : Code s.length, Decidable (Reach k (extend s c) t) :=
      fun c => reachDec k (extend s c) t
    inferInstanceAs (Decidable (Ends s t ∨
      ∃ c : Code s.length, Legal c ∧ Reach k (extend s c) t))

def search {r : ℕ} (k : ℕ) (s : List (Sig r)) (t : Sig r) : Bool :=
  @decide (Reach k s t) (reachDec k s t)

theorem search_false {r : ℕ} (k : ℕ) (s : List (Sig r)) (t : Sig r)
    (h : search k s t = false) : ¬ Reach k s t := by
  letI := reachDec k s t
  exact of_decide_eq_false h

private theorem stop {r : ℕ} (s : List (Sig r)) (o : ℕ) (t : Sig r)
    (h : ∀ z, (row s z).getD o false = t z) : Ends s t := by
  refine ⟨⟨min o s.length, by omega⟩, ?_⟩
  intro z
  change (row s z).getD (min o s.length) false = t z
  by_cases ho : o ≤ s.length
  · simpa only [min_eq_left ho] using h z
  · have hl : (row s z).length = s.length := by simp [row]
    rw [min_eq_right (by omega : s.length ≤ o)]
    have ht := h z
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (row s z).length ≤ o)] at ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (row s z).length ≤ s.length)]
    exact ht

-- The very same gate choice is used on every row. The circuit may contain
-- constants, junk gates, repeated or forward reads and an arbitrary output.
theorem raw_reaches {r : ℕ} (k : ℕ) (s : List (Sig r)) (t : Sig r) (D : Circuit)
    (hfan : FanInTwo D) (hsize : D.size ≤ k)
    (hrows : ∀ z, D.eval (row s z) = t z) : Reach k s t := by
  induction k generalizing s D with
  | zero =>
    obtain ⟨gs,o⟩ := D
    cases gs with
    | nil => exact stop s o t hrows
    | cons g tail =>
      change (g :: tail).length ≤ 0 at hsize
      simp only [List.length_cons] at hsize
      omega
  | succ k ih =>
    obtain ⟨gs,o⟩ := D
    cases gs with
    | nil => exact Or.inl (stop s o t hrows)
    | cons g tail =>
      let c := encodeGate s.length g
      refine Or.inr ⟨c, legal_encode _ _, ?_⟩
      apply ih (s := extend s c) (D := ⟨tail,o⟩)
      · intro u hu
        exact hfan u (List.mem_cons_of_mem g hu)
      · change (g :: tail).length ≤ k+1 at hsize
        change tail.length ≤ k
        simp only [List.length_cons] at hsize
        omega
      · intro z
        have hg := hfan g (by simp)
        rw [row_extend, show evalCode c (row s z) =
          g.op.eval (g.inputs.map fun i => (row s z).getD i false) from
            eval_encode _ _ _ (by simp [row]) hg.1 hg.2]
        exact hrows z

def initial {n r : ℕ} (xs : Fin r → Fin n → Bool) (head : (Fin n → Bool) → Bool) :
    List (Sig r) := (List.ofFn fun i : Fin n => fun z => xs z i) ++ [fun z => head (xs z)]

theorem row_initial {n r : ℕ} (xs : Fin r → Fin n → Bool) (head : (Fin n → Bool) → Bool) (z : Fin r) :
    row (initial xs head) z = List.ofFn (xs z) ++ [head (xs z)] := by
  simp [row, initial, List.map_ofFn, Function.comp_def]

theorem of_finite_exclusion {n r : ℕ} (k : ℕ) (xs : Fin r → Fin n → Bool)
    (head f : (Fin n → Bool) → Bool)
    (no : ¬ Reach k (initial xs head) (fun z => f (xs z))) :
    ∀ D : Circuit, FanInTwo D → D.size ≤ k →
      ∃ x, D.eval (List.ofFn x ++ [head x]) ≠ f x := by
  classical
  intro D hfan hs
  by_contra! agree
  apply no
  exact raw_reaches k (initial xs head) _ D hfan hs (fun z => by
    simpa only [row_initial] using agree (xs z))

-- Pool search merges histories which contain the same signatures. Supplying
-- both constants for free makes this an overapproximation suitable for exclusion.
def pool {r : ℕ} (s : List (Sig r)) : Finset (Sig r) :=
  insert (fun _ => true) (insert (fun _ => false) s.toFinset)

private theorem getD_pool {r : ℕ} (s : List (Sig r)) (i : ℕ) :
    s.getD i (fun _ => false) ∈ pool s := by
  induction s generalizing i with
  | nil => simp [pool, List.getD_eq_getElem?_getD]
  | cons a s ih =>
    cases i with
    | zero => simp [pool, List.getD_eq_getElem?_getD]
    | succ i =>
      have h := ih i
      simp only [pool, Finset.mem_insert, List.mem_toFinset] at h ⊢
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.mem_cons] using
        (show s.getD i (fun _ => false) = (fun _ => true) ∨
            s.getD i (fun _ => false) = (fun _ => false) ∨
            s.getD i (fun _ => false) = a ∨ s.getD i (fun _ => false) ∈ s from by tauto)

private theorem row_lookup {r : ℕ} (s : List (Sig r)) (i : ℕ) :
    (fun z => (row s z).getD i false) = s.getD i (fun _ => false) := by
  funext z
  simp only [row, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases s[i]? <;> rfl

private theorem pin_pool {r : ℕ} (s : List (Sig r)) (p : Pin s.length) (b : Bool) :
    (fun z => readPin (row s z) b p) ∈ pool s := by
  by_cases h : p.val = s.length + 1
  · cases b <;> simp [readPin, h, pool]
  · simp only [readPin, h, if_false, row_lookup]
    exact getD_pool s p.val

def pointOp {r : ℕ} (op : Fin 3) (a b : Sig r) : Sig r := fun z =>
  if op = 0 then a z && b z else if op = 1 then a z || b z else !(a z)

def PoolReach {r : ℕ} : ℕ → Finset (Sig r) → Sig r → Prop
  | 0, p, t => t ∈ p
  | k+1, p, t => t ∈ p ∨ ∃ (op : Fin 3) (a b : Sig r), a ∈ p ∧ b ∈ p ∧
      PoolReach k (insert (pointOp op a b) p) t

private theorem ends_pool {r : ℕ} (s : List (Sig r)) (t : Sig r) (h : Ends s t) :
    t ∈ pool s := by
  obtain ⟨o,ho⟩ := h
  rw [← funext ho, row_lookup]
  exact getD_pool s o.val

theorem reaches_pool {r : ℕ} (k : ℕ) (s : List (Sig r)) (t : Sig r) :
    Reach k s t → PoolReach k (pool s) t := by
  induction k generalizing s with
  | zero => exact ends_pool s t
  | succ k ih =>
    rintro (stopNow | ⟨c, _, rest⟩)
    · exact Or.inl (ends_pool s t stopNow)
    · let b := decide (c.1 = 0)
      let a₁ : Sig r := fun z => readPin (row s z) b c.2.1
      let a₂ : Sig r := fun z => readPin (row s z) b c.2.2
      refine Or.inr ⟨c.1,a₁,a₂,pin_pool s _ b,pin_pool s _ b,?_⟩
      have val : (fun z => evalCode c (row s z)) = pointOp c.1 a₁ a₂ := by
        funext z
        by_cases ha : c.1 = 0 <;> by_cases ho : c.1 = 1 <;>
          simp [evalCode, pointOp, a₁, a₂, b, ha, ho]
      have hp : pool (extend s c) = insert (pointOp c.1 a₁ a₂) (pool s) := by
        ext f
        simp [pool, extend, val, or_comm, or_left_comm, or_assoc]
      rw [← hp]
      exact ih _ rest

theorem of_pool_exclusion {n r : ℕ} (k : ℕ) (xs : Fin r → Fin n → Bool)
    (head f : (Fin n → Bool) → Bool)
    (no : ¬ PoolReach k (pool (initial xs head)) (fun z => f (xs z))) :
    ∀ D : Circuit, FanInTwo D → D.size ≤ k →
      ∃ x, D.eval (List.ofFn x ++ [head x]) ≠ f x := by
  apply of_finite_exclusion k xs head f
  intro h
  exact no (reaches_pool _ _ _ h)

end PEqualNP.Research.PetersenRaw
