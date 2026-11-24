import Mathlib

namespace CoFormula1963Protocol

/-- A binary monotone formula over raw coordinates. -/
inductive Expr (ι : Type*) where
  | atom (i : ι)
  | conj (a b : Expr ι)
  | disj (a b : Expr ι)

def Expr.eval {ι : Type*} (x : ι → Bool) : Expr ι → Bool
  | .atom i => x i
  | .conj a b => a.eval x && b.eval x
  | .disj a b => a.eval x || b.eval x

def Expr.leaves {ι : Type*} : Expr ι → ℕ
  | .atom _ => 1
  | .conj a b | .disj a b => a.leaves + b.leaves

structure Rect (ι α β : Type*) where
  label : ι
  rows : Finset α
  cols : Finset β

variable {ι α β : Type*} [DecidableEq α] [DecidableEq β]

/-- OR chooses a true child on the positive row. AND chooses a false child
    on the negative column. A fixed choice on ties makes the cells disjoint. -/
def partition (xp : α → ι → Bool) (xn : β → ι → Bool) :
    Expr ι → Finset α → Finset β → List (Rect ι α β)
  | .atom i, R, C => [⟨i,R,C⟩]
  | .conj a b, R, C =>
    partition xp xn a R (C.filter fun j => a.eval (xn j) = false) ++
    partition xp xn b R (C.filter fun j => a.eval (xn j) = true)
  | .disj a b, R, C =>
    partition xp xn a (R.filter fun i => a.eval (xp i) = true) C ++
    partition xp xn b (R.filter fun i => a.eval (xp i) = false) C

variable (xp : α → ι → Bool) (xn : β → ι → Bool)

theorem partition_length (t : Expr ι) (R : Finset α) (C : Finset β) :
    (partition xp xn t R C).length = t.leaves := by
  induction t generalizing R C with
  | atom => rfl
  | conj a b ia ib => simp [partition,Expr.leaves,ia,ib]
  | disj a b ia ib => simp [partition,Expr.leaves,ia,ib]

def hits (i : α) (j : β) (r : Rect ι α β) : ℕ :=
  if i ∈ r.rows ∧ j ∈ r.cols then 1 else 0

def multiplicity (i : α) (j : β) (rs : List (Rect ι α β)) : ℕ :=
  (rs.map (hits i j)).sum

theorem multiplicity_append (i : α) (j : β) (a b : List (Rect ι α β)) :
    multiplicity i j (a ++ b) = multiplicity i j a + multiplicity i j b := by
  simp [multiplicity]

theorem partition_exact (t : Expr ι) (R : Finset α) (C : Finset β) (i : α) (j : β) :
    multiplicity i j (partition xp xn t R C) = if i∈R ∧ j∈C then 1 else 0 := by
  induction t generalizing R C with
  | atom => simp [partition,multiplicity,hits]
  | conj a b ia ib =>
    simp only [partition,multiplicity_append,ia,ib,Finset.mem_filter]
    by_cases hr : i∈R <;> by_cases hc : j∈C <;> cases e : a.eval (xn j) <;> simp [hr,hc,e]
  | disj a b ia ib =>
    simp only [partition,multiplicity_append,ia,ib,Finset.mem_filter]
    by_cases hr : i∈R <;> by_cases hc : j∈C <;> cases e : a.eval (xp i) <;> simp [hr,hc,e]

/-- Every rectangle carries a real 1-to-0 coordinate. Empty rectangles are
    allowed and consume one leaf, so they never weaken a leaf lower bound. -/
theorem partition_sound (t : Expr ι) (R : Finset α) (C : Finset β)
    (hp : ∀ i ∈ R, t.eval (xp i) = true) (hn : ∀ j ∈ C, t.eval (xn j) = false) :
    ∀ r ∈ partition xp xn t R C, ∀ i ∈ r.rows, ∀ j ∈ r.cols,
      xp i r.label = true ∧ xn j r.label = false := by
  induction t generalizing R C with
  | atom v =>
    intro r h i hi j hj
    simp only [partition,List.mem_singleton] at h
    subst r
    exact ⟨hp i hi, hn j hj⟩
  | conj a b ia ib =>
    intro r h
    rcases List.mem_append.mp h with h | h
    · apply ia _ _ (fun i hi => ?_) (fun j hj => (Finset.mem_filter.mp hj).2) r h
      have both : a.eval (xp i) = true ∧ b.eval (xp i) = true := by
        simpa only [Expr.eval,Bool.and_eq_true] using hp i hi
      exact both.1
    · apply ib _ _ (fun i hi => ?_) (fun j hj => ?_) r h
      · have both : a.eval (xp i) = true ∧ b.eval (xp i) = true := by
          simpa only [Expr.eval,Bool.and_eq_true] using hp i hi
        exact both.2
      · obtain ⟨memC,he⟩ := Finset.mem_filter.mp hj
        simpa [Expr.eval,he] using hn j memC
  | disj a b ia ib =>
    intro r h
    rcases List.mem_append.mp h with h | h
    · apply ia _ _ (fun i hi => (Finset.mem_filter.mp hi).2) (fun j hj => ?_) r h
      have hh := hn j hj
      cases ha : a.eval (xn j) <;> simp_all [Expr.eval]
    · apply ib _ _ (fun i hi => ?_) (fun j hj => ?_) r h
      · obtain ⟨memR,he⟩ := Finset.mem_filter.mp hi
        simpa [Expr.eval,he] using hp i memR
      · have hh := hn j hj
        cases hb : b.eval (xn j) <;> simp_all [Expr.eval]

#print axioms partition_exact
#print axioms partition_sound
end CoFormula1963Protocol
