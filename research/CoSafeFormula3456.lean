import Mathlib

namespace CoSafeFormula3456

inductive Tree (ι : Type*) where
  | leaf : ι → Tree ι
  | both : Tree ι → Tree ι → Tree ι
  | either : Tree ι → Tree ι → Tree ι

variable {ι : Type*}

def holds (p : ι → Prop) : Tree ι → Prop
  | .leaf a => p a
  | .both a b => holds p a ∧ holds p b
  | .either a b => holds p a ∨ holds p b

def optHolds (p : ι → Prop) : Option (Tree ι) → Prop
  | none => False
  | some t => holds p t

def mergeAnd : Option (Tree ι) → Option (Tree ι) → Option (Tree ι)
  | some a, some b => some (.both a b)
  | _, _ => none

def mergeOr : Option (Tree ι) → Option (Tree ι) → Option (Tree ι)
  | some a, some b => some (.either a b)
  | some a, none => some a
  | none, b => b

theorem holds_and (p : ι → Prop) (a b : Option (Tree ι)) :
    optHolds p (mergeAnd a b) ↔ optHolds p a ∧ optHolds p b := by
  cases a <;> cases b <;> simp [mergeAnd,optHolds,holds]

theorem holds_or (p : ι → Prop) (a b : Option (Tree ι)) :
    optHolds p (mergeOr a b) ↔ optHolds p a ∨ optHolds p b := by
  cases a <;> cases b <;> simp [mergeOr,optHolds,holds]

def project (kill : ι → Bool) : Tree ι → Option (Tree ι)
  | .leaf a => if kill a then none else some (.leaf a)
  | .both a b => mergeAnd (project kill a) (project kill b)
  | .either a b => mergeOr (project kill a) (project kill b)

theorem eval_project (kill : ι → Bool) (p : ι → Prop) (t : Tree ι) :
    optHolds p (project kill t) ↔ holds (fun a => kill a = false ∧ p a) t := by
  induction t with
  | leaf a => cases hx : kill a <;> simp [project,optHolds,holds,hx]
  | both a b ia ib => simp only [project,holds_and,holds,ia,ib]
  | either a b ia ib => simp only [project,holds_or,holds,ia,ib]

def gates : Tree ι → Nat
  | .leaf _ => 0
  | .both a b | .either a b => gates a + gates b + 1

def leaves : Tree ι → Nat
  | .leaf _ => 1
  | .both a b | .either a b => leaves a + leaves b

def optLeaves : Option (Tree ι) → Nat
  | none => 0
  | some t => leaves t

def lost (kill : ι → Bool) : Tree ι → Nat
  | .leaf a => if kill a then 1 else 0
  | .both a b | .either a b => lost kill a + lost kill b

theorem leaf_gate (t : Tree ι) : leaves t = gates t + 1 := by
  induction t with
  | leaf a => rfl
  | both a b ia ib => simp only [leaves,gates,ia,ib]; omega
  | either a b ia ib => simp only [leaves,gates,ia,ib]; omega

theorem and_leaves (a b : Option (Tree ι)) :
    optLeaves (mergeAnd a b) ≤ optLeaves a + optLeaves b := by
  cases a <;> cases b <;> simp [optLeaves,mergeAnd,leaves]

theorem or_leaves (a b : Option (Tree ι)) :
    optLeaves (mergeOr a b) = optLeaves a + optLeaves b := by
  cases a <;> cases b <;> simp [optLeaves,mergeOr,leaves]

theorem leaf_refund (kill : ι → Bool) (t : Tree ι) :
    optLeaves (project kill t) + lost kill t ≤ leaves t := by
  induction t with
  | leaf a => cases hx : kill a <;> simp [project,optLeaves,lost,leaves,hx]
  | both a b ia ib =>
    have h := and_leaves (project kill a) (project kill b)
    simp only [project,lost,leaves]
    omega
  | either a b ia ib =>
    simp only [project,lost,leaves,or_leaves]
    omega

theorem gate_refund (kill : ι → Bool) (t u : Tree ι)
    (hu : project kill t = some u) :
    gates u + lost kill t ≤ gates t := by
  have h := leaf_refund kill t
  rw [hu] at h
  change leaves u + lost kill t ≤ leaves t at h
  rw [leaf_gate u,leaf_gate t] at h
  omega

/-- Every computed AND has value zero on this particular physical row. -/
def clean (p : ι → Prop) : Tree ι → Prop
  | .leaf _ => True
  | .both a b => clean p a ∧ clean p b ∧ ¬ (holds p a ∧ holds p b)
  | .either a b => clean p a ∧ clean p b

def optClean (p : ι → Prop) : Option (Tree ι) → Prop
  | none => True
  | some t => clean p t

theorem and_clean (p : ι → Prop) (a b : Option (Tree ι))
    (ca : optClean p a) (cb : optClean p b) (hz : ¬ (optHolds p a ∧ optHolds p b)) :
    optClean p (mergeAnd a b) := by
  cases a <;> cases b <;> simp_all [mergeAnd,optClean,optHolds,clean]

theorem or_clean (p : ι → Prop) (a b : Option (Tree ι))
    (ca : optClean p a) (cb : optClean p b) :
    optClean p (mergeOr a b) := by
  cases a <;> cases b <;> simp_all [mergeOr,optClean,clean]

theorem holds_mono {p q : ι → Prop} (inc : ∀ i, p i → q i)
    (t : Tree ι) : holds p t → holds q t := by
  induction t with
  | leaf i => exact inc i
  | both a b ia ib => exact fun h => ⟨ia h.1,ib h.2⟩
  | either a b ia ib => exact Or.imp ia ib

theorem project_clean (kill : ι → Bool) (p : ι → Prop) (t : Tree ι)
    (hc : clean p t) : optClean p (project kill t) := by
  induction t with
  | leaf i => cases hx : kill i <;> simp [optClean,project,clean,hx]
  | both a b ia ib =>
    obtain ⟨ha,hb,hz⟩ := hc
    apply and_clean p _ _ (ia ha) (ib hb)
    intro cab
    apply hz
    have inc : ∀ i : ι, (kill i = false ∧ p i) → p i := fun _ hx => hx.2
    exact ⟨holds_mono inc a ((eval_project kill p a).1 cab.1),
           holds_mono inc b ((eval_project kill p b).1 cab.2)⟩
  | either a b ia ib => exact or_clean p _ _ (ia hc.1) (ib hc.2)

/-- Given clean earlier subformulas, killing a dirty root on each singleton
    makes the residual formula clean before the top OR is reattached. -/
theorem repair_root (kill : ι → Bool) (p : ι → Prop) (a b : Tree ι)
    (ha : clean p a) (hb : clean p b)
    (cleared : ¬ optHolds p (project kill (.both a b))) :
    optClean p (project kill (.both a b)) := by
  apply and_clean p _ _ (project_clean kill p a ha) (project_clean kill p b hb)
  exact fun h => cleared ((holds_and p _ _).2 h)

end CoSafeFormula3456
