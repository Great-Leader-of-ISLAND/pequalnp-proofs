import PEqualNP.CoSafeFormula3456

namespace CoSafeFormula3456

variable {ι : Type*}

/-- Repeated occurrences are retained and pay for themselves. -/
def selected (kill : ι → Bool) : Tree ι → List ι
  | .leaf i => if kill i then [i] else []
  | .both a b | .either a b => selected kill a ++ selected kill b

theorem selected_length (kill : ι → Bool) (t : Tree ι) :
    (selected kill t).length = lost kill t := by
  induction t with
  | leaf i => cases hh : kill i <;> simp [selected,lost,hh]
  | both a b ia ib => simp [selected,lost,ia,ib]
  | either a b ia ib => simp [selected,lost,ia,ib]

theorem selected_kill (kill : ι → Bool) (t : Tree ι) (i : ι)
    (mem : i ∈ selected kill t) : kill i = true := by
  induction t with
  | leaf j =>
    cases h : kill j <;> simp [selected,h] at mem
    simpa [mem] using h
  | both a b ia ib =>
    rcases List.mem_append.mp mem with ha|hb
    · exact ia ha
    · exact ib hb
  | either a b ia ib =>
    rcases List.mem_append.mp mem with ha|hb
    · exact ia ha
    · exact ib hb

def addBack : List ι → Option (Tree ι) → Option (Tree ι)
  | [], t => t
  | i::ls, t => mergeOr (some (.leaf i)) (addBack ls t)

theorem addBack_eval (p : ι → Prop) (ls : List ι) (q : Option (Tree ι)) :
    optHolds p (addBack ls q) ↔ (∃ i ∈ ls, p i) ∨ optHolds p q := by
  induction ls with
  | nil => simp [addBack]
  | cons i ls ih =>
    change optHolds p (mergeOr (some (.leaf i)) (addBack ls q)) ↔ _
    rw [holds_or,ih]
    change (p i ∨ (∃ j ∈ ls, p j) ∨ optHolds p q) ↔ _
    constructor
    · rintro (hp | ⟨j,hj,hp⟩ | hq)
      · exact Or.inl ⟨i,by simp,hp⟩
      · exact Or.inl ⟨j,List.mem_cons_of_mem _ hj,hp⟩
      · exact Or.inr hq
    · rintro (⟨j,hj,hp⟩ | hq)
      · rcases List.mem_cons.mp hj with rfl | old
        · exact Or.inl hp
        · exact Or.inr (Or.inl ⟨j,old,hp⟩)
      · exact Or.inr (Or.inr hq)

theorem addBack_leaves (ls : List ι) (q : Option (Tree ι)) :
    optLeaves (addBack ls q) = ls.length + optLeaves q := by
  induction ls with
  | nil => simp [addBack]
  | cons i ls ih =>
    change optLeaves (mergeOr (some (.leaf i)) (addBack ls q)) = _
    rw [or_leaves,ih]
    change 1 + (ls.length + optLeaves q) = (ls.length + 1) + optLeaves q
    omega

theorem addBack_clean (p : ι → Prop) (ls : List ι) (q : Option (Tree ι))
    (cq : optClean p q) : optClean p (addBack ls q) := by
  induction ls with
  | nil => exact cq
  | cons i ls ih => exact or_clean p _ _ (by trivial) ih

/-- On a row with no active selected occurrence, freezing those inputs
    leaves every formula evaluation on the row unchanged. -/
theorem unchanged (kill : ι → Bool) (p : ι → Prop) (t : Tree ι)
    (noneOn : ∀ i ∈ selected kill t, ¬ p i) :
    holds p t ↔ holds (fun a => kill a = false ∧ p a) t := by
  induction t with
  | leaf i =>
    cases h : kill i
    · simp [holds,h]
    · have no := noneOn i (by simp [selected,h])
      simp [holds,h,no]
  | both a b ia ib =>
    exact and_congr (ia fun i hi => noneOn i (List.mem_append_left _ hi))
      (ib fun i hi => noneOn i (List.mem_append_right _ hi))
  | either a b ia ib =>
    exact or_congr (ia fun i hi => noneOn i (List.mem_append_left _ hi))
      (ib fun i hi => noneOn i (List.mem_append_right _ hi))

def repair (kill : ι → Bool) (t : Tree ι) : Option (Tree ι) :=
  addBack (selected kill t) (project kill t)

theorem repair_eval (kill : ι → Bool) (p : ι → Prop) (t : Tree ι)
    (safe : ∀ i, kill i = true → p i → holds p t) :
    optHolds p (repair kill t) ↔ holds p t := by
  classical
  rw [repair,addBack_eval,eval_project]
  constructor
  · rintro (⟨i,hi,hit⟩ | hp)
    · exact safe i (selected_kill kill t i hi) hit
    · have inc : ∀ i : ι, (kill i = false ∧ p i) → p i := fun _ h => h.2
      exact holds_mono inc t hp
  · intro hp
    by_cases active : ∃ i ∈ selected kill t, p i
    · exact Or.inl active
    · exact Or.inr ((unchanged kill p t (fun i hi hit => active ⟨i,hi,hit⟩)).1 hp)

theorem repair_budget (kill : ι → Bool) (t u : Tree ι)
    (eq : repair kill t = some u) : gates u ≤ gates t := by
  have ref := leaf_refund kill t
  have hh := addBack_leaves (selected kill t) (project kill t)
  change optLeaves (repair kill t) = _ at hh
  rw [eq,selected_length] at hh
  change leaves u = _ at hh
  have l : leaves u ≤ leaves t := by omega
  rw [leaf_gate u,leaf_gate t] at l
  omega

theorem repair_clean (kill : ι → Bool) (p : ι → Prop) (a b : Tree ι)
    (ha : clean p a) (hb : clean p b)
    (cleared : ¬ optHolds p (project kill (.both a b))) :
    optClean p (repair kill (.both a b)) :=
  addBack_clean p _ _ (repair_root kill p a b ha hb cleared)

end CoSafeFormula3456
