import PEqualNP.CoSafePort3456
import PEqualNP.CoSafeReattach3456

namespace CoSafeFormula3456

open CoSafePort3456

variable {ι α ν : Type*}

theorem holds_zero (t : Tree ι) : ¬ holds (fun _ => False) t := by
  induction t with
  | leaf => simp [holds]
  | both a b ia ib => simp [holds,ia]
  | either a b ia ib => simp [holds,ia,ib]

theorem untouched (kill : ι → Bool) (t : Tree ι)
    (s : selected kill t = []) : project kill t = some t := by
  induction t with
  | leaf i => cases h : kill i <;> simp_all [project,selected]
  | both a b ia ib =>
    have hh : selected kill a = [] ∧ selected kill b = [] := by simpa [selected] using s
    simp [project,ia hh.1,ib hh.2,mergeAnd]
  | either a b ia ib =>
    have hh : selected kill a = [] ∧ selected kill b = [] := by simpa [selected] using s
    simp [project,ia hh.1,ib hh.2,mergeOr]

theorem repair_present (kill : ι → Bool) (t : Tree ι) :
    ∃ u, repair kill t = some u := by
  cases e : selected kill t with
  | nil => exact ⟨t,by simp [repair,e,addBack,untouched kill t e]⟩
  | cons a as' =>
    simp only [repair,e,addBack]
    cases addBack as' (project kill t) <;> simp [mergeOr]

/-- The care-row sort is arbitrary. A non-marked active source dominates all
    inputs of that singleton on any physical row where it is activated. The
    marked sources firing together on a singleton form an implication chain. -/
theorem normalize_block [Fintype ι] (ports : α → Set ι) (one : ν → α) (mark : ι → Prop)
    (raw : ∀ v i, i ∈ ports (one v) → ¬ mark i → ∀ y,
      i ∈ ports y → ports (one v) ⊆ ports y)
    (chain : ∀ v i j, i ∈ ports (one v) → j ∈ ports (one v) → mark i → mark j →
      ImpliesPort ports i j ∨ ImpliesPort ports j i) (t : Tree ι) :
    ∃ u : Tree ι, gates u ≤ gates t ∧
      (∀ x : α, holds (fun i => i ∈ ports x) u ↔ holds (fun i => i ∈ ports x) t) ∧
      ∀ v : ν, clean (fun i => i ∈ ports (one v)) u := by
  classical
  induction t with
  | leaf i => exact ⟨.leaf i, le_rfl, fun _ => Iff.rfl, fun _ => trivial⟩
  | either a b ia ib =>
    obtain ⟨a',ca,ea,da⟩ := ia
    obtain ⟨b',cb,eb,db⟩ := ib
    refine ⟨.either a' b',?_,fun x => or_congr (ea x) (eb x),fun v => ⟨da v,db v⟩⟩
    simp only [gates]
    omega
  | both a b ia ib =>
    obtain ⟨a',ca,ea,da⟩ := ia
    obtain ⟨b',cb,eb,db⟩ := ib
    let s : Tree ι := .both a' b'
    let H : Set ι → Prop := fun q => holds (fun i => i ∈ q) s
    let kill : ι → Bool := fun i => decide (Safe H ports i)
    have mono : ∀ {A B : Set ι}, A ⊆ B → H A → H B :=
      fun {_ _} inc => holds_mono (fun _ hi => inc hi) s
    have zero : ¬ H ∅ := holds_zero s
    have safe (i : ι) (h : kill i = true) : Safe H ports i := of_decide_eq_true h
    have extinct (v : ν) : ¬ optHolds (fun i => i ∈ ports (one v)) (project kill s) := by
      intro hh
      have masked := (eval_project kill (fun i => i ∈ ports (one v)) s).1 hh
      let U := ports (one v) \ {i | Safe H ports i}
      have hu : H U := by
        apply holds_mono (p := fun i => kill i = false ∧ i ∈ ports (one v)) _ s masked
        intro i hi
        exact ⟨hi.2,by simpa [kill] using hi.1⟩
      have orig : H (ports (one v)) := mono (A := U) (B := ports (one v))
        (fun _ hi => hi.1) hu
      have marked (i : ι) (hi : i ∈ U) : mark i := by
        by_contra h
        exact hi.2 (fun y hy => mono (A := ports (one v)) (B := ports y)
          (raw v i hi.1 h y hy) orig)
      apply cleared_chain H ports mono zero (one v) _ hu
      intro i hi j hj
      exact chain v i j hi.1 hj.1 (marked i hi) (marked j hj)
    obtain ⟨u,eq⟩ := repair_present kill s
    refine ⟨u,?_,?_,?_⟩
    · have lim := repair_budget kill s u eq
      change gates u ≤ gates a' + gates b' + 1 at lim
      change gates u ≤ gates a + gates b + 1
      omega
    · intro x
      have ev := repair_eval kill (fun i => i ∈ ports x) s (fun i hi hx => safe i hi x hx)
      rw [eq] at ev
      exact ev.trans (and_congr (ea x) (eb x))
    · intro v
      have dry := repair_clean kill (fun i => i ∈ ports (one v)) a' b'
        (da v) (db v) (extinct v)
      change optClean _ (repair kill s) at dry
      rw [eq] at dry
      exact dry

end CoSafeFormula3456
