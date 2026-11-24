import PEqualNP.CoSafeCompiledBlock3456

/- The baseline formula and physical compiler are CoSafeBlock3456 and
CoSafeCompiledBlock3456. Here the repaired formula dominates the original
on the entire abstract cube; only the chosen rejection rows need exact agreement. -/
namespace CoNegativePorts5282
open CoSafePort3456 CoSafeFormula3456

variable {ι α ν : Type*}

theorem repair_dominates (kill : ι → Bool) (p : ι → Prop) (t : Tree ι) :
    holds p t → optHolds p (repair kill t) := by
  classical
  rw [repair,addBack_eval,eval_project]
  intro hold
  by_cases active : ∃ i ∈ selected kill t, p i
  · exact Or.inl active
  · exact Or.inr ((unchanged kill p t (fun i hi hit => active ⟨i,hi,hit⟩)).mp hold)

theorem normalize_from_negative_rows [Fintype ι] (ports : α → Set ι) (one : ν → α) (mark : ι → Prop)
    (raw : ∀ v i, i ∈ ports (one v) → ¬ mark i → ∀ y,
      i ∈ ports y → ports (one v) ⊆ ports y)
    (chain : ∀ v i j, i ∈ ports (one v) → j ∈ ports (one v) → mark i → mark j →
      ImpliesPort ports i j ∨ ImpliesPort ports j i) (t : Tree ι) :
    ∃ u : Tree ι, gates u ≤ gates t ∧
      (∀ x : α, holds (fun i => i ∈ ports x) u ↔ holds (fun i => i ∈ ports x) t) ∧
      (∀ v : ν, clean (fun i => i ∈ ports (one v)) u) ∧
      ∀ p : ι → Prop, holds p t → holds p u := by
  classical
  induction t with
  | leaf i => exact ⟨.leaf i, le_rfl, fun _ => Iff.rfl, (fun _ => trivial), (fun _ h => h)⟩
  | either a b ia ib =>
    obtain ⟨a',ca,ea,da,ua⟩ := ia
    obtain ⟨b',cb,eb,db,ub⟩ := ib
    refine ⟨.either a' b',?_,fun x => or_congr (ea x) (eb x),(fun v => ⟨da v,db v⟩), (fun p => Or.imp (ua p) (ub p))⟩
    simp only [gates]
    omega
  | both a b ia ib =>
    obtain ⟨a',ca,ea,da,ua⟩ := ia
    obtain ⟨b',cb,eb,db,ub⟩ := ib
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
    refine ⟨u,?_,?_,?_,?_⟩
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
    · intro p hp
      have easier : holds p s := ⟨ua p hp.1,ub p hp.2⟩
      have grew := repair_dominates kill p s easier
      rw [eq] at grew
      exact grew

open CoAO3143Restriction CoCompile3456 CoSafePhysical3456
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem compiled_on_negative_rows {ι α : Type*} [Fintype ι] {n} (bank : ι → Wire (Rows n))
    (row : α → Rows n) (sing : Fin n → α) (atOne : ∀ v, row (sing v) = one v)
    (mark : ι → Prop) (t : CoSafeFormula3456.Tree ι) {gs : List Gate}
    (well : good n gs) (dryBank : dry n gs) (paid : ∀ i, bank i ∈ symbolic n gs)
    (raw : ∀ v i, i ∈ active bank row (sing v) → ¬ mark i → ∀ y,
       i ∈ active bank row y → active bank row (sing v) ⊆ active bank row y)
    (chain : ∀ v i j, i ∈ active bank row (sing v) → j ∈ active bank row (sing v) →
      mark i → mark j →
        ImpliesPort (active bank row) i j ∨ ImpliesPort (active bank row) j i) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ dry n D.gates ∧
      D.size ≤ gs.length + gates t ∧
      (∀ x, circuitFun n D (row x) = true ↔ holds (fun i => bank i (row x) = true) t) ∧
      ∀ r, holds (fun i => bank i r = true) t → circuitFun n D r = true := by
  obtain ⟨u,budget,same,cleaned,grows⟩ :=
    normalize_from_negative_rows (active bank row) sing mark raw chain t
  have cleared : ∀ v : Fin n, clean (fun i => bank i (one v) = true) u := by
    intro v
    simpa [active,atOne v] using cleaned v
  obtain ⟨D,dm,dr,dd,ds,de⟩ := physical_formula bank u well dryBank paid cleared
  refine ⟨D,dm,dr,dd,by omega,?_,?_⟩
  · intro x
    rw [de]
    exact (value_iff bank u (row x)).trans (same x)
  · intro r hit
    rw [de]
    exact (value_iff bank u r).mpr (grows _ hit)

#print axioms compiled_on_negative_rows
#print axioms normalize_from_negative_rows
end CoNegativePorts5282
