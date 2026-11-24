import PEqualNP.CoFormula1963Circuit

namespace CoFormula1963Targets
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoFormula1963Geometry CoFormula1963Link CoFormula1963Circuit CoFormula1963Ledger

/-- The exact two test clauses in 1963 suffice for the physical no-fanout
    bound. The remaining official hypotheses only narrow that target. -/
theorem sample1963 (C : Circuit) (mono : Monotone2 C) (one : noShare 26 C.gates)
    (positive : ∀ p l : V, p-l ∈ D → C.eval
      ((List.ofFn fun v : V => decide (v=p)) ++ List.ofFn fun v : V => decide (v=l)) = true)
    (negative : ∀ P : Finset V, P.card=4 → (∀ l : V, (P.filter fun p => p-l ∈ D).card ≤ 2) →
      C.eval ((List.ofFn fun p : V => decide (p∈P)) ++
        List.ofFn fun l : V => decide (∀ p∈P, p-l ∉ D)) = false) : 64 ≤ C.size := by
  apply no_shared_64 C mono one
  · intro e
    exact positive e.val.1 e.val.2 e.property
  · intro y
    obtain ⟨q,_⟩ := samples y.1 y.2
    exact negative _ q.1 q.2

def incA (p l : V) : Prop := ∃ d ∈ D, p = l+d
instance (p l : V) : Decidable (incA p l) := by unfold incA; infer_instance

def genericA (P : Finset V) : Prop :=
  (∀ v : V, v∉P → ∃ l : V, (∀ p∈P,¬incA p l) ∧ incA v l) ∧
  (¬ ∃ l : V, ∀ p∈P, incA p l) ∧
  ¬ ∃ v : V, ∀ l : V, (∀ p∈P,¬incA p l) → incA v l

def rowP (p l : V) (k : Fin 26) := decide (k=Fin.castAdd 13 p ∨ k=Fin.natAdd 13 l)

def rowN (P : Finset V) (k : Fin 26) := decide
  ((∃ p∈P, k=Fin.castAdd 13 p) ∨ ∃ l : V,k=Fin.natAdd 13 l ∧ ∀ p∈P, ¬incA p l)

theorem indices : ∀ a b : V,
    (Fin.castAdd 13 a = Fin.castAdd 13 b ↔ a=b) ∧
    (Fin.natAdd 13 a = Fin.natAdd 13 b ↔ a=b) ∧ Fin.castAdd 13 a ≠ Fin.natAdd 13 b ∧
    Fin.natAdd 13 a ≠ Fin.castAdd 13 b := by decide +kernel

theorem pos_input (e : E) : input (pos e) = List.ofFn (rowP e.val.1 e.val.2) := by
  unfold input
  rw [← List.ofFn_fin_append]
  congr 1
  funext k
  refine Fin.addCases (fun p => ?_) (fun l => ?_) k
  · simp [pos,rowP,Fin.append_left,(indices _ _).1,(indices _ _).2.2.1]
  · simp [pos,rowP,Fin.append_right,(indices _ _).2.1,(indices _ _).2.2.2]

theorem neg_input (y : Y) : input (neg y) = List.ofFn (rowN (quad y.1 y.2)) := by
  unfold input
  rw [← List.ofFn_fin_append]
  congr 1
  funext k
  refine Fin.addCases (fun p => ?_) (fun l => ?_) k
  · simp [neg,rowN,Fin.append_left,(indices _ _).1,(indices _ _).2.2.1]
  · simp [neg,rowN,Fin.append_right,(indices _ _).2.1,(indices _ _).2.2.2,
      incA,←inc_add,clear]

/-- A physical 1681 witness, if one exists, must reuse at least one genuine
    internal wire. The positive/negative quantifiers and the generic tests
    have exactly the additive incidence convention of that task. -/
theorem sample1681 (C : Circuit) (mono : Monotone2 C) (one : noShare 26 C.gates)
    (positive : ∀ p l : V, incA p l → circuitFun 26 C (rowP p l) = true)
    (negative : ∀ P : Finset V, genericA P → circuitFun 26 C (rowN P) = false) : 64 ≤ C.size := by
  apply no_shared_64 C mono one
  · intro e
    rw [pos_input]
    exact positive e.val.1 e.val.2 ((inc_add _ _).mp e.property)
  · intro y
    rw [neg_input]
    apply negative
    simpa [genericA,generic,clear,incA,←inc_add] using (samples y.1 y.2).2

#print axioms sample1963
#print axioms sample1681
end CoFormula1963Targets
