import PEqualNP.CoFormula1963Circuit

namespace CoFormula1963Targets
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoFormula1963Geometry CoFormula1963Link CoFormula1963Circuit CoFormula1963Ledger

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem decisions {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    decide P = decide Q := by
  by_cases p : P
  · rw [decide_eq_true p,decide_eq_true (h.mp p)]
  · rw [decide_eq_false p,decide_eq_false (fun q => p (h.mpr q))]

private theorem raw_clear (P : Finset V) (l : V) :
    decide (clear P l) = decide (∀ p ∈ P, p-l ∉ D) := decisions Iff.rfl

private theorem input1963 (y : Y) : input (neg y) =
    (List.ofFn fun p : V => decide (p∈quad y.1 y.2)) ++
    List.ofFn fun l : V => decide (∀ p∈quad y.1 y.2,p-l ∉ D) := by
  unfold input
  apply congrArg₂ List.append
  · rfl
  · apply congrArg List.ofFn
    funext l
    exact raw_clear _ _

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
    rw [input1963]
    exact negative (quad y.1 y.2) q.1 q.2

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

private theorem left_eq (a b : V) : Fin.castAdd 13 a = Fin.castAdd 13 b ↔ a=b := (indices a b).1
private theorem right_eq (a b : V) : Fin.natAdd 13 a = Fin.natAdd 13 b ↔ a=b := (indices a b).2.1
private theorem left_ne (a b : V) : Fin.castAdd 13 a ≠ Fin.natAdd 13 b := (indices a b).2.2.1
private theorem right_ne (a b : V) : Fin.natAdd 13 a ≠ Fin.castAdd 13 b := (indices a b).2.2.2

private theorem positive_arrays : ∀ p l : V,
    (List.ofFn fun z : V => decide (z=p)) ++ (List.ofFn fun z : V => decide (z=l)) =
      List.ofFn (rowP p l) := by
  intro p
  fin_cases p <;> decide +kernel

theorem pos_input (e : E) : input (pos e) = List.ofFn (rowP e.val.1 e.val.2) :=
  positive_arrays e.val.1 e.val.2

private theorem negative_left (P : Finset V) (a : V) :
    rowN P (Fin.castAdd 13 a) = decide (a∈P) := by
  unfold rowN
  apply decisions
  constructor
  · rintro (⟨p,hp,eq⟩ | ⟨l,eq,_⟩)
    · have ap : a=p := (left_eq a p).mp eq
      simpa only [ap] using hp
    · exact (left_ne a l eq).elim
  · intro ha
    exact Or.inl ⟨a,ha,rfl⟩

private theorem negative_right (P : Finset V) (a : V) :
    rowN P (Fin.natAdd 13 a) = decide (clear P a) := by
  unfold rowN
  apply decisions
  constructor
  · rintro (⟨p,_,eq⟩ | ⟨l,eq,c⟩)
    · exact (right_ne a p eq).elim
    · have al : a=l := (right_eq a l).mp eq
      subst l
      exact fun p hp h => c p hp ((inc_add p a).mp h)
  · intro h
    exact Or.inr ⟨a,rfl,fun p hp z => h p hp ((inc_add p a).mpr z)⟩

theorem neg_input (y : Y) : input (neg y) = List.ofFn (rowN (quad y.1 y.2)) := by
  unfold input
  rw [← List.ofFn_fin_append]
  apply congrArg List.ofFn
  funext k
  refine Fin.addCases (fun p => ?_) (fun l => ?_) k
  · rw [Fin.append_left]
    exact (negative_left _ p).symm
  · rw [Fin.append_right]
    exact (negative_right _ l).symm

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
