import PEqualNP.CoFormula1963Targets

namespace CoUnfold1963
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoFormula1963Ledger CoFormula1963Circuit CoFormula1963Geometry CoFormula1963Link

def amount (n : Nat) (gs : List Gate) : List Nat :=
  gs.foldl (fun w g => w ++ [1 + readCost w g.inputs]) (List.replicate n 0)

private theorem extend_pair {as bs : List Nat} (h : List.Forall₂ (· ≤ ·) as bs)
    {a b : Nat} (p : a≤b) : List.Forall₂ (· ≤ ·) (as++[a]) (bs++[b]) := by
  induction h with
  | nil => exact .cons p .nil
  | cons e _ ih => exact .cons e ih

private theorem entry {as bs : List Nat} (h : List.Forall₂ (· ≤ ·) as bs) (j : Nat) :
    as.getD j 0 ≤ bs.getD j 0 := by
  induction h generalizing j with
  | nil => exact Nat.le_refl _
  | cons head _ ih => cases j with
    | zero => exact head
    | succ i => exact ih i

private theorem operands {as bs : List Nat} (h : List.Forall₂ (· ≤ ·) as bs) (ids : List Nat) :
    readCost as ids ≤ readCost bs ids := by
  induction ids with
  | nil => exact Nat.le_refl _
  | cons i is ih => exact Nat.add_le_add (entry h i) ih

private theorem tracks {n gs w} (h : Trace n gs w) :
    List.Forall₂ (· ≤ ·) w (amount n gs) := by
  induction h with
  | start =>
    change List.Forall₂ (· ≤ ·) (List.replicate n 0) (List.replicate n 0)
    induction n with
    | zero => exact .nil
    | succ n ih => exact .cons (Nat.le_refl 0) ih
  | step prev g z cap ih =>
    change List.Forall₂ _ _ (( _ ++ [g]).foldl _ _)
    rw [List.foldl_append]
    apply extend_pair ih
    exact cap.trans (Nat.add_le_add_left (operands ih g.inputs) 1)

theorem unfold_lower (C : Circuit) (mono : Monotone2 C)
    (posOK : ∀ e : E, C.eval (input (pos e))=true)
    (negOK : ∀ y : CoFormula1963Link.Y, C.eval (input (neg y))=false) :
    64 ≤ (amount 26 C.gates).getD C.output 0 := by
  let t := (run C.gates initial).getD C.output (.fixed false)
  have sem (x) : val x t = C.eval (input x) := value_of_output C mono x
  have cap := entry (tracks (run_costs C.gates)) C.output
  rw [cost_get] at cap
  change cost t ≤ _ at cap
  cases eq : t with
  | fixed b =>
    let e : E := ⟨(0,0),by decide⟩
    let y : CoFormula1963Link.Y := (0,0)
    have u := (sem (pos e)).trans (posOK e)
    have v := (sem (neg y)).trans (negOK y)
    simp only [eq,val] at u v
    exact Bool.noConfusion (u.symm.trans v)
  | tree f =>
    have yes (e) := (sem (pos e)).trans (posOK e)
    have no (y) := (sem (neg y)).trans (negOK y)
    simp only [eq,val] at yes no
    have bound := CoFormula1963Complete.leaves65 f yes no
    rw [eq] at cap
    change f.leaves-1 ≤ _ at cap
    omega

theorem solved_premise : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → x2 C → 64 ≤ ((C.gates.foldl (fun (w : List ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [1 + (g.inputs.map (fun i => w.getD i 0)).sum]) (List.replicate 26 0)).getD C.output 0) := by
  intro C mono tests
  apply unfold_lower C mono
  · intro e
    exact tests.1 e.val.1 e.val.2 e.property
  · intro y
    obtain ⟨q,_⟩ := samples y.1 y.2
    rw [CoFormula1963Targets.input1963]
    exact tests.2 (quad y.1 y.2) q.1 q.2

#print axioms solved_premise

#print axioms unfold_lower
end CoUnfold1963
