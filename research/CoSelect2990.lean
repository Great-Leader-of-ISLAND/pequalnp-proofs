import Mathlib
import PEqualNP.Defs

namespace CoSelect2990
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def binary (g : Gate) : Prop :=
  (g.op=.and ∨ g.op=.or) ∧ ∃ i j, g.inputs=[i,j]

def choose (w : List Bool) (g : Gate) : Gate :=
  match g.op,g.inputs with
  | .and,[i,j] => ⟨.or,[if w.getD i false then j else i]⟩
  | _,_ => g

def selected : List Gate → List Bool → List Gate
  | [],_ => []
  | g::gs,w => choose w g :: selected gs (step w g)

def raises (a b : Bool) : Prop := a=true → b=true

private theorem get_raises {v w : List Bool} (h : List.Forall₂ raises v w) (i : Nat) :
    raises (v.getD i false) (w.getD i false) := by
  induction h generalizing i with
  | nil => exact fun eq => eq
  | cons h _ ih =>
    cases i with
    | zero => exact h
    | succ i => exact ih i

private theorem same_step (w : List Bool) (g : Gate) (hg : binary g) :
    step w (choose w g)=step w g := by
  obtain ⟨op,⟨i,j,pins⟩⟩ := hg
  obtain ⟨kind,ins⟩ := g
  change ins=[i,j] at pins
  subst ins
  rcases op with h|h <;> change kind=_ at h <;> subst kind
  · apply congrArg (fun b : Bool => w ++ [b])
    change (w.getD (if w.getD i false then j else i) false || false) =
      (w.getD i false && (w.getD j false && true))
    by_cases ha : w.getD i false=true
    · rw [if_pos ha,ha] <;> simp only [Bool.or_false,Bool.and_true,Bool.true_and]
    · rw [if_neg ha,Bool.eq_false_iff.mpr ha] <;> rfl
  · rfl

private theorem snoc {v w : List Bool} (h : List.Forall₂ raises v w) {a b : Bool} (ab : raises a b) :
    List.Forall₂ raises (v ++ [a]) (w ++ [b]) := by
  induction h with
  | nil => exact .cons ab .nil
  | cons e _ ih => exact .cons e ih

private theorem above_step (ref v w : List Bool) (g : Gate) (hg : binary g)
    (h : List.Forall₂ raises v w) : List.Forall₂ raises (step v g) (step w (choose ref g)) := by
  obtain ⟨op,⟨i,j,pins⟩⟩ := hg
  obtain ⟨kind,ins⟩ := g
  change ins=[i,j] at pins
  subst ins
  apply snoc h
  have a := get_raises h i
  have b := get_raises h j
  rcases op with eq|eq <;> change kind=_ at eq <;> subst kind
  · change raises (v.getD i false && (v.getD j false && true))
      (w.getD (if ref.getD i false then j else i) false || false)
    simp only [Bool.and_true,Bool.or_false,raises,Bool.and_eq_true]
    intro hit
    by_cases test : ref.getD i false=true
    · rw [if_pos test]
      exact b hit.2
    · rw [if_neg test]
      exact a hit.1
  · change raises (v.getD i false || (v.getD j false || false))
      (w.getD i false || (w.getD j false || false))
    simp only [raises,Bool.or_false,Bool.or_eq_true] at a b ⊢
    aesop

theorem equal_at (gs : List Gate) (ok : ∀g∈gs,binary g) (ref : List Bool) :
    (selected gs ref).foldl step ref=gs.foldl step ref := by
  induction gs generalizing ref with
  | nil => rfl
  | cons g gs ih =>
    simp only [selected,List.foldl_cons,same_step ref g (ok g (by simp))]
    exact ih (fun z hz => ok z (by simp [hz])) _

theorem raises_all (gs : List Gate) (ok : ∀g∈gs,binary g) (ref v w : List Bool)
    (h : List.Forall₂ raises v w) :
    List.Forall₂ raises (gs.foldl step v) ((selected gs ref).foldl step w) := by
  induction gs generalizing ref v w with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun z hz => ok z (by simp [hz])) _ _ _ (above_step ref v w g (ok g (by simp)) h)

def upper (C : Circuit) (ref : List Bool) : Circuit := ⟨selected C.gates ref,C.output⟩

private theorem selected_or (gs : List Gate) (ok : ∀g∈gs,binary g) (ref : List Bool) :
    ∀g∈selected gs ref,g.op=.or ∧ g.inputs.length≤2 := by
  induction gs generalizing ref with
  | nil => simp [selected]
  | cons g gs ih =>
    intro a ha
    rcases List.mem_cons.mp ha with eq|mem
    · subst a
      obtain ⟨op,⟨i,j,pins⟩⟩ := ok g (by simp)
      obtain ⟨kind,ins⟩ := g
      change ins=[i,j] at pins
      subst ins
      rcases op with eq|eq <;> change kind=_ at eq <;> subst kind <;> simp [choose]
    · exact ih (fun z hz => ok z (by simp [hz])) _ _ mem

theorem certificate (C : Circuit) (ok : ∀g∈C.gates,binary g) (ref : List Bool) :
    (∀g∈(upper C ref).gates,g.op=.or ∧ g.inputs.length≤2) ∧
    (upper C ref).eval ref=C.eval ref ∧
    ∀v, raises (C.eval v) ((upper C ref).eval v) := by
  refine ⟨selected_or C.gates ok ref,?_,?_⟩
  · exact congrArg (fun w : List Bool => w.getD C.output false) (equal_at C.gates ok ref)
  · intro v
    have rel : List.Forall₂ raises v v := by
      induction v with
      | nil => exact .nil
      | cons h t ih => exact .cons (fun e => e) ih
    exact get_raises (raises_all C.gates ok ref v v rel) C.output

#print axioms certificate
end CoSelect2990
