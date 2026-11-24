import PEqualNP.CoSelect2990

namespace CoUnions2990
open PEqualNP.CircuitLowerBounds CoSelect2990
variable {I : Type} [DecidableEq I]

noncomputable section
def fires (row : I → Bool) (A : Finset I) : Bool := A.toList.any row

private theorem fires_iff (row : I → Bool) (A : Finset I) :
    fires row A=true ↔ ∃ i∈A,row i=true := by
  simp [fires,List.any_eq_true]

private theorem fires_union (row : I → Bool) (A B : Finset I) :
    fires row (A ∪ B) = (fires row A || fires row B) := by
  apply Bool.eq_iff_iff.mpr
  simp only [fires_iff,Bool.or_eq_true,Finset.mem_union]
  aesop

private theorem lookup (row : I → Bool) (w : List (Finset I)) (j : Nat) :
    (w.map (fires row)).getD j false = fires row (w.getD j ∅) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => simp [fires]
  | some a => rfl

def operands (w : List (Finset I)) : List Nat → Finset I
  | [] => ∅
  | i::is => w.getD i ∅ ∪ operands w is

private theorem operand_bits (row : I → Bool) (w : List (Finset I)) (is : List Nat) :
    fires row (operands w is) = GateOp.or.eval (is.map fun j => (w.map (fires row)).getD j false) := by
  induction is with
  | nil => simp [operands,fires,GateOp.eval]
  | cons i is ih =>
    rw [operands,fires_union,ih,←lookup]
    rfl

def supports : List Gate → List (Finset I) → List (Finset I)
  | [],w => w
  | g::gs,w => supports gs (w ++ [operands w g.inputs])

private theorem support_bits (gs : List Gate) (row : I → Bool) (w : List (Finset I))
    (ors : ∀g∈gs,g.op=.or) :
    (supports gs w).map (fires row) = gs.foldl step (w.map (fires row)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [supports,ih _ (fun a ha => ors a (by simp [ha]))]
    simp only [List.foldl_cons,step,List.map_append,List.map_singleton,ors g (by simp),operand_bits]

theorem point_support (C : Circuit) (ok : ∀g∈C.gates,binary g) (ref : List Bool)
    (raw : List (Finset I)) : ∃ S : Finset I, ∀ row : I → Bool,
    (upper C ref).eval (raw.map (fires row))=fires row S := by
  let D := upper C ref
  refine ⟨(supports D.gates raw).getD D.output ∅,?_⟩
  intro row
  have ors (g) (hg : g∈D.gates) := ((certificate C ok ref).1 g hg).1
  have eq := support_bits D.gates row raw ors
  change (D.gates.foldl step (raw.map (fires row))).getD D.output false=_
  rw [←eq,lookup]

/-- The extra coordinate is a fixed true line. All other line inputs
can be represented by the empty support in the preceding theorem. -/
def fixedRow {P : Type} [DecidableEq P] (X : Finset P) : Option P → Bool
  | none => true
  | some p => decide (p∈X)

theorem recover {P : Type} [Fintype P] [DecidableEq P]
    (neighbors : Finset P) (S : Finset (Option P))
    (negative : fires (fixedRow (Finset.univ \ neighbors)) S=false)
    (positive : ∀p∈neighbors,fires (fixedRow {p}) S=true) :
    S=neighbors.image some := by
  classical
  have impossible {i : Option P} (hi : i∈S) (on : fixedRow (Finset.univ \ neighbors) i=true) : False := by
    have hit := (fires_iff _ _).2 ⟨i,hi,on⟩
    rw [negative] at hit
    contradiction
  have noConst : none∉S := fun h => impossible h rfl
  ext i
  cases i with
  | none => simpa using noConst
  | some p =>
    simp only [Finset.mem_image,Option.some.injEq,exists_eq_right]
    constructor
    · intro hp
      by_contra notIn
      exact impossible hp (by simp [fixedRow,notIn])
    · intro hp
      obtain ⟨j,hj,on⟩ := (fires_iff _ _).1 (positive p hp)
      cases j with
      | none => exact (noConst hj).elim
      | some y =>
        have yp : y=p := by simpa [fixedRow] using on
        simpa [yp] using hj

#print axioms point_support
#print axioms recover
end
end CoUnions2990
