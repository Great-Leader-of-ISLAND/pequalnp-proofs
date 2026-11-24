import PEqualNP.CoFrontier3024Price
import PEqualNP.CoAllRaw3024

namespace CoFrontier3024Seed
open CoThetaNine CoThetaFreeCore CoAO3143Restriction CoFrontier3024Price

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def fee (lift : SmallInput→Input) : Nat :=
  if Constant (cut lift (vtx 0)) ∨ Constant (cut lift (vtx 2)) then 0 else 1

/-- The physical seed and its free negation are supplied by a single binary gate.
    Fixing either endpoint to a constant makes even this one gate unnecessary. -/
theorem initial (lift : SmallInput→Input) (p : Fin 11)
    (raw : ∀ i : Fin 9,norm 0 (cut lift (vtx i))∈vertices7) :
    ∃ ys, Free vertices7 (fee lift) ys ∧
      ∀ i : Fin 13,norm 0 (cut lift (CoAllRaw3024.label p i))∈ys := by
  let a := cut lift (vtx 0)
  let b := cut lift (vtx 2)
  have prefix : ∃ ys, Free vertices7 (fee lift) ys ∧ (∀ w∈vertices7,w∈ys) ∧
      norm 0 (cut lift CoAllRaw3024.seed)∈ys := by
    by_cases hc : Constant a ∨ Constant b
    · refine ⟨vertices7,?_,fun _ hw => hw,?_⟩
      · rw [show fee lift=0 from if_pos hc]
        exact Free.start
      · exact free_step Free.start (raw 0) (raw 2) (collapsed true a b hc)
    · rw [show fee lift=1 from if_neg hc]
      exact paid_step Free.start true (raw 0) (raw 2)
  obtain ⟨ys,prog,keep,seed⟩ := prefix
  have raw' (i : Fin 9) := keep _ (raw i)
  have cn (v : Bool) : norm 0 (cut lift (con v))∈ys := by cases v <;> exact keep _ List.mem_cons_self
  have inv : norm 0 (cut lift (CoAllRaw3024.inverse p))∈ys := by
    unfold CoAllRaw3024.inverse
    split
    · exact neg_known (raw' _)
    · split
      · exact neg_known seed
      · exact cn true
  refine ⟨ys,prog,fun i => ?_⟩
  unfold CoAllRaw3024.label
  split
  · exact raw' _
  · split
    · exact seed
    · split
      · exact inv
      · exact cn _


theorem raw_nine (j i : Fin 9) : norm 0 (cut (CoThetaCuts3024.plant j) (vtx i))∈vertices7 := by
  let w := cut (CoThetaCuts3024.plant j) (vtx i)
  have hold : w∈vertices7 := CoThetaCuts3024.known j (vtx i)
    (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  have z : w 0=false := by
    change vtx i (CoThetaCuts3024.plant j 0)=false
    rw [CoThetaCuts3024.column]
    cases CoThetaCuts3024.coordinate j i <;> simp [raw7]
  have eqn : norm 0 w=w := by funext r; simp [CoThetaFreeCore.norm,phase,z]
  change norm 0 w∈vertices7
  rw [eqn]
  exact hold

theorem nine_initial (j : Fin 9) (p : Fin 11) :
    ∃ ys,Free vertices7 (fee (CoThetaCuts3024.plant j)) ys ∧
      ∀ i : Fin 13,norm 0 (cut (CoThetaCuts3024.plant j) (CoAllRaw3024.label p i))∈ys :=
  initial _ p (raw_nine j)

#print axioms CoFrontier3024Seed.nine_initial

end
end CoFrontier3024Seed
