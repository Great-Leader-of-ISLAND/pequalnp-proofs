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
  have ready : ∃ ys, Free vertices7 (fee lift) ys ∧ (∀ w∈vertices7,w∈ys) ∧
      norm 0 (cut lift CoAllRaw3024.seed)∈ys := by
    by_cases hc : Constant a ∨ Constant b
    · refine ⟨vertices7,?_,fun _ hw => hw,?_⟩
      · rw [show fee lift=0 from if_pos hc]
        exact Free.start
      · exact free_step Free.start (raw 0) (raw 2) (collapsed true a b hc)
    · rw [show fee lift=1 from if_neg hc]
      exact paid_step Free.start true (raw 0) (raw 2)
  obtain ⟨ys,prog,keep,seed⟩ := ready
  have raw' (i : Fin 9) : norm 0 (cut lift (vtx i))∈ys := keep _ (raw i)
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

/-- A projected step costs one except when a constant operand saves it. This
    version accepts the two arithmetic indicator digits directly. -/
theorem advance {h ys} (pre : Free vertices7 h ys) (d : Bool) (a b : Wire SmallInput)
    (ha : norm 0 a∈ys) (hb : norm 0 b∈ys) (x y : Nat)
    (bx : x≤1) (by' : y≤1) (ax : x=1 ↔ Constant a) (ay : y=1 ↔ Constant b) :
    ∃ n ws, Free vertices7 n ws ∧ n+max x y=h+1 ∧
      (∀ w∈ys,w∈ws) ∧ norm 0 (op d a b)∈ws := by
  by_cases hc : Constant a ∨ Constant b
  · have one : max x y=1 := by
      rcases hc with t|t
      · have e := ax.mpr t
        omega
      · have e := ay.mpr t
        omega
    refine ⟨h,ys,pre,by omega,fun _ hw => hw,?_⟩
    exact free_step pre ha hb (collapsed d a b hc)
  · have zero : max x y=0 := by
      have nx : x≠1 := fun e => hc (Or.inl (ax.mp e))
      have ny : y≠1 := fun e => hc (Or.inr (ay.mp e))
      omega
    obtain ⟨ws,paid,keep,z⟩ := paid_step pre d ha hb
    exact ⟨h+1,ws,paid,by omega,keep,z⟩

theorem available_three (lower : SignedLower) (j : Fin 9) {k S} (tail : Cone ans k S)
    {h pool} (pre : Free vertices7 h pool)
    (hold : ∀ w∈S,norm 0 (cut (CoThetaCuts3024.plant j) w)∈pool)
    (spent : Nat) (total : h+spent+k≤14) : spent+losses (CoThetaCuts3024.plant j) S≤3 := by
  have needed := nine_signed lower j tail pre hold
  omega


#print axioms CoFrontier3024Seed.nine_initial

end
end CoFrontier3024Seed
