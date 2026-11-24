import PEqualNP.CoNine3024Budget
import PEqualNP.CoNine3024Data
import PEqualNP.CoThetaCuts3024
import PEqualNP.CoAO3143Restriction

namespace CoNine3024FixedMap
open CoNine3024 CoNine3024Budget CoThetaNine CoAO3143Restriction

def maskWord (j : Fin 9) : Truth := sliceWords.getD j.val 0

theorem mask_table : List.ofFn maskWord = sliceWords := by decide +kernel

def read (a : Truth) : Wire Input := fun r => a.getLsbD r.val

/-- Recover the seven coordinates retained by the corresponding theta cut. -/
def pull (j : Fin 9) (x : Input) : SmallInput :=
  let v := (List.ofFn (fun i : Fin 7 =>
    if vtx (CoThetaCuts3024.embedding j i) x then (1:Nat) <<< i.val else 0)).sum
  ⟨v%128,Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
theorem contained : ∀ (j : Fin 9) (r : SmallInput),
    (maskWord j).getLsbD (CoThetaCuts3024.plant j r).val=true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem recovers (j : Fin 9) : ∀ x : Input, (maskWord j).getLsbD x.val=true →
    CoThetaCuts3024.plant j (pull j x)=x := by
  fin_cases j <;> decide +kernel

private theorem zero_constant (a : Truth) (j : Fin 9) (z : a &&& maskWord j=0) :
    cut (CoThetaCuts3024.plant j) (read a) = con false := by
  funext r
  have e := congrArg (fun v : Truth => v.getLsbD (CoThetaCuts3024.plant j r).val) z
  simpa [cut,read,con,BitVec.getLsbD_and,contained j r] using e

private theorem one_constant (a : Truth) (j : Fin 9) (z : a &&& maskWord j=maskWord j) :
    cut (CoThetaCuts3024.plant j) (read a) = con true := by
  funext r
  have e := congrArg (fun v : Truth => v.getLsbD (CoThetaCuts3024.plant j r).val) z
  simpa [cut,read,con,BitVec.getLsbD_and,contained j r] using e

/-- The finite mask detects exactly those wires that become constant on the
    geometric theta restriction. All 128 actual rows of each slice are used. -/
theorem flag_constant (a : Truth) (j : Fin 9) :
    flag maskWord a j=1 ↔ Constant (cut (CoThetaCuts3024.plant j) (read a)) := by
  constructor
  · intro fl
    unfold flag at fl
    split at fl
    · rename_i choice
      rcases choice with h|h
      · exact ⟨false,zero_constant a j h⟩
      · exact ⟨true,one_constant a j h⟩
    · contradiction
  · rintro ⟨b,constant⟩
    have uniform (x : Input) (inside : (maskWord j).getLsbD x.val=true) : a.getLsbD x.val=b := by
      have h := congrFun constant (pull j x)
      change a.getLsbD (CoThetaCuts3024.plant j (pull j x)).val=b at h
      rw [recovers j x inside] at h
      exact h
    have formula : a &&& maskWord j = (if b then maskWord j else 0) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      let x : Input := ⟨i,hi⟩
      have fact := uniform x
      change (maskWord j).getLsbD i=true → a.getLsbD i=b at fact
      cases e : (maskWord j).getLsbD i with
      | false => cases b <;> simp [BitVec.getLsbD_and,e]
      | true => have h := fact e; cases b <;> simp [BitVec.getLsbD_and,e,h]
    cases b with
    | false =>
      have h : a &&& maskWord j=0 := by simpa using formula
      simp [flag,h]
    | true =>
      have h : a &&& maskWord j=maskWord j := by simpa using formula
      simp [flag,h]

end CoNine3024FixedMap
