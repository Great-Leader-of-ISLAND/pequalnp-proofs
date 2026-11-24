import PEqualNP.CoBlockIntervals4482
namespace CoMaskShape4482

def ofBits {k : Nat} (f : Fin k→Bool) : BitVec k :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem ofBits_at {k : Nat} (f : Fin k→Bool) (j : Fin k) :
    (ofBits f).getLsbD j.val=f j := by
  simp only [ofBits,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]

/-- At most h of the input columns are true. The bitwise computation
generates an entire mask, with no quantification over the 2^n slots. -/
def atMost {k : Nat} : List (BitVec k) → Nat → BitVec k
  | [],_ => BitVec.allOnes k
  | a::xs,0 => (~~~a) &&& atMost xs 0
  | a::xs,h+1 => ifTrue a (atMost xs h) (atMost xs (h+1))
where
  ifTrue (a y n : BitVec k) := (a &&& y) ||| ((~~~a) &&& n)

theorem atMost_get {k} (ws : List (BitVec k)) (j : Fin k) (h : Nat) :
    (atMost ws h).getLsbD j.val =
      decide ((ws.filter (fun a => a.getLsbD j.val)).length≤h) := by
  induction ws generalizing h with
  | nil => simp only [atMost,BitVec.getLsbD_allOnes,j.isLt,decide_true,
      List.filter_nil,List.length_nil,Nat.zero_le]
  | cons a xs ih =>
    cases h with
    | zero =>
      cases b : a.getLsbD j.val <;>
        simp [atMost,BitVec.getLsbD_and,BitVec.getLsbD_not,j.isLt,b,ih,List.filter_cons]
    | succ h =>
      cases b : a.getLsbD j.val <;>
        simp [atMost,atMost.ifTrue,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,
          j.isLt,b,ih,List.filter_cons]

end CoMaskShape4482
