import PEqualNP.CoBlockIntervals4482
namespace CoImplicitBlock4482
open CoBitBlock4482 CoBlockIntervals4482

/-- These functions only propose a row pair. The acceptance proof does
not require their arithmetic or search strategy to be correct. -/
def least {n : Nat} (w : BitVec n) : Nat := (w &&& (-w)).toNat.log2
def pickRow (w : Bits) : Row := ⟨least w % 258,Nat.mod_lt _ (by decide)⟩

def findPair : List Mark → Bits → Bits → Option (Row×Row)
  | [],p,n => if p=0 ∨ n=0 then none else some (pickRow p,pickRow n)
  | w::ws,p,n =>
    if p=0 ∨ n=0 then none else
      match findPair ws (p &&& ~~~w.1) n with
      | some r => some r
      | none => findPair ws (p &&& w.1) (n &&& w.2)

def propose {k} (cols : List (Col k)) (j : Nat) : Option (Row×Row) :=
  let inside := (cols.filter fun c => c.inc.getLsbD j).map Col.data
  let es := cols.foldr (fun c v => if c.inc.getLsbD j then v else avoid c.data v)
    (BitVec.allOnes 258)
  findPair inside es es

/-- In each round select one candidate group, propose a witness pair,
and remove *only* the actual interval excluded by that witness. -/
def check {k} (cols : List (Col k)) : Nat → BitVec k → Bool
  | 0,m => m==0
  | fuel+1,m =>
    if m=0 then true else
    match propose cols (least m) with
    | none => false
    | some (r,s) => check cols fuel (m &&& ~~~(interval r s cols))

theorem check_sound {k} (cols : List (Col k)) (fuel : Nat) (m : BitVec k)
    (h : check cols fuel m=true) : ∃ pairs : List (Row×Row), m &&& cover cols pairs=m := by
  induction fuel generalizing m with
  | zero =>
    have off : m=0 := beq_iff_eq.mp h
    exact ⟨[],by simp [off]⟩
  | succ fuel ih =>
    by_cases off : m=0
    · exact ⟨[],by simp [off]⟩
    cases guess : propose cols (least m) with
    | none => simp only [check,if_neg off,guess,Bool.false_eq_true] at h
    | some rs =>
      obtain ⟨r,s⟩ := rs
      simp only [check,if_neg off,guess] at h
      obtain ⟨pairs,covered⟩ := ih _ h
      refine ⟨(r,s)::pairs,?_⟩
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      have old := congrArg (fun v : BitVec k => v.getLsbD j) covered
      simp only [cover,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,
        hj,decide_true,Bool.true_and] at old ⊢
      cases v : m.getLsbD j <;> cases t : (interval r s cols).getLsbD j <;>
        cases p : (cover cols pairs).getLsbD j <;> simp_all

#print axioms check_sound
end CoImplicitBlock4482
