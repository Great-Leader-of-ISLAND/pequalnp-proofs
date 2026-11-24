import PEqualNP.CoOnlyReadPhysical
import PEqualNP.CoRootless3825

namespace CoPortRows3825
open PEqualNP.CircuitLowerBounds CoOnlyReadPhysical CoRootless3825

private theorem other (front back : List Bool) (p q : Bool) (k : Nat) (ne : k≠front.length) :
    (front++p::back).getD k false=(front++q::back).getD k false := by
  induction front generalizing k with
  | nil => cases k <;> simp_all
  | cons a f ih =>
    cases k with
    | zero => rfl
    | succ j => exact ih j (fun e => ne (by simp [e]))

private theorem pivot (front back : List Bool) (p : Bool) :
    (front++p::back).getD front.length false=p := by
  induction front with
  | nil => rfl
  | cons a f ih => exact ih

/-- The value is the actual indexed companion after the full prefix, rather than
    an existential neutral witness. The prefix and suffix may use arbitrary gates. -/
theorem neutral_at (pre post : List Gate) (front rear : List Bool) (op : GateOp)
    (kind : op=.and ∨ op=.or) (otherPin out : Nat) (input : List Nat)
    (pins : input=[front.length,otherPin] ∨ input=[otherPin,front.length])
    (distinct : otherPin≠front.length) (elsewhere : out≠front.length)
    (before : ∀ g∈pre,front.length∉g.inputs) (later : ∀ g∈post,front.length∉g.inputs)
    (changes : (⟨pre++⟨op,input⟩::post,out⟩ : Circuit).eval (front++false::rear) ≠
      (⟨pre++⟨op,input⟩::post,out⟩ : Circuit).eval (front++true::rear)) :
    let b := (run pre (front++false::rear)).getD otherPin false
    (op=.and → b=true) ∧ (op=.or → b=false) := by
  classical
  obtain ⟨after,hpre⟩ := scanWithout pre front rear before
  let b := (front++false::after).getD otherPin false
  have pinval (p : Bool) : (front++p::after).getD otherPin false=b := other _ _ _ _ _ distinct
  let g : Gate := ⟨op,input⟩
  have read (p : Bool) : value g (front++p::after)=op.eval [p,b] := by
    rcases pins with i|i <;> rcases kind with t|t <;>
      simp only [value,g,i,t,List.map_cons,List.map_nil,pivot,pinval] <;>
      simp [GateOp.eval,Bool.and_comm,Bool.or_comm]
  have calcval (p : Bool) :
      (⟨pre++g::post,out⟩ : Circuit).eval (front++p::rear)=
      (run post (front++p::(after++[op.eval [p,b]]))).getD out false := by
    change (run (pre++g::post) (front++p::rear)).getD out false=_
    have eq : run (pre++g::post) (front++p::rear) =
        run post ((run pre (front++p::rear))++[value g (run pre (front++p::rear))]) := by
      simp [run,List.foldl_append]
    rw [eq,hpre,read]
    simp only [List.append_assoc,List.cons_append]
  have diff : op.eval [false,b]≠op.eval [true,b] := by
    intro e
    apply changes
    change (Circuit.mk (pre++g::post) out).eval _=_
    rw [calcval false,calcval true,e]
    obtain ⟨final,hpost⟩ := scanWithout post front (after++[op.eval [true,b]]) later
    rw [hpost false,hpost true]
    exact other _ _ _ _ _ elsewhere
  dsimp only
  rw [hpre false]
  change (op=.and → b=true) ∧ (op=.or → b=false)
  cases b <;> rcases kind with rfl|rfl <;> simp_all [GateOp.eval]

/-- The higher seven raw bits are in increasing physical wire order. -/
def row (v : Fin 2) (bit : Bool) (Y : Fin 128) (i : Fin 9) : Bool :=
  if i.val=v.val then bit else if i.val < 2 then true else Y.val.testBit (i.val-2)

def zeroRows (v : Fin 2) : List ℕ :=
  ((List.finRange 128).filter (fun Y => !graph (row v false Y))).map Fin.val

theorem table : zeroRows 0=[0,2,4,8,10,12,32,34,36,64,68,96,100] ∧
    zeroRows 1=[0,1,2,16,17,18,32,34,48,50,64,65,96] := by decide +kernel

theorem pair_fires (v : Fin 2) (Y : Fin 128) : graph (row v true Y)=true := by
  change decide _=true
  apply decide_eq_true
  refine ⟨0,1,by decide,?_,?_⟩ <;> fin_cases v <;> rfl

#print axioms neutral_at
#print axioms table
end CoPortRows3825
