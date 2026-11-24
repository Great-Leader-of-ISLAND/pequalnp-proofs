import PEqualNP.CoNonredundant3825
import PEqualNP.CoOnlyReadPhysical

namespace CoLive3825
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoNonredundant3825
open CoOnlyReadPhysical

private theorem length_run (gs : List Gate) (xs : List Bool) : (run gs xs).length=xs.length+gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons g t ih =>
    change (run t (xs++[value g xs])).length=_
    rw [ih]
    simp
    omega

private theorem other_read (front back : List Bool) (p q : Bool) (k : ℕ)
    (different : k≠front.length) :
    (front++p::back).getD k false=(front++q::back).getD k false := by
  induction front generalizing k with
  | nil => cases k <;> simp_all
  | cons a f ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k (fun h => different (by simp [h]))

private theorem at_pivot (front back : List Bool) (p : Bool) :
    (front++p::back).getD front.length false=p := by
  induction front with
  | nil => rfl
  | cons a f ih => exact ih

def zeroGate : Gate := ⟨.or,[]⟩

theorem used_or_output (n out : ℕ) (pre tail : List Gate) (g : Gate)
    (minimum : IsMinimalCircuit n ⟨pre++g::tail,out⟩)
    (nc : nonconstant n ⟨pre++g::tail,out⟩) :
    out=n+pre.length ∨ ∃ h∈tail,n+pre.length∈h.inputs := by
  classical
  by_contra! nope
  let C : Circuit := ⟨pre++g::tail,out⟩
  let D : Circuit := ⟨pre++zeroGate::tail,out⟩
  have dfan : FanInTwo D := by
    intro h hh
    change h∈pre++zeroGate::tail at hh
    rcases List.mem_append.mp hh with left|rt
    · exact minimum.1 h (by change h∈pre++g::tail; simp [left])
    · rcases List.mem_cons.mp rt with eq|old
      · subst h
        simp [zeroGate]
      · exact minimum.1 h (by change h∈pre++g::tail; simp [old])
  have sample (x : Fin n → Bool) :
      wire n D out x=wire n C out x ∧ wire n D (n+pre.length) x=false := by
    let front := run pre (List.ofFn x)
    have len : front.length=n+pre.length := by simp [front,length_run]
    obtain ⟨post,after⟩ := scanWithout tail front []
      (fun h hh => by rw [len]; exact nope.2 h hh)
    have before (z : Gate) : (Circuit.mk (pre++z::tail) out).wires (List.ofFn x)=
        run tail (front++[value z front]) := by
      simp [Circuit.wires,front,run,value,List.foldl_append]
    have cd : C.wires (List.ofFn x)=front++value g front::post := (before g).trans (after _)
    have dd : D.wires (List.ofFn x)=front++false::post := (before zeroGate).trans (after false)
    change (D.wires _).getD out false=(C.wires _).getD out false ∧ (D.wires _).getD _ false=false
    rw [cd,dd,←len]
    exact ⟨other_read _ _ _ _ _ (fun e => nope.1 (e.trans len)),at_pivot _ _ _⟩
  have same : circuitFun n D=circuitFun n C := funext fun y => (sample y).1
  have sizeeq : C.size=D.size := by simp [C,D,Circuit.size]
  have mind : IsMinimalCircuit n D := ⟨dfan,fun E he eq =>
    sizeeq.symm.le.trans (minimum.2 E he (eq.trans same))⟩
  have nd : nonconstant n D := fun b h => nc b (fun y => ((sample y).1).symm.trans (h y))
  have pos : pre.length < D.gates.length := by simp [D] <;> omega
  exact no_alias_or_constant mind nd pos (Or.inl ⟨false,fun x => (sample x).2⟩)

end CoLive3825
