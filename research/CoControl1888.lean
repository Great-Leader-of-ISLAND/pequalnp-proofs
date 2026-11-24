import PEqualNP.CoRaw1888
namespace CoControl1888
open CoRaw1888 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def candidate : Circuit := ⟨[
  ⟨.or,[10,6]⟩,
  ⟨.and,[1,11]⟩,
  ⟨.or,[2,8]⟩,
  ⟨.or,[13,4]⟩,
  ⟨.and,[3,14]⟩,
  ⟨.or,[0,9]⟩,
  ⟨.and,[4,16]⟩,
  ⟨.or,[0,8]⟩,
  ⟨.or,[18,7]⟩,
  ⟨.and,[5,19]⟩,
  ⟨.or,[8,9]⟩,
  ⟨.and,[6,21]⟩,
  ⟨.or,[2,9]⟩,
  ⟨.and,[7,23]⟩,
  ⟨.or,[12,15]⟩,
  ⟨.or,[25,17]⟩,
  ⟨.or,[26,20]⟩,
  ⟨.or,[27,22]⟩,
  ⟨.or,[28,24]⟩],29⟩

theorem size : candidate.size=19 := by decide

theorem legal : FanInTwo candidate := by
  intro g hg
  simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

private theorem distribute (a b c : Bool) : a && (b || c)=(a && b)||(a && c) := by
  cases a <;> cases b <;> cases c <;> rfl

/- The star at 1 reuses the supplied disjunction. Its five companions cover
    the other Petersen edges. -/
set_option maxRecDepth 8192 in
theorem correct (x : Vertex→Bool) : candidate.eval (bank id x)=target x := by
  change ((((((x 1 && (((x 0 || x 2) || (x 6 || false)) && true)) || ((x 3 && (((x 2 || (x 8 || false)) || (x 4 || false)) && true)) || false)) || ((x 4 && ((x 0 || (x 9 || false)) && true)) || false)) || ((x 5 && (((x 0 || (x 8 || false)) || (x 7 || false)) && true)) || false)) || ((x 6 && ((x 8 || (x 9 || false)) && true)) || false)) || ((x 7 && ((x 2 || (x 9 || false)) && true)) || false))=target x
  simp only [Bool.and_true,Bool.or_false,target,distribute]
  ac_rfl

#print axioms CoControl1888.correct
end CoControl1888
