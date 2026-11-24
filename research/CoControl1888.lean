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

def packRow (x : Vertex→Bool) : Row :=
  (BitVec.ofBoolListLE (List.ofFn x)).toFin.cast (by simp [List.length_ofFn])

theorem unpack (x : Vertex→Bool) : raw (packRow x)=x := by
  funext i
  change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

/- The star at 1 reuses the supplied disjunction. Its five companions cover
   the other Petersen edges. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem controls : ∀r : Row,candidate.eval (bank id (raw r))=target (raw r) := by decide +kernel

theorem correct (x : Vertex→Bool) : candidate.eval (bank id x)=target x := by
  simpa only [unpack] using controls (packRow x)

#print axioms CoControl1888.correct
end CoControl1888
