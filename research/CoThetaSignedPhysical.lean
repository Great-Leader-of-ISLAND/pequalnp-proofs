import PEqualNP.CoThetaPackedFinal
import PEqualNP.CoThetaWholeOrbit

namespace CoThetaWholeBase
open PEqualNP.CircuitLowerBounds

/-- All seven possible supplied input complements are covered. -/
theorem no_supplied_theta (j : Fin 7) : NoSignedTail j :=
  all_heads_from CertifiedData.lower_0 CertifiedData.lower_2 CertifiedData.lower_3 j

/-- A physical circuit whose first gate evaluates to an input complement
    on every row needs at least twelve gates for this theta graph. -/
theorem theta_first_complement_twelve (j : Fin 7) (g : Gate) (gs : List Gate) (o : Nat)
    (hfan : PEqualNP.MetaComplexity.FanInTwo ⟨g::gs,o⟩)
    (head : ∀ x : Fin 7 → Bool,
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = !(x j))
    (heval : ∀ x : Fin 7 → Bool, (Circuit.mk (g::gs) o).eval (List.ofFn x)=theta x) :
    12 ≤ (Circuit.mk (g::gs) o).size := by
  by_contra h
  exact physical_of_signed_tail j (no_supplied_theta j) g gs o hfan (by omega) head heval
end CoThetaWholeBase
