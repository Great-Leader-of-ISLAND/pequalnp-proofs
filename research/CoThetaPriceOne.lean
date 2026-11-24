import PEqualNP.CoPaid3143

namespace CoPriceTest
open CoNatBench CoThetaSeven
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block0 (b : Fin 38) : permitBlock 5 0 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
#print axioms block0
end CoPriceTest
