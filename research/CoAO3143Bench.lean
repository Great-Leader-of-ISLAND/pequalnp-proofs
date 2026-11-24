import PEqualNP.CoAO3143Bridge

namespace CoAO3143
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
theorem bridge_smoke : search 9 0 base1 = false := by decide +kernel
#print axioms CoAO3143.ao_lower_of_checks
#print axioms CoAO3143.bridge_smoke
end CoAO3143
