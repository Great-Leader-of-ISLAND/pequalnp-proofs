import PEqualNP.CoPortBanks4482
namespace CoPortProbe4482
open CoPortBanks4482
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem first : verified 0 = true := by decide +kernel
theorem mid : verified 63 = true := by decide +kernel
#print axioms first
end CoPortProbe4482
