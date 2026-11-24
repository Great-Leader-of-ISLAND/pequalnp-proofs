import PEqualNP.Co4358Buckets
namespace CoNum4358
set_option maxRecDepth 65000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000
theorem smoke_16and : firstRoot 1 6 false = false := by decide +kernel
#print axioms smoke_16and
end CoNum4358
