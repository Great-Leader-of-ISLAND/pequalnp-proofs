import PEqualNP.Co4358DirectData
namespace CoNum4358.Direct
set_option maxHeartbeats 0
set_option maxRecDepth 65536
theorem missedLocation : place coins 6 0 [514,3328,91208,119072,139448,299089,361092]=1064 := by decide +kernel
theorem presentLocation : place coins 8 1 [24578,31234,91208,119072,139448,299089,361092,396564]=1515 := by decide +kernel
end CoNum4358.Direct
