import PEqualNP.Co4358RectBench
namespace CoNum4358.RectCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 0
theorem middleRates : CoAO3143.Memo.allAt (entryTest pkg 6) 8 48 &&
    CoAO3143.Memo.allAt (entryTest pkg 7) 0 64 &&
    CoAO3143.Memo.allAt (entryTest pkg 8) 8 16 = true := by decide +kernel
#print axioms middleRates
end CoNum4358.RectCheck
