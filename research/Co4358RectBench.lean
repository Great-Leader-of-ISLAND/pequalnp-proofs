import PEqualNP.Co4358RectBytes

namespace CoNum4358.RectCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem bench3 : CoAO3143.Memo.allAt (entryTest pkg 2) 0 8=true := by decide +kernel
theorem bench7 : CoAO3143.Memo.allAt (entryTest pkg 6) 0 8=true := by decide +kernel
theorem bench9 : CoAO3143.Memo.allAt (entryTest pkg 8) 0 8=true := by decide +kernel
theorem bench11 : entryTest pkg 10 0=true := by decide +kernel

end CoNum4358.RectCheck
