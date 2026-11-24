import PEqualNP.Co4358TinyDry
namespace CoNum4358.Dry
set_option maxHeartbeats 0
set_option maxRecDepth 65536
theorem p3 : CoAO3143.Memo.allAt (entry 2) 0 8=true := by decide +kernel
theorem p7 : CoAO3143.Memo.allAt (entry 6) 0 8=true := by decide +kernel
theorem p9 : CoAO3143.Memo.allAt (entry 8) 0 8=true := by decide +kernel
theorem p11 : entry 10 0=true := by decide +kernel
end CoNum4358.Dry
