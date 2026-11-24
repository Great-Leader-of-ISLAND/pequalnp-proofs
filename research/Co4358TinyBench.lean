import PEqualNP.Co4358TinyDirect
namespace CoNum4358.Direct
set_option maxRecDepth 65536
set_option maxHeartbeats 0
theorem tiny3 : CoAO3143.Memo.allAt (tinyEntry 2) 0 8=true := by decide +kernel
theorem tiny7 : CoAO3143.Memo.allAt (tinyEntry 6) 0 8=true := by decide +kernel
theorem tiny9 : CoAO3143.Memo.allAt (tinyEntry 8) 0 8=true := by decide +kernel
theorem tiny11 : tinyEntry 10 0=true := by decide +kernel
end CoNum4358.Direct
