import PEqualNP.Co4358ColorTable
namespace CoNum4358.Tiny.Splice
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 30
theorem layer7row : entry 6 0=true := by decide +kernel
theorem layer8row : entry 7 0=true := by decide +kernel
theorem layer9row : entry 8 0=true := by decide +kernel
theorem rootRow : entry 10 0=true := by decide +kernel
end CoNum4358.Tiny.Splice
