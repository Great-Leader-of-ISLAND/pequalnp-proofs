import PEqualNP.Co4358ColorSplit
namespace CoNum4358.Tiny.ShareGrid.Forest
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 30
theorem sample1 : shadePossible [1956,5700,7442,8715,22568,22829,24784]=false := by decide +kernel
theorem sample2 : shadePossible [6116,7442,8715,13903,18725,22568,24784]=false := by decide +kernel
theorem sample3 : shadePossible [208,1952,5700,7442,8715,18693,22568]=true := by decide +kernel
theorem sample4 : shadePossible [6116,7442,8715,13903,18693,22568,24816]=true := by decide +kernel
theorem sample5 : shadePossible [1952,5700,7442,8715,9739,18693,22568,24784]=false := by decide +kernel
theorem sample6 : shadePossible [1952,5700,7442,8715,18693,19717,22568,24784]=false := by decide +kernel
theorem sample7 : shadePossible [1952,5700,7442,8182,8715,18693,22568,24784]=true := by decide +kernel
theorem sample8 : shadePossible [5700,6116,7442,8715,18693,22568,24784,24816]=true := by decide +kernel
theorem sample9 : shadePossible [1024,1536,1952,5700,7442,8715,18693,22568,24784]=false := by decide +kernel
theorem sample10 : shadePossible [1536,1952,5700,7442,7954,8715,18693,22568,24784]=false := by decide +kernel
theorem sample11 : shadePossible [1952,5700,6116,7442,8022,8715,18693,22568,24784]=true := by decide +kernel
theorem sample12 : shadePossible [1952,5700,6116,7442,8114,8715,18693,22568,24784]=true := by decide +kernel
end CoNum4358.Tiny.ShareGrid.Forest
