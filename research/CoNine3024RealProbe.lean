import PEqualNP.CoNine3024Probe
open CoNine3024
set_option maxRecDepth 16384
set_option maxHeartbeats 0
example : probe 9 true [0,0,0]=true := by decide +kernel
