import PEqualNP.CoNine3024FlatData
open CoNine3024 CoNine3024.Flat
set_option maxRecDepth 16384
set_option maxHeartbeats 0
example : (children (geom 9) 12 s0)[0]?=some s1 := by decide +kernel
