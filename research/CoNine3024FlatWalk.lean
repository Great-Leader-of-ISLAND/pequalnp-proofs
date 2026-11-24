import PEqualNP.CoNine3024FlatData
open CoNine3024 CoNine3024.Flat
set_option maxRecDepth 16384
set_option maxHeartbeats 0
example : search (geom 9) 10 s3=false := by decide +kernel
