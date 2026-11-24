import PEqualNP.CoNine3024PairProgram
import PEqualNP.CoNine3024FlatData
open CoNine3024 CoNine3024PairGuard
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem pair_probe : guardSearch (keep 9) (geom 9) 10 CoNine3024.Flat.s3=false := by decide +kernel
