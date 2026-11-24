import PEqualNP.CoProbe3174

namespace CoComponents3174
open CoNine3024 CoNine3024.Canon CoProbe3174

set_option maxRecDepth 16384
set_option maxHeartbeats 0
example : (⟨6,#[0x50203]⟩ : Packed).read 0=3 := by decide +kernel
example : (chosen 5 [2,3,9])=[2,9] := by decide +kernel
example : ids 8 14 35=[2,3] := by decide +kernel
example : sort (fun a b : Nat => decide (a≤b)) [5,2,4]=[2,4,5] := by decide +kernel
example : (order (CoRoot3174.root 0 true)).wires.length=11 := by decide +kernel
example : (t13.state 0).spent=(CoRoot3174.root 0 true).spent := by decide +kernel
example : (t13.state 0).wires.length=11 := by decide +kernel
example : (t10.state 0).wires.length>0 := by decide +kernel

end CoComponents3174
