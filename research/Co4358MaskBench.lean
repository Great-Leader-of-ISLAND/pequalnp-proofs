import PEqualNP.Co4358TinyDirect
import PEqualNP.Co4358MaskFast
namespace CoNum4358.Direct
set_option maxRecDepth 65536
set_option maxHeartbeats 0
def maskEntry (k i : Nat) : Bool :=
  let r := (tinyTable coins (k+1)).row i
  Tiny.MaskFast.node k r.1 (tinyTable coins k) r.2
theorem bitsF3 : CoAO3143.Memo.allAt (maskEntry 2) 0 8=true := by decide +kernel
theorem bitsF7 : CoAO3143.Memo.allAt (maskEntry 6) 0 8=true := by decide +kernel
theorem bitsF9 : CoAO3143.Memo.allAt (maskEntry 8) 0 8=true := by decide +kernel
theorem bitsF11 : maskEntry 10 0=true := by decide +kernel
end CoNum4358.Direct
