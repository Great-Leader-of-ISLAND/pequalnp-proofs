import PEqualNP.Co4358TinyDirect
import PEqualNP.Co4358TinyFast
namespace CoNum4358.Direct
set_option maxRecDepth 65536
set_option maxHeartbeats 0
def tinyFastEntry (k i : Nat) : Bool :=
  let r := (tinyTable coins (k+1)).row i
  Tiny.Fast.node k r.1 (tinyTable coins k) r.2
theorem tinyF3 : CoAO3143.Memo.allAt (tinyFastEntry 2) 0 8=true := by decide +kernel
theorem tinyF7 : CoAO3143.Memo.allAt (tinyFastEntry 6) 0 8=true := by decide +kernel
theorem tinyF9 : CoAO3143.Memo.allAt (tinyFastEntry 8) 0 8=true := by decide +kernel
theorem tinyF11 : tinyFastEntry 10 0=true := by decide +kernel
end CoNum4358.Direct
