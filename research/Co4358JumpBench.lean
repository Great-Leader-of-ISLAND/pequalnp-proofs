import PEqualNP.Co4358ColorGround
import PEqualNP.Co4358BicolorBaseWords
import PEqualNP.Co4358PerfectJumps
namespace CoNum4358.Tiny.FastJumpBench
open CoNum4358.WordRows
set_option maxRecDepth 65536
set_option maxHeartbeats 0
def row (k i : Nat) := let r := WordRows.row (BicolorBase.tier k) i; (r.1,r.2.map read)
def fastTable (parent i k : Nat) : Table :=
  ⟨(BicolorBase.tier k).total,row k,fun q ws => FastJump.lookup (FastJump.tier parent) i (Splice.stamp q ws)⟩
def test (k i : Nat) :=
  let r := row (k+1) i
  MaskFast.nodeWith Splice.post k r.1 (fastTable (k+1) i k) r.2
set_option profiler true
set_option profiler.threshold 25
theorem k7 : test 6 0=true := by decide +kernel
theorem k8 : test 7 0=true := by decide +kernel
theorem k9 : test 8 0=true := by decide +kernel
theorem k11 : test 10 0=true := by decide +kernel
end CoNum4358.Tiny.FastJumpBench
