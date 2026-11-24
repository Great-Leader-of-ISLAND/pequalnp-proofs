import PEqualNP.Co4358IntCorners
namespace CoNum4358.NumericTimer
open Direct (coins getTier row place)
open CoAO3143.Memo (allAt)
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option profiler true
set_option profiler.threshold 30

def sample (k j : Nat) :=
  let count := (getTier coins (k+1)).count
  ((2*j+1)*count)/64

def literal (k j : Nat) :=
  let i := sample k j
  let r := row coins (k+1) i
  place coins (k+1) r.1 r.2==i

theorem literal7 : allAt (literal 6) 0 32=true := by decide +kernel
theorem literal8 : allAt (literal 7) 0 32=true := by decide +kernel

def finite (k j : Nat) := IntCornerGround.Fast.entry k (sample k j)

theorem genuine7 : allAt (finite 6) 0 32=true := by decide +kernel
theorem genuine8 : allAt (finite 7) 0 32=true := by decide +kernel

end CoNum4358.NumericTimer
