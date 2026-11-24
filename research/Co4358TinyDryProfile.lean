import PEqualNP.Co4358TinyDryFast
namespace CoNum4358.Dry
set_option maxRecDepth 65536
set_option maxHeartbeats 0
def sampleK (k j : Nat) := (let n := (Direct.getTier Direct.coins (k+1)).count; ((2*j+1)*n)/32)
def probeIndex (k j : Nat) : Bool :=
  let t := table (k+1)
  let i := sampleK k j
  let r := t.row i
  t.loc r.1 r.2 == i

theorem lookupOnly : ∀j : Fin 16, probeIndex 6 j.val && probeIndex 7 j.val := by
  decide +kernel
theorem uniform7 (j : Fin 16) : Fast.entry 6 (sampleK 6 j.val)=true := by
  fin_cases j <;> decide +kernel
theorem uniform8 (j : Fin 16) : Fast.entry 7 (sampleK 7 j.val)=true := by
  fin_cases j <;> decide +kernel
end CoNum4358.Dry
