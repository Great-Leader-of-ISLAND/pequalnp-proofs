import PEqualNP.Co4358JumpBench
namespace CoNum4358.Tiny.FastJumpBench
open CoAO3143.Memo (allAt allAt_get)
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 50
def portion (g : Nat) (b : Fin 8) :=
  let i := (8*g+b.val)*16
  allAt (test 7) i (min 16 (772-i))
theorem batch0 (b : Fin 8) : portion 0 b=true := by fin_cases b <;> decide +kernel
theorem batch1 (b : Fin 8) : portion 1 b=true := by fin_cases b <;> decide +kernel
theorem batch2 (b : Fin 8) : portion 2 b=true := by fin_cases b <;> decide +kernel
theorem batch3 (b : Fin 8) : portion 3 b=true := by fin_cases b <;> decide +kernel
theorem batch4 (b : Fin 8) : portion 4 b=true := by fin_cases b <;> decide +kernel
theorem batch5 (b : Fin 8) : portion 5 b=true := by fin_cases b <;> decide +kernel
theorem batch6 (b : Fin 8) : portion 6 b=true := by fin_cases b <;> decide +kernel
theorem layer8_every (i : Nat) (bound : i<772) : test 7 i=true := by
  have all (g : Fin 7) (b : Fin 8) : portion g.val b=true := by
    fin_cases g
    · exact batch0 b
    · exact batch1 b
    · exact batch2 b
    · exact batch3 b
    · exact batch4 b
    · exact batch5 b
    · exact batch6 b
  let g : Fin 7 := ⟨i/16/8,by omega⟩
  let b : Fin 8 := ⟨i/16%8,Nat.mod_lt _ (by decide)⟩
  have eq : 8*g.val+b.val=i/16 := by dsimp [g,b]; omega
  have yes := all g b
  unfold portion at yes
  rw [eq] at yes
  exact allAt_get yes i (by omega) (by omega)
#print axioms layer8_every
end CoNum4358.Tiny.FastJumpBench
