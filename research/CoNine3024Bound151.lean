import PEqualNP.CoNine3024Split

namespace CoNine3024
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def first (p : Fin 11) (seed : Bool) (i : Nat) := indexed (geom p) 12 (root p seed) i

theorem split6Y_0 : search (geom 6) 12 (first 6 true 0)=false := by
  apply exclude_children _ _ _ 11 (by decide +kernel) (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

end CoNine3024
