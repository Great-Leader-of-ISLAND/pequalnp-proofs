import PEqualNP.CoNine3024Bound17
import PEqualNP.CoNine3024Bound50
import PEqualNP.CoNine3024Bound151

namespace CoNine3024
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def first (p : Fin 11) (seed : Bool) (i : Nat) := indexed (geom p) 12 (root p seed) i

theorem split6Y_1 : search (geom 6) 12 (first 6 true 1)=false := by
  apply exclude_children _ _ _ 11 (by decide +kernel) (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

theorem split6Y_2 : search (geom 6) 12 (first 6 true 2)=false := by
  apply exclude_children _ _ _ 12 (by decide +kernel) (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

theorem split6Y_5 : search (geom 6) 12 (first 6 true 5)=false := by
  apply exclude_children _ _ _ 4 (by decide +kernel) (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

theorem split6Y_6 : search (geom 6) 12 (first 6 true 6)=false := by
  apply exclude_children _ _ _ 7 (by decide +kernel) (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

theorem split6Y_7 : search (geom 6) 12 (first 6 true 7)=false := by
  apply exclude_children _ _ _ 5 (by decide +kernel) (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

theorem split6Y_8 : search (geom 6) 12 (first 6 true 8)=false := by
  apply exclude_children _ _ _ 11 (by decide +kernel) (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

theorem exclude6Y : search (geom 6) 13 (root 6 true)=false := by
  apply exclude_children _ _ _ 9 (by decide +kernel) (by decide +kernel)
  intro i
  fin_cases i
  · exact split6Y_0
  · exact split6Y_1
  · exact split6Y_2
  · exact split6Y_3
  · exact split6Y_4
  · exact split6Y_5
  · exact split6Y_6
  · exact split6Y_7
  · exact split6Y_8

end CoNine3024
