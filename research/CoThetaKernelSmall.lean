import PEqualNP.CoThetaFast

/- Concrete computational exclusions.  For four remaining inversions every
   representative is checked with the positive head literal dropped. -/
namespace CoThetaFast

def droppedHead (j : Fin 7) := (raw j).erase (col j)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem test0four : Impossible 10 4 (droppedHead 0) :=
  exclude_search (by decide +kernel) (by decide +kernel)
theorem test2four : Impossible 10 4 (droppedHead 2) :=
  exclude_search (by decide +kernel) (by decide +kernel)
theorem test3four : Impossible 10 4 (droppedHead 3) :=
  exclude_search (by decide +kernel) (by decide +kernel)

end CoThetaFast
