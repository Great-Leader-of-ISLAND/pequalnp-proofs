import PEqualNP.CoNine3024Data

namespace CoNine3024
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- A three-step path indexes accepted children only. A missing child is
    observable, and the positive control below requires an actual endpoint. -/
def traceAt (g : Geometry) : Nat → State → List Nat → Option State
  | _,s,[] => some s
  | 0,_,_::_ => none
  | k+1,s,i::is => ((children g k s)[i]?).bind fun t => traceAt g k t is

def probe (p : Fin 11) (seed : Bool) (ids : List Nat) : Bool :=
  (traceAt (geom p) 13 (root p seed) ids).any fun s => !(search (geom p) (13-ids.length) s)

/-- The exact nine-cut budget already prevents these four signed roots. -/
theorem root0 : search (geom 0) 13 (root 0 true)=false := by decide +kernel
theorem root2 : search (geom 2) 13 (root 2 true)=false := by decide +kernel
theorem root4 : search (geom 4) 13 (root 4 true)=false := by decide +kernel
theorem root7 : search (geom 7) 13 (root 7 true)=false := by decide +kernel

end CoNine3024
