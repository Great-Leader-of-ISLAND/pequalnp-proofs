import PEqualNP.CoNine3024Data

namespace CoRoot3174
open CoNine3024

def other : Fin 3 → Fin 9 := ![2,3,8]

def mode (inv : Bool) : Fin 11 := if inv then 0 else 10

def head (b : Fin 3) (inv : Bool) : Atom :=
  let p := mode inv
  operation (geom p) true (rootAtom p 1) (rootAtom p (other b))

def root (b : Fin 3) (inv : Bool) : State :=
  let p := mode inv
  let ws := List.ofFn (rootAtom p) ++ [head b inv] ++ (if inv then [inverseAtom p] else [])
  ⟨ws,(rootAtom p 1).fixed ||| (rootAtom p (other b)).fixed⟩

end CoRoot3174
