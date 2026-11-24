import Mathlib

namespace CoRawClosure3004
abbrev V := Fin 14
def near : V → Nat := ![1408,8832,12544,6272,11264,5632,2816,11,69,98,49,88,44,22]
def mask (a : V) : Nat := 1 <<< a.val
def marked (s : Nat) (a : V) : Bool := s.testBit a.val
def canEnter (s : Nat) (v : V) : Bool :=
  decide ((near v &&& s)=near v) ||
    (List.finRange 14).all (fun u => !(marked (near v) u) || decide ((near u &&& s)≠0))

theorem pair_closed : ∀ a b v : V, v≠a → v≠b → canEnter (mask a ||| mask b) v=false := by
  decide +kernel

theorem cover_two (a b : V) (v : V) (openGate : canEnter (mask a ||| mask b) v=true) :
    v=a ∨ v=b := by
  by_contra! other
  have closed := pair_closed a b v other.1 other.2
  exact Bool.noConfusion (closed.symm.trans openGate)

end CoRawClosure3004
