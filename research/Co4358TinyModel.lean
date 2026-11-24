import PEqualNP.Co4358Tiny

namespace CoNum4358.Tiny
open CoAO3143

structure Good (k : Nat) (S : Finset W) : Prop where
  live : Live k 0 (S.image fun w => wide w.1)
  caps : ∀ s : Bool, ∃ w∈S, capability s w.2=true

inductive Trace : Nat → Nat → Finset W → Prop
  | done (q : Nat) (w : W) (orig : w.1=255) (sep₀ : w.2.1.separates=true)
      (sep₃ : w.2.2.separates=true) : Trace 0 q {w}
  | step {k q : Nat} {U : Finset W} (d : Bool) (a b : W) (apart : a≠b)
      (budget : pay d a b≤q) (clean : (make d a b).1≠0 ∧ (make d a b).1≠32767)
      (unused : (make d a b).1∉(insert a (insert b U)).image Prod.fst)
      (raw : (make d a b).1∉bare)
      (facts : Good (k+1) (insert a (insert b U)))
      (child : Trace k (q-pay d a b) (insert (make d a b) U)) :
      Trace (k+1) q (insert a (insert b U))

end CoNum4358.Tiny
