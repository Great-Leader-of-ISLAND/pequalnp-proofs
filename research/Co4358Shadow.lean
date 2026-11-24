import PEqualNP.Co4358PairSearch

namespace CoNum4358
open CoAO3143

abbrev AugWire := Sig × PairFlag

def augGate (d : Bool) (a b : AugWire) : AugWire :=
  (bin d a.1 b.1,mergePair d a.2 b.2)

def twoKW : Sig := lookupKW rawKW 2

def augPay (d : Bool) (a b : AugWire) : Nat :=
  if d && (a.1 == twoKW || b.1 == twoKW) then 1 else 0

structure Local (k : Nat) (S : Finset AugWire) : Prop where
  live : Live k 0 (S.image Prod.fst)
  caps : ∀ s : Bool, ∃ w∈S, capability s w.2=true

inductive Shadow : Nat → Nat → Finset AugWire → Prop
  | done (q : Nat) (w : AugWire) (orig : w.1=target)
      (sep₀ : w.2.1.separates=true) (sep₃ : w.2.2.separates=true) : Shadow 0 q {w}
  | step {k q : Nat} {U : Finset AugWire} (d : Bool) (a b : AugWire)
      (apart : a≠b) (budget : augPay d a b≤q)
      (clean : proper (augGate d a b).1)
      (unused : (augGate d a b).1∉(insert a (insert b U)).image Prod.fst)
      (raw : (augGate d a b).1∉rawKW)
      (localFacts : Local (k+1) (insert a (insert b U)))
      (child : Shadow k (q-augPay d a b) (insert (augGate d a b) U)) :
      Shadow (k+1) q (insert a (insert b U))

def augRoots : List AugWire := rawKW.zip rawPair

end CoNum4358
