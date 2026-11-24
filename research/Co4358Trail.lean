import PEqualNP.Co4358Syntax
import PEqualNP.CoAO3143CotreeCheck

namespace CoNum4358
open CoAO3143

/-- Low input bit is vertex zero. Each KW bit is a positive edge row
    and a maximal negative independent-set row. We repeat the 56 pairs. -/
def posRows : List Nat := [3,6,17,34,68,40,80,72]
def negRows : List Nat := [13,26,28,37,52,66,97]
def rawKW : List CoAO3143.Sig := [
  (0x1fc07f000000001fc07f000000001fc07f,0x264c993264c993264c993264c993264c993264c9),
  (0xfe03fff0000000fe03fff0000000fe03fff,0x8912244891224489122448912244891224489122),
  (0x7f0003f80000007f0003f80000007f0003f80,0x74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d),
  (0x3f800000000fe03f800000000fe03f800000000,0x1c3870e1c3870e1c3870e1c3870e1c3870e1c387),
  (0xfc00001fc00001fc00001fc00001fc00001fc000,0x58b162c58b162c58b162c58b162c58b162c58b16),
  (0x3f80fe000000003f80fe000000003f80fe00000,0x62c58b162c58b162c58b162c58b162c58b162c58),
  (0xfc07f0000000fffc07f0000000fffc07f0000000,0x83060c183060c183060c183060c183060c183060)]

def lookupKW (bank : List Sig) (i : Nat) := bank.getD i zero

def Gate.kw (g : Gate) (bank : List Sig) : Sig :=
  bin g.isOr (lookupKW bank g.a) (lookupKW bank g.b)

def bankKW (bank : List Sig) : List Gate → List Sig
  | [] => bank
  | g::gs => bankKW (bank ++ [g.kw bank]) gs

abbrev LiftVal := BitVec 6
abbrev LiftSet := List LiftVal

def rawLoose : List LiftSet := [[1,63],[24,63],[32,63],[2,63],[48,63],[36,63],[12,63]]
def looseGate (d : Bool) (xs ys : LiftSet) : LiftSet :=
  63 :: (xs.flatMap fun x => ys.map fun y => if d then x ||| y else x &&& y).eraseDups
def Gate.loose (g : Gate) (bank : List LiftSet) : LiftSet :=
  looseGate g.isOr (bank.getD g.a []) (bank.getD g.b [])
def bankLoose (bank : List LiftSet) : List Gate → List LiftSet
  | [] => bank
  | g::gs => bankLoose (bank ++ [g.loose bank]) gs

/-- The fringe lists real physical wire indices. Last uses determine the
    optional retention of either operand. The output is the final gate. -/
inductive DirTrail : Nat → List Gate → Finset Nat → Prop
  | done {off : Nat} : DirTrail off [] {off-1}
  | step {off : Nat} {gs : List Gate} {U : Finset Nat} (g : Gate)
      (sane : g.sane off) (fresh : off∉U)
      (tail : DirTrail (off+1) gs (insert off U)) :
      DirTrail off (g::gs) (insert g.a (insert g.b U))

end CoNum4358
