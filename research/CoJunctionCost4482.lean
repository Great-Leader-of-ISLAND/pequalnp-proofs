import PEqualNP.CoBitBlock4482
namespace CoJunctionCost4482
open CoBitBlock4482

abbrev W := BitVec 512
abbrev Pin := W × Mark
structure Choice where
  a : Nat
  b : Nat
  op : Bool
  drop : Nat

def code (c : Choice) := ((16*c.a+c.b)*2+(if c.op then 1 else 0))*4+c.drop
def calc {n} (op : Bool) (a b : BitVec n) := if op then a ||| b else a &&& b
def delta (m : Mark) := m.1 ^^^ m.2

def rest (ws : List Pin) (a b : Nat) : Bits :=
  ws.zipIdx.foldl (fun acc p =>
    if p.2=a ∨ p.2=b then acc else acc ||| delta p.1.2) 0

/-- All four last-use choices and both gate operations. The order agrees
with the proof archive; each accepted choice consumes exactly one route. -/
def choices (ws : List Pin) (k : Nat) : List Choice :=
  let n := ws.length
  (List.range n).flatMap fun i => (List.range n).flatMap fun j =>
    if i≥j then [] else
    let a := ws.getD i (0,(0,0))
    let b := ws.getD j (0,(0,0))
    let keep := rest ws i j
    [false,true].flatMap fun d =>
      let full := calc d a.1 b.1
      if ws.any (fun w => w.1==full) then [] else
      let keepGate := keep ||| (calc d a.2.1 b.2.1 ^^^ calc d a.2.2 b.2.2)
      (List.range 4).filterMap fun drop =>
        let da := drop.testBit 0
        let db := drop.testBit 1
        let wid := n+1-(if da then 1 else 0)-(if db then 1 else 0)
        let cov := keepGate ||| (if da then 0 else delta a.2) ||| (if db then 0 else delta b.2)
        if wid≤6+(k-1) ∧ cov=BitVec.allOnes 258 then some ⟨i,j,d,drop⟩ else none

def toWords (before : List W) (c : Choice) : List W :=
  calc c.op (before.getD c.a 0) (before.getD c.b 0) ::
    (before.zipIdx.filter (fun w =>
      !((w.2==c.a && c.drop.testBit 0) || (w.2==c.b && c.drop.testBit 1)))).map Prod.fst

def sameSet (xs ys : List W) := xs.all ys.contains && ys.all xs.contains

/-- Numeric microbenchmark with the actual 512-bit transporter views and
target arrays. Generic physical correctness is supplied separately by the
frontier transport theorems, so this benchmark need not reconstruct 512
input assignments separately for each outgoing arc. -/
def routes (transport target : Nat → List W) : List Choice → List (Nat×Nat×Nat) → Bool
  | [],[] => true
  | c::cs,(id,t,g)::rs => code c==id && sameSet (toWords (transport g) c) (target t) &&
    routes transport target cs rs
  | _,_ => false
end CoJunctionCost4482
