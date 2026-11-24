import PEqualNP.CoJunctionCost4482
namespace CoJunctionFixed4482

/-- Fixed-width positions are contained in short independent Nat literals.
No operation shifts or walks across the entire graph payload. -/
structure Column where
  width : Nat
  blocks : Array Nat

def field (c : Column) (i : Nat) : Nat :=
  (((c.blocks[i/64]?).getD 0) >>> ((i%64)*c.width)) % 2^c.width

structure Graph where
  size : Nat
  idBits : Nat
  offsetBits : Nat
  runCount : Nat
  internalCount : Nat
  rows : Column
  actions : Column
  parentRuns : Column
  exitRuns : Column
  arcs : Column

/-- First sorted table index whose key reaches x (an absent one returns n).
Fuel is a conservative bound on the height of this binary search. -/
def lowerBound (key : Nat→Nat) (x : Nat) : Nat → Nat → Nat → Nat
  | 0,lo,_ => lo
  | f+1,lo,hi =>
    if lo≥hi then lo else
    let m := (lo+hi)/2
    if key m < x then lowerBound key x f (m+1) hi else lowerBound key x f lo m

def lookupBound (key : Nat→Nat) (n x : Nat) :=
  lowerBound key x ((n+1).log2+2) 0 n

def budget (h : Graph) (i : Nat) := (field h.rows i)%8
def leafCode (h : Graph) (i : Nat) := (field h.rows i)/8

def parent (h : Graph) (i : Nat) :=
  let pos := lookupBound (fun j => (field h.parentRuns j) >>> h.idBits) h.runCount i
  (field h.parentRuns pos)%2^h.idBits

def firstAction (h : Graph) (i : Nat) := field h.actions (i-1)

def exits (h : Graph) (i : Nat) : Nat×Nat :=
  let pos := lookupBound (fun j => (field h.exitRuns j) >>> h.offsetBits) h.internalCount i
  let last := field h.exitRuns pos
  if pos≥h.internalCount ∨ last >>> h.offsetBits ≠ i then (0,0) else
    (if pos=0 then 0 else (field h.exitRuns (pos-1))%2^h.offsetBits,last%2^h.offsetBits)

def references (h : Graph) (i : Nat) : List (Nat×Nat) :=
  let (start,stop) := exits h i
  (List.range (stop-start)).map fun d =>
    let v := field h.arcs (start+d)
    (v/16,v%16)

end CoJunctionFixed4482
