import PEqualNP.CoNine3024Guard

namespace CoNine3024PairGuard
open CoNine3024

structure Hint where
  a : Atom
  b : Atom
  r₁ : Fin 320
  r₂ : Fin 320
  n₁ : Fin 320
  n₂ : Fin 320

def owns (p : Fin 11) (ws : List Atom) (c : Fin 320) (a : Atom) : Bool :=
  (cellMasks p).getLsbD c.val && ws.all fun w => !(separator w).getLsbD c.val || w.full==a.full

def verify (p : Fin 11) (ws : List Atom) (h : Hint) : Bool :=
  h.a.full != h.b.full && h.r₂.val/(no p).length == h.r₁.val/(no p).length && h.n₂.val%(no p).length == h.n₁.val%(no p).length &&
  owns p ws h.r₁ h.a && owns p ws h.r₂ h.b && owns p ws h.n₁ h.a && owns p ws h.n₂ h.b

def bandRows (p : Fin 11) : List Cells :=
  let n := (no p).length
  let first : Cells := BitVec.ofNat 320 (2^n-1)
  (List.range (yes p).length).map fun i => first <<< (i*n)

def bandCols (p : Fin 11) : List Cells :=
  let n := (no p).length
  let first : Cells := (List.range (yes p).length).foldl (fun a i => a ||| ((1:Cells) <<< (i*n))) 0
  (List.range n).map fun j => first <<< j

def indexBit (v : Cells) : Fin 320 := ⟨v.toNat.log2%320,Nat.mod_lt _ (by decide)⟩

def bandHit (bs : List Cells) (x y : Cells) : Option (Fin 320 × Fin 320) :=
  bs.findSome? fun b =>
    let a := x &&& b
    let c := y &&& b
    if a != 0 && c != 0 then some (indexBit a,indexBit c) else none

def profilePair (rs cs : List Cells) (a b : Atom × Cells) : Option Hint := do
  let r ← bandHit rs a.2 b.2
  let n ← bandHit cs a.2 b.2
  return ⟨a.1,b.1,r.1,r.2,n.1,n.2⟩

def propose (rs cs : List Cells) : List (Atom × Cells) → Option Hint
  | [] => none
  | x::xs => match xs.findSome? (profilePair rs cs x) with
    | some h => some h
    | none => propose rs cs xs

def hint (p : Fin 11) (ws : List Atom) : Option Hint :=
  let keys := ws.map fun w => (w,separator w &&& cellMasks p)
  let twin := keys.foldl (fun (v : Cells × Cells) a => (v.1 ||| a.2,v.2 ||| (v.1 &&& a.2))) (0,0)
  propose (bandRows p) (bandCols p) (keys.map fun (w,k) => (w,k &&& ~~~twin.2))

def keep (p : Fin 11) (cap : Nat) (s : State) : Bool :=
  !(s.wires.length==cap+1 && (hint p s.wires).any (verify p s.wires))

end CoNine3024PairGuard
