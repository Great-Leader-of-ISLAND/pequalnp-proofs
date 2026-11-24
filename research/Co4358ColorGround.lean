import PEqualNP.Co4358BicolorWords

import PEqualNP.Co4358CornerPost

namespace CoNum4358.Tiny.ShareGrid

open CoAO3143

open CoNum4358.WordRows

def cov (xs : List K) := (Corners.counts xs).1

def noBit (s : Nat) (p : Fin 8) (n : Fin 7) := !s.testBit (p.val*7+n.val)

def productBit (s : Nat) (p : Fin 8) (n : Fin 7) : Bool :=
  let uncovered := fullMask ^^^ s
  let m := Fin.ofNat 7 (((uncovered >>> (p.val*7)) &&& 127).log2)
  let q := Fin.ofNat 8 (((uncovered &&& (columnMask <<< n.val)).log2)/7)
  noBit s p m && noBit s q n

end CoNum4358.Tiny.ShareGrid

namespace CoNum4358.Tiny.ShareGrid

open CoAO3143

open CoNum4358.WordRows

def estimateProduct (used : Nat) :=
  let u := fullMask ^^^ used
  let high := columnMask<<<6
  let low := fullMask ^^^ high
  let p := ((u ||| ((u&&&low)+low)) &&& high)>>>6
  let z := u ||| (u>>>7)
  let z := z ||| (z>>>14)
  let z := z ||| (z>>>28)
  p*(z%128)

def uncoveredProduct (left right prod : Nat) :=
  let missing := prod &&& (fullMask ^^^ left)
  if missing==0 then false else
    let i := missing.log2
    let p := Fin.ofNat 8 (i/7)
    let n := Fin.ofNat 7 i
    productBit right p n && noBit left p n

end CoNum4358.Tiny.ShareGrid

namespace CoNum4358.Tiny.ShareGrid

open CoAO3143

open CoNum4358.WordRows

def shade (xs : List K) (a b : Prof) :=
  match propose a b with
  | none => false
  | some r => r.a==a.wire && r.b==b.wire && validRect xs r

end CoNum4358.Tiny.ShareGrid

namespace CoNum4358.Tiny.ShareGrid.Forest

open CoAO3143

open CoNum4358.WordRows

structure Label where
  wire : K
  root : K
  flip : Bool
deriving DecidableEq, Repr

def seed (xs : List K) := xs.map fun w => Label.mk w w false

def locate (ls : List Label) (x : K) := ls.find? fun v => v.wire==x

def rebase (a b : Label) (v : Label) :=
  if v.root=b.root then ⟨v.wire,a.root,xor v.flip (!(xor a.flip b.flip))⟩ else v

def link (x y : K) (ls : List Label) : Option (List Label) := do
  let some a := locate ls x | return ls
  let some b := locate ls y | return ls
  if a.root=b.root then
    if a.flip=b.flip then none else return ls
  else return ls.map (rebase a b)

def edges (xs : List K) : List Prof → List (K×K)
  | [] => []
  | a::r => (r.filterMap (fun b => if shade xs a b then some (a.wire,b.wire) else none))++edges xs r

def compile : List (K×K) → List Label → Option (List Label)
  | [],ls => some ls
  | e::es,ls => (link e.1 e.2 ls).bind (compile es)

end CoNum4358.Tiny.ShareGrid.Forest

namespace CoNum4358.Tiny.ShareGrid.Forest

open CoAO3143

open CoNum4358.WordRows

structure Block where
  key : K
  lhs : List K
  rhs : List K
deriving Repr

def band (ls : List Label) (r : K) (b : Bool) :=
  (ls.filter (fun l => l.root==r && l.flip==b)).map Label.wire

def blocks (ls : List Label) := (ls.map Label.root).eraseDups.map fun r => Block.mk r (band ls r false) (band ls r true)

def pool : List Block → List K
  | [] => []
  | g::gs => g.lhs ++ (g.rhs ++ pool gs)

def solve : List Block → List K → List K → Bool
  | [],a,b => !a.isEmpty && !(uncoveredProduct (cov a) (cov b) (estimateProduct (cov b)))
  | g::gs,a,b =>
    let anySide := pool (g::gs)
    let cA := cov (a++anySide)
    let cB := cov (b++anySide)
    !(uncoveredProduct cA cB (estimateProduct cB)) &&
      (solve gs (g.lhs++a) (g.rhs++b) || solve gs (g.rhs++a) (g.lhs++b))

def shadePossible (xs : List K) :=
  let unique := Corners.exclusive xs
  let pairs := edges xs (xs.map fun x => prof x unique)
  (compile pairs (seed xs)).any (fun ls => solve (blocks ls) [] [])

end CoNum4358.Tiny.ShareGrid.Forest

namespace CoNum4358.Tiny.Splice

open CoAO3143

open CoNum4358.WordRows

def stamp (q : Nat) (ws : List W) :=
  (ws.foldl (fun s w => let x := emit w; s+(x ^^^ (x>>>7))*(x+89587)) (q*17+ws.length*467))%65536

def stored (k i : Nat) := let row := WordRows.row (Bicolor.tier k) i; (row.1,row.2.map read)

def bank (parent i k : Nat) : Table :=
  ⟨(Bicolor.tier k).total,stored k,fun q ws => WordRows.findHash (Bicolor.tier parent) i (stamp q ws)⟩

def shadeBound (k : Nat) (cs : List K) := cs.length==k && !(ShareGrid.Forest.shadePossible cs)

def post (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false &&
    (if k==0 then ws.any isGoal else
      !(Corners.limit k (ws.map Prod.fst) || matched T q ws || shadeBound k (ws.map Prod.fst)))

def entry (k i : Nat) :=
  let r := stored (k+1) i
  MaskFast.nodeWith post k r.1 (bank (k+1) i k) r.2

end CoNum4358.Tiny.Splice

