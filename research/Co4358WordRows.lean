import PEqualNP.Co4358DirectPack
namespace CoNum4358.WordRows
open Direct (Pack rawPart)

structure Tier where
  total : Nat
  cuts : Array Nat
  header : Pack
  extras : Array Pack
  edgeStart : Pack
  edgeList : Pack

def blank : Tier := ⟨0,#[0,0,0,0,0,0,0],⟨0,#[]⟩,#[],⟨0,#[]⟩,⟨0,#[]⟩⟩
def bound (t : Tier) (n : Nat) := t.cuts[n]?.getD t.total

def width (t : Tier) (i : Nat) :=
  if i<bound t 2 then (if i<bound t 1 then 0 else 1)
  else if i<bound t 4 then (if i<bound t 3 then 2 else 3)
  else if i<bound t 5 then 4 else 5

def unroll : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,c => (c%524288)::unroll n (c>>>19)

def row (t : Tier) (i : Nat) : Nat × List Nat :=
  let h := t.header.val i
  let n := width t i
  let items := (t.extras[n]?.getD ⟨0,#[]⟩).val (i-bound t n)
  (h%2,rawPart (h>>>1) ++ unroll n items)

def seek (es : Pack) (code : Nat) : Nat → Nat → Nat
  | 0,_ => 1048576
  | fuel+1,i =>
    let e := es.val i
    if e>>>10==code then e%1024 else seek es code fuel (i+1)

def locate (t : Tier) (i code : Nat) :=
  let start := t.edgeStart.val i
  let stop := t.edgeStart.val (i+1)
  seek t.edgeList code (stop-start) start
end CoNum4358.WordRows
