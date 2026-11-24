import PEqualNP.Co4358Tiny

namespace CoNum4358.Direct

structure Pack where
  bits : Nat
  words : Array Nat
def Pack.val (x : Pack) (i : Nat) := (x.words[i/32]?.getD 0 >>> (x.bits*(i%32))) % 2^x.bits
def blank : Pack := ⟨0,#[]⟩

structure Tier where
  count : Nat
  groups : Nat
  index : Pack
  base : Array Nat
  keys : Array Pack
structure Data where
  dict : Pack
  starts : Pack
  layers : Array Tier

def roots : List Nat := [31234,91208,119072,139448,299089,361092,396548]
def getTier (d : Data) (k : Nat) : Tier := d.layers[k]?.getD ⟨0,0,blank,#[],#[]⟩

def lower (ok : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0,lo,_ => lo
  | fuel+1,lo,hi => if lo≥hi then lo else
    let m := (lo+hi)/2
    if ok m then lower ok fuel lo m else lower ok fuel (m+1) hi

def column (t : Tier) (n index : Nat) :=
  (t.keys[n]?.getD blank).val (index-(t.base[n]?.getD 0))

def rawNumber (v : Nat) : Nat :=
  if v==31234 then 0 else if v==91208 then 1 else if v==119072 then 2 else
  if v==139448 then 3 else if v==299089 then 4 else if v==361092 then 5 else
  if v==396548 then 6 else 7

def decodeExtras (dict : Pack) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,key => dict.val (key%2048)::decodeExtras dict n (key>>>11)

def rawPart (raw : Nat) := (List.range 7).filterMap fun j =>
  if raw.testBit j then roots[j]? else none

def row (d : Data) (k i : Nat) : Nat × List Nat :=
  let t := getTier d k
  let g := lower (fun j => decide (t.index.val j>>>11>i)) 16 0 t.groups - 1
  let tagWord := t.index.val g % 2048
  let n := tagWord>>>8
  (tagWord%2,rawPart ((tagWord>>>1)%128) ++ decodeExtras d.dict n (column t n i))

def dictID (d : Data) (v : Nat) : Nat :=
  let b := v>>>10
  let lo := d.starts.val b
  let hi := d.starts.val (b+1)
  lower (fun j => decide (d.dict.val j≥v)) 12 lo hi

def encodeExtras (xs : List Nat) := xs.mergeSort.foldr (fun x n => (n<<<11) ||| x) 0

def place (d : Data) (k q : Nat) (words : List Nat) : Nat :=
  let t := getTier d k
  let split := words.foldl (fun (v : Nat×List Nat) w =>
    let j := rawNumber w
    if j<7 then (v.1 ||| (1<<<j),v.2) else (v.1,dictID d w::v.2)) (0,[])
  let n := split.2.length
  let tag := q+2*split.1+256*n
  let g := lower (fun i => decide (t.index.val i%2048≥tag)) 16 0 t.groups
  let found := t.index.val g
  if g≥t.groups || found%2048 != tag then t.count else
    let hi := if g+1<t.groups then t.index.val (g+1)>>>11 else t.count
    let key := encodeExtras split.2
    let i := lower (fun j => decide (column t n j≥key)) 16 (found>>>11) hi
    if i<hi && column t n i==key then i else t.count

end CoNum4358.Direct
