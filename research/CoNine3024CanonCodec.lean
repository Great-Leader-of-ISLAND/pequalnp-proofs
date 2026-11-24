import PEqualNP.CoNine3024CanonTable
import PEqualNP.CoNine3024Data

namespace CoNine3024.Canon
def zeroAtom : Atom := ⟨0,0,0,0⟩

def unpack (vocab : Array Atom) (base : Nat) : Nat → Nat → List Atom
  | 0,_ => []
  | n+1,key =>
    if key=0 then [] else vocab[key%base-1]?.getD zeroAtom :: unpack vocab base n (key/base)

def fingerprint (s : State) : Nat :=
  s.wires.foldl (fun acc a => acc + (a.full.toNat%4294967291+1)^2%4294967291)
    (s.spent * 2654435761)

def mix (x salt : Nat) : Nat :=
  let y := ((x ^^^ salt)*73244475)%4294967296
  let z := ((y ^^^ (y/65536))*73244475)%4294967296
  z ^^^ (z/65536)

def proposed (cap salt : Nat) (delta : Array Nat) (s : State) : Nat :=
  if cap≤1 then 0 else
    let h := fingerprint s
    let b := mix h (salt+19)%delta.size
    (mix h (salt+347)%cap + delta[b]?.getD 0 * (1 + mix h (salt+2131)%(cap-1)))%cap

def table (vocab : Array Atom) (base salt : Nat) (delta : Array Nat) (words : Array Nat) : Table :=
  ⟨words.size,fun i =>
    let key := words[i]?.getD 0
    ⟨unpack vocab base 14 (key/35184372088832),key%35184372088832⟩,
    proposed words.size salt delta⟩


def fromKey (s : State) (code : Nat) : Option CoNine3024PairGuard.Hint :=
  if code=0 then none else
    let id := code-1
    let row (k : Nat) : Fin 320 := ⟨((id >>> k)%512)%320,Nat.mod_lt _ (by decide)⟩
    some ⟨s.wires[id%16]?.getD zeroAtom,s.wires[(id>>>4)%16]?.getD zeroAtom,
      row 8,row 17,row 26,row 35⟩

def oracle (salt : Nat) (delta keys : Array Nat) : Oracle := fun _ s =>
  fromKey s (keys[proposed keys.size salt delta s]?.getD 0)

def scatter (t : Array Nat) (stride : Nat) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,x => t[x%16]?.getD 0 + ((scatter t stride n (x/16)) <<< stride)

def expand (t : Array Nat) (stride rowfull repeatCols : Nat) (a : Truth) (y n fix : Nat) : Atom :=
  ⟨a,BitVec.ofNat 320 (scatter t stride 8 y * rowfull),BitVec.ofNat 320 (n*repeatCols),fix⟩

structure Packed where
  bits : Nat
  groups : Array Nat

def Packed.read (v : Packed) (i : Nat) : Nat :=
  ((v.groups[i/32]?.getD 0) >>> ((i%32)*v.bits)) % (2^v.bits)

def place (cap bins salt : Nat) (delta : Packed) (s : State) : Nat :=
  if cap≤1 then 0 else
    let h := fingerprint s
    let b := mix h (salt+19)%bins
    (mix h (salt+347)%cap + delta.read b * (1 + mix h (salt+2131)%(cap-1)))%cap

def lookup (cap bins salt : Nat) (offset refs hints : Packed) : Oracle := fun _ s =>
  fromKey s (hints.read (refs.read (place cap bins salt offset s)))

def chosen (mask : Nat) : List Nat → List Nat
  | [] => []
  | i::is => if mask%2=1 then i::chosen (mask/2) is else chosen (mask/2) is

def ids (base : Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,x => if x=0 then [] else (x%base-1) :: ids base n (x/base)

def record (vocab : Array Atom) (originals : List Nat) (pays : Packed)
    (paybase rawbase ibase : Nat) (word : Nat) : State :=
  if word=0 then ⟨[],0⟩ else
    let w := word-1
    let pool := w/paybase
    let ws := (chosen (pool%rawbase) originals ++ ids ibase 14 (pool/rawbase)).mergeSort
    ⟨ws.map (fun i => vocab[i]?.getD zeroAtom),pays.read (w%paybase)⟩

def catalog (sample : Nat → State) (count bins salt : Nat) (offset words : Packed) : Table :=
  ⟨count,fun i => sample (words.read i),place count bins salt offset⟩

def recordWith (label : Nat → Atom) (originals : List Nat) (pays : Packed)
    (paybase rawbase ibase : Nat) (word : Nat) : State :=
  if word=0 then ⟨[],0⟩ else
    let w := word-1
    let pool := w/paybase
    let ws := (chosen (pool%rawbase) originals ++ ids ibase 14 (pool/rawbase)).mergeSort
    ⟨ws.map label,pays.read (w%paybase)⟩

def initial (p : Fin 11) (i : Nat) : Truth :=
  if h : i<9 then rawTruth ⟨i,h⟩ else
    let seed := rawTruth 0 ||| rawTruth 2
    if i=9 then seed else if h : p.val<9 then ~~~(rawTruth ⟨p.val,h⟩) else ~~~seed

def column (p : Fin 11) (rootCount base : Nat) (recipes : Packed) : Nat → Nat → Truth
  | 0,i => initial p i
  | n+1,i =>
    if i<rootCount then initial p i else
      let entry := recipes.read (i-rootCount)
      let a := column p rootCount base recipes n (entry%base)
      let b := column p rootCount base recipes n ((entry/base)%base)
      if entry/(base*base)=0 then a &&& b else a ||| b

def labelWord (p : Fin 11) (rootCount base maxdepth ybase nbase : Nat) (recipes desc : Packed)
    (t : Array Nat) (stride rf period : Nat) (i : Nat) : Atom :=
  let w := desc.read i
  let y := w/base
  let n := y/ybase
  let f := n/nbase
  let grid : Array Nat := #[0,1,32,33,1024,1025,1056,1057,32768,32769,32800,32801,33792,33793,33824,33825]
  expand t stride rf period (column p rootCount base recipes maxdepth (w%base))
    (y%ybase) (n%nbase) (scatter grid 20 3 f)

end CoNine3024.Canon
