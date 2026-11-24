import PEqualNP.CoAO3143Memo

namespace CoAO3143.Memo

structure Packed where
  bits : Nat
  words : Array Nat

def Packed.entry (p : Packed) (i : Nat) : Nat :=
  (p.words[i/32]?.getD 0 >>> (p.bits*(i%32))) % 2^p.bits

structure LayerCode where
  cap : Nat
  buckets : Nat
  salt : Nat
  place : Packed
  moves : Packed

structure Program where
  width : Nat
  height : Nat
  maxDepth : Nat
  roots : List Nat
  layers : Array LayerCode

def blankCode : LayerCode := ⟨0,0,0,⟨0,#[]⟩,⟨0,#[]⟩⟩

def layerAt (p : Program) (k : Nat) := p.layers[k]?.getD blankCode

def mix (x salt : Nat) : Nat :=
  let y := ((x ^^^ salt)*0x45d9f3b) % 4294967296
  let z := ((y ^^^ (y>>>16))*0x45d9f3b) % 4294967296
  z ^^^ (z>>>16)

def extractWord (p : Program) (s : Sig) : Nat :=
  let high := (s.2.toNat%2^p.width) <<< p.height
  (List.range p.height).foldl (fun n i => if s.1.getLsbD (i*p.width) then n ||| (1<<<i) else n) high

def hashWire (salt : Nat) (h : Nat×Nat×Nat) (x : Nat) : Nat×Nat×Nat :=
  (h.1+mix x (salt+19),h.2.1+mix x (salt+347),h.2.2+mix x (salt+2131))

def lookup (p : Program) (k : Nat) (ws : List Sig) : Nat :=
  let l := layerAt p k
  let h := ws.foldl (fun h v => hashWire l.salt h (extractWord p v)) (0,0,0)
  let d := l.place.entry (h.1%l.buckets)
  (h.2.1+d*(1+h.2.2%(l.cap-1)))%l.cap

def expand (p : Program) (v : Nat) : Sig :=
  let n := p.width
  let m := p.height
  let rowMask := 2^n-1
  let rows := (List.range m).foldl (fun s i => if v.testBit i then s ||| (rowMask<<<(i*n)) else s) 0
  let rep := fun x period => x*((2^(period*((160+period-1)/period))-1)/(2^period-1))
  (BitVec.ofNat 160 (rep rows (m*n)),BitVec.ofNat 160 (rep ((v>>>m)%2^n) n))

def applyMove (xs : List Nat) (word : Nat) : List Nat :=
  let i := (word>>>7)%16
  let j := (word>>>3)%16
  let m := word%4
  let a := xs.getD i 0
  let b := xs.getD j 0
  let z := if word.testBit 2 then a ||| b else a &&& b
  let others := xs.filter fun w => w != a && w != b
  let keptA := if m.testBit 0 then a::others else others
  let keptB := if m.testBit 1 then b::keptA else keptA
  (z::keptB).mergeSort

def unpack (p : Program) : Nat → Nat → List Nat
  | 0,_ => p.roots
  | d+1,i =>
    let k := p.maxDepth-(d+1)
    let word := (layerAt p k).moves.entry i
    if word=0 then [] else
      applyMove (unpack p d ((word-1)>>>11)) ((word-1)%2048)

def dataset (p : Program) (k : Nat) : Table :=
  let l := layerAt p k
  ⟨l.cap,fun i => (unpack p (p.maxDepth-k) i).map (expand p),lookup p k⟩

end CoAO3143.Memo
