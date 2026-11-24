import PEqualNP.CoNine3024CanonTable

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

end CoNine3024.Canon
