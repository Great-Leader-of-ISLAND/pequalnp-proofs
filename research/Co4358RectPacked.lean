import PEqualNP.Co4358RectCheck

namespace CoNum4358.RectCheck

structure Pack where
  bits : Nat
  words : Array Nat

def Pack.at (z : Pack) (i : Nat) : Nat :=
  ((z.words[i/32]?.getD 0) >>> (z.bits*(i%32))) % 2^z.bits

structure Layer where
  count : Nat
  buckets : Nat
  salt : Nat
  offset : Pack
  move : Pack

abbrev Bytes := Array Layer

def fetch (p : Bytes) (k : Nat) : Layer :=
  p[k]?.getD ⟨0,0,0,⟨0,#[]⟩,⟨0,#[]⟩⟩

def mix (x n : Nat) : Nat :=
  let b := ((x ^^^ n)*0x45d9f3b)%4294967296
  let c := ((b ^^^ (b>>>16))*0x45d9f3b)%4294967296
  c ^^^ (c>>>16)

def foldHash (salt : Nat) (t : Nat×Nat×Nat) (x : Nat) : Nat×Nat×Nat :=
  (t.1+mix x (salt+19),t.2.1+mix x (salt+347),t.2.2+mix x (salt+2131))

def code (w : AugWire) : Nat :=
  let hi := (w.1.2.toNat%128) <<< 8
  let u := w.1.1.toNat &&& 0x2040810204081
  let u := (u ||| (u>>>6)) &&& 0xc003000c003
  let u := (u ||| (u>>>12)) &&& 0xf000000f
  let sig := hi ||| ((u ||| (u>>>24)) &&& 255)
  (sig <<< 4) ||| (w.2.2.original.toNat <<< 3) ||| (w.2.1.original.toNat <<< 2) |||
    (w.2.2.separates.toNat <<< 1) ||| w.2.1.separates.toNat

def findSlot (l : Layer) (q : Nat) (ws : List AugWire) : Nat :=
  let h := ws.foldl (fun acc w => foldHash l.salt acc (code w)) (foldHash l.salt (0,0,0) q)
  let d := l.offset.at (h.1%l.buckets)
  let i := (h.2.1+d*(1+h.2.2%(l.count-1)))%l.count
  if (l.move.at i)%16 == ((h.2.1>>>17)%16) then i else l.count

def decode (word : Nat) : AugWire :=
  let v := word>>>4
  let u := v &&& 255
  let u := (u ||| (u<<<24)) &&& 0xf000000f
  let u := (u ||| (u<<<12)) &&& 0xc003000c003
  let rows := ((u ||| (u<<<6)) &&& 0x2040810204081)*127
  ((BitVec.ofNat 160 (rows*0x10000000000000100000000000001),
      BitVec.ofNat 160 ((v>>>8)*0x408102040810204081020408102040810204081)),
    (⟨word.testBit 2,word.testBit 0⟩,⟨word.testBit 3,word.testBit 1⟩))

def placeWord (z : Nat) : List Nat → List Nat
  | [] => [z]
  | a::xs => if z<a then z::a::xs else a::placeWord z xs

def replay (r : Nat × List Nat) (m : Nat) : Nat × List Nat :=
  let xs := r.2
  let a := xs.getD ((m>>>7)%16) 0
  let b := xs.getD ((m>>>3)%16) 0
  let isOr := m.testBit 2
  let bits := if isOr then a|||b else a&&&b
  let n := (bits>>>2)%4
  let can := if isOr then ((a|||b)%4) &&& (3 ^^^ n) else (a|||b)%4
  let v := ((bits>>>4)<<<4) ||| (n<<<2) ||| can
  let tail := xs.filter fun x => (x != a || m.testBit 0) && (x != b || m.testBit 1)
  (if isOr && ((a>>>4)==7442 || (b>>>4)==7442) then r.1-1 else r.1,placeWord v tail)

def unpack (p : Bytes) : Nat → Nat → Nat × List Nat
  | 0,_ => (1,[31234,91208,119072,139448,299089,361092,396548])
  | d+1,i =>
    let v := (((fetch p (11-(d+1))).move).at i)>>>4
    if v==0 then (0,[]) else replay (unpack p d ((v-1)>>>11)) ((v-1)%2048)

def table (p : Bytes) (k : Nat) : Table :=
  let lay := fetch p k
  ⟨lay.count,fun i => let x := unpack p (11-k) i; (x.1,x.2.map decode),findSlot lay⟩

def entryTest (p : Bytes) (k i : Nat) : Bool :=
  let x := (table p (k+1)).row i
  node k x.1 (table p k) x.2

def groupCheck (p : Bytes) (k group : Nat) (b : Fin 8) : Bool :=
  let i := (group*8+b.val)*16
  CoAO3143.Memo.allAt (entryTest p k) i (min 16 ((table p (k+1)).count-i))

theorem layer {p k} (old : Valid k (table p k))
    (closed : ∀ i<(table p (k+1)).count, entryTest p k i=true) :
    Valid (k+1) (table p (k+1)) :=
  fun i h => node_ok old (closed i h)

theorem chunkLayer {p k} (old : Valid k (table p k)) (chunk : Nat) (hc : 0<chunk)
    (groups : Nat) (enough : (table p (k+1)).count≤groups*8*chunk)
    (cert : ∀ a : Fin groups,∀ b : Fin 8,
      CoAO3143.Memo.allAt (entryTest p k) ((a.val*8+b.val)*chunk)
     (min chunk ((table p (k+1)).count-(a.val*8+b.val)*chunk))=true) :
    Valid (k+1) (table p (k+1)) := by
  apply layer old
  intro i hi
  have div : i/chunk < groups*8 := (Nat.div_lt_iff_lt_mul hc).2 (by omega)
  have div8 : i/chunk/8<groups := (Nat.div_lt_iff_lt_mul (by decide : 0<8)).2 (by simpa [Nat.mul_comm] using div)
  let a : Fin groups := ⟨i/chunk/8,div8⟩
  let b : Fin 8 := ⟨(i/chunk)%8,Nat.mod_lt _ (by decide)⟩
  have ab : a.val*8+b.val=i/chunk := by dsimp [a,b]; omega
  have h := cert a b
  rw [ab] at h
  apply CoAO3143.Memo.allAt_get h i (Nat.div_mul_le_self _ _)
  have less := Nat.mod_lt i hc
  have eq := Nat.mod_add_div i chunk
  rw [Nat.mul_comm chunk (i/chunk)] at eq
  omega

end CoNum4358.RectCheck
