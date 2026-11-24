import PEqualNP.Co4358DirectData
namespace CoNum4358.IntGround
open CoAO3143
abbrev K := Nat
abbrev W := Nat
def sig (w : Nat) := w>>>4
def bare : List Nat := [18693,8715,7442,1952,5700,22568,24784]
def pay (d : Bool) (a b : Nat) := if d && ((a>>>4)==7442 || (b>>>4)==7442) then 1 else 0
def make (d : Bool) (a b : Nat) :=
  let raw := if d then a|||b else a&&&b
  let caps := (a|||b) &&& 3
  let live := if d then caps &&& (3 ^^^ ((raw>>>2) &&& 3)) else caps
  ((raw>>>2)<<<2) ||| live
open Direct (coins getTier row place)
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def directed (w : K) (p : Fin 8) (n : Fin 7) : Bool :=
  w.testBit p.val && !(w.testBit (8+n.val))

def fullMask : Nat := 0xffffffffffffff

def columnMask : Nat := 0x2040810204081

def cells (w : K) : Nat :=
  let v := w
  let u := v &&& 255
  let u := (u ||| (u<<<24)) &&& 0xf000000f
  let u := (u ||| (u<<<12)) &&& 0xc003000c003
  let rows := ((u ||| (u<<<6)) &&& columnMask)*127
  rows &&& (fullMask ^^^ ((v>>>8)*columnMask))

def missing (ws : List K) : Bool :=
  let total := ws.foldl (fun n a => n ||| cells a) 0
  if total==fullMask then false else
    let i := (fullMask ^^^ total).log2
    ws.all fun a => !(directed a (Fin.ofNat 8 (i/7)) (Fin.ofNat 7 i))

def forced (ws : List K) (p : Fin 8) (n : Fin 7) (a : K) : Bool :=
  ws.all fun x => x==a || !(x.testBit p.val) || x.testBit (8+n.val)

structure Rect where
  a : K
  b : K
  p : Fin 8
  q₁ : Fin 8
  q₂ : Fin 8
  n : Fin 7
  m₁ : Fin 7
  m₂ : Fin 7

def validRect (ws : List K) (r : Rect) :=
  r.a != r.b && forced ws r.p r.m₁ r.a && forced ws r.q₁ r.n r.a &&
    forced ws r.p r.m₂ r.b && forced ws r.q₂ r.n r.b

structure Prof where
  wire : K
  unique : Nat
  posMask : Nat
  negMask : Nat

def prof (a : K) (only : Nat) : Prof :=
  let u := cells a &&& only
  let high := columnMask<<<6
  let low := fullMask ^^^ high
  let p := (u ||| ((u&&&low)+low)) &&& high
  let z := u ||| (u>>>7)
  let z := z ||| (z>>>14)
  let z := z ||| (z>>>28)
  ⟨a,u,p,z%128⟩

def propose (a b : Prof) : Option Rect :=
  let posBoth := a.posMask &&& b.posMask
  let negBoth := a.negMask &&& b.negMask
  if posBoth==0 || negBoth==0 then none else
    let p := posBoth.log2/7
    let n := negBoth.log2
    let band := 127<<<(7*p)
    let col := columnMask<<<n
    let A := fun x : Nat => Fin.ofNat 8 ((x&&&col).log2/7)
    let B := fun x : Nat => Fin.ofNat 7 ((x&&&band).log2%7)
    some ⟨a.wire,b.wire,Fin.ofNat 8 p,A a.unique,A b.unique,Fin.ofNat 7 n,B a.unique,B b.unique⟩

def firstHit : List Prof → Option Rect
  | [] => none
  | p::ps => (ps.findSome? (propose p)).orElse fun _ => firstHit ps

def restrict (ws : List K) : Bool :=
  let seen := ws.foldl (fun (p : Nat×Nat) a =>
    let u := cells a; (p.1|||u,p.2||| (u&&&p.1))) (0,0)
  let only := seen.1 ^^^ seen.2
  (firstHit (ws.map fun w => prof w only)).any (validRect ws)

structure Table where
  count : Nat
  row : Nat → Nat × List W
  loc : Nat → List W → Nat

def matched (T : Table) (q : Nat) (ws : List W) :=
  let i := T.loc q ws
  let r := T.row i
  decide (i<T.count) && r.1==q && ws.isPerm r.2

def cap (ws : List W) (s : Bool) := ws.any fun w => w.testBit (if s then 0 else 1)

def isGoal (w : W) := (w>>>4)==255 && (w&&&3)==3

def overfull (k : Nat) (cs : List K) := decide (k+1<cs.length)

def rectBound (k : Nat) (cs : List K) := (cs.length==k+1) && restrict cs

def blocked (k q : Nat) (T : Table) (ws : List W) : Bool :=
  let cs := ws.map sig
  !(cap ws true && cap ws false) || overfull k cs || missing cs ||
    (if k==0 then !(ws.any isGoal) else matched T q ws || rectBound k cs)

def remaining (ws : List W) (a b : W) (ka kb : Bool) :=
  ws.filter fun z => (z != a || ka) && (z != b || kb)

def branch (k q : Nat) (T : Table) (ws : List W) (a b : W) (d : Bool) :=
  let z := make d a b
  decide (pay d a b≤q) && (sig z) != 0 && (sig z) != 32767 &&
    !(bare.contains (sig z)) && !(ws.any fun w => (sig w)==(sig z)) &&
      options.any fun ka => options.any fun kb =>
        !(blocked k (q-pay d a b) T (z::remaining ws a b ka kb))

def check (k q : Nat) (T : Table) (ws : List W) :=
  decide (ws.map sig).Nodup && !(scanPairs (fun a b => options.any (branch k q T ws a b)) ws)

def table (k : Nat) : Table :=
  ⟨(getTier coins k).count,Direct.row coins k,Direct.place coins k⟩

def entry (k i : Nat) : Bool :=
  let r := (table (k+1)).row i
  check k r.1 (table k) r.2



namespace Fast
def retain (a b : W) (ka kb : Bool) (rest : List W) : List W :=
  let r := if kb then b::rest else rest
  if ka then a::r else r

def possible (ws : List W) (mask : Nat) :=
  if mask==fullMask then true else
    let i := (fullMask ^^^ mask).log2
    ws.any fun w => directed (sig w) (Fin.ofNat 8 (i/7)) (Fin.ofNat 7 i)

def finish (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false &&
    (if k==0 then ws.any isGoal else !(matched T q ws || rectBound k (ws.map sig)))

def tryGate (k q : Nat) (T : Table) (ws rest : List W) (a b : W)
    (restMask ca cb : Nat) (d : Bool) :=
  let z := make d a b
  let payNow := pay d a b
  decide (payNow≤q) && (sig z) != 0 && (sig z) != 32767 && !(bare.contains (sig z)) &&
    !(ws.any fun w => (sig w)==(sig z)) &&
    (let base := restMask ||| cells (sig z)
     options.any fun ka => options.any fun kb =>
       decide (1+rest.length+ka.toNat+kb.toNat≤k+1) &&
       (let fringe := z::retain a b ka kb rest
        let mask := (if ka then ca else 0) ||| (if kb then cb else 0) ||| base
        possible fringe mask && finish k (q-payNow) T fringe))

def node (k q : Nat) (T : Table) (ws : List W) :=
  decide (ws.map sig).Nodup &&
  !(scanPairs (fun a b =>
    let rest := remaining ws a b false false
    let mask := rest.foldl (fun n w => n ||| cells (sig w)) 0
    options.any (tryGate k q T ws rest a b mask (cells (sig a)) (cells (sig b)))) ws)

def entry (k i : Nat) : Bool :=
  let r := (table (k+1)).row i
  node k r.1 (table k) r.2

theorem p3 : CoAO3143.Memo.allAt (entry 2) 0 8=true := by decide +kernel
theorem p7 : CoAO3143.Memo.allAt (entry 6) 0 8=true := by decide +kernel
theorem p9 : CoAO3143.Memo.allAt (entry 8) 0 8=true := by decide +kernel
theorem p11 : entry 10 0=true := by decide +kernel
end Fast
end CoNum4358.IntGround
