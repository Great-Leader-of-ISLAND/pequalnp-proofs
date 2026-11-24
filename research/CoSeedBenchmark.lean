import Mathlib

namespace SeedBenchmark
abbrev Word := Nat × Nat
def target : Word := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0)
def all := target.1
def sep (w : Word) := w.1 ^^^ w.2
def meet (a b : Word) : Word := (a.1 &&& b.1,a.2 &&& b.2)
def join (a b : Word) : Word := (a.1 ||| b.1,a.2 ||| b.2)
def skip (a b : Word) : Word := (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
def cover (ws : List Word) := ws.foldl (fun c w => c ||| sep w) 0
def pairs {α : Type} (f : α → α → Bool) : List α → Bool
  | [] => false
  | x::xs => xs.any (f x) || pairs f xs
def multiplicities : List Word → Nat×Nat
  | [] => (0,0)
  | w::ws =>
    let s := sep w
    let m := multiplicities ws
    (s ||| m.1, (s &&& m.1) ||| m.2)

def guarded (k : Nat) (next : List Word→Bool) (ws : List Word) : Bool :=
  let n := ws.length
  if n>k+2 then false else
  let bucket := multiplicities ws
  let once := bucket.1 ^^^ bucket.2
  let cols := ws.map fun w => (w,sep w &&& once)
  let half := n≤k+1
  let stay := n≤k
  pairs (fun a b =>
    let a0 := (a.2 &&& b.1.1)==0
    let a1 := (a.2 &&& b.1.1)==a.2
    let b0 := (b.2 &&& a.1.1)==0
    let b1 := (b.2 &&& a.1.1)==b.2
    let rest := ws.filter (fun w => w != a.1 && w != b.1)
    let base := cover rest
    let attempt (oka okb : Bool) (value : Unit → Word) :=
      (stay || (half && (oka || okb)) || (oka && okb)) &&
        (let z := value ()
         z != (0,0) && !(ws.contains z) &&
          ((oka && okb && (base ||| sep z)==all && next (z::rest)) ||
           (half && okb && next (z::a.1::rest)) ||
           (half && oka && next (z::b.1::rest)) ||
           (stay && next (z::a.1::b.1::rest))))
    attempt a1 b1 (fun _ => meet a.1 b.1) ||
      attempt a0 b0 (fun _ => join a.1 b.1) ||
      attempt a0 b1 (fun _ => skip a.1 b.1) ||
      attempt a1 b0 (fun _ => skip b.1 a.1)) cols

def guardedSearch : Nat → List Word → Bool
  | 0,ws => ws.contains target
  | k+1,ws => ws.contains target || guarded k (guardedSearch k) ws


def raw : List Word := [(0xaa1404600a0270047003878002808c017f84fc07ff0fffe0050138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff,0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a),(0xcc1807800c0380078003f8000300f00181ff3ff807f00ffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000,0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c),(0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00007fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff,0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0),(0xffe000000ffffff80000000003fffffe0007fffff800000007fffffc000003fff000000007ffffffffff000000003ffffffffc00000000,0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220),(0xfffffffff00000000000000003fffffffff800000000000007fffffffffffc000000000007ffffffffffffffffffc00000000000000000,0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0),(0xfffffffffffffffffffffffffc000000000000000000000007fffffffffffffffffffffff8000000000000000000000000000000000000,0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300),(0xfffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000,0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00)]
def four (k : Nat) (a b : Word) := match k with
  | 0 => meet a b | 1 => join a b | 2 => skip a b | _ => skip b a
def chk (j n : Nat) : Bool :=
  let g := join (raw.getD 0 (0,0)) (raw.getD j (0,0))
  let ws := g :: raw
  let ps := (List.range 8).flatMap fun i => ((List.range 8).filter fun h => decide (i<h)).map fun h => (i,h)
  let p := ps.getD (n/16) (0,1)
  let a := ws.getD p.1 (0,0)
  let b := ws.getD p.2 (0,0)
  let z := four ((n/4)%4) a b
  let rest := ws.filter fun x => x != a && x != b
  let next := match n%4 with
    | 0 => z::rest | 1 => z::a::rest | 2 => z::b::rest | _ => z::a::b::rest
  if z == (0,0) || ws.contains z || cover next != all then true else !(guardedSearch 9 next)
end SeedBenchmark
