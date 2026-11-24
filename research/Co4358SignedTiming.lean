import Mathlib
import PEqualNP.Defs

namespace Co4358Timing

structure Wr where
  w : ℕ
  s : ℕ
  f : ℕ

def sepN (L w : ℕ) : ℕ := Nat.land (Nat.xor w (Nat.shiftRight w 143)) L

def covL : List Wr → ℕ
  | [] => 0
  | a :: l => Nat.lor a.s (covL l)

def flL : List Wr → ℕ
  | [] => 0
  | a :: l => Nat.lor a.f (flL l)

def lenL : List Wr → ℕ
  | [] => 0
  | _ :: l => Nat.succ (lenL l)

def absentL (g : ℕ) : List Wr → Bool
  | [] => true
  | x :: l => cond (Nat.beq x.w g) false (absentL g l)

def app : List Wr → List Wr → List Wr
  | [], m => m
  | a :: l, m => a :: app l m

def sub (a b : ℕ) : Bool := Nat.beq (Nat.land a b) a

def force (x : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun n _ => f (Nat.succ n)) x

abbrev Next := List Wr → ℕ → ℕ → ℕ → ℕ → Bool

def tryG (L : ℕ) (r : Next) (k m : ℕ) (rest : List Wr) (cr c1 c2 c3 : ℕ) (a b : Wr) (last : ℕ)
    (uses : Bool) (g fg : ℕ) : Bool :=
  cond (Nat.beq g 0) false (cond (Nat.beq g a.w) false (cond (Nat.beq g b.w) false
    (cond (cond uses true (Nat.ble last g))
      (cond (sub fg c1)
        (force (sepN L g) fun sg =>
          force (Nat.lor cr sg) fun base =>
            (cond (Nat.beq base L) (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: rest) c1 c2 c3 g) false)
              false) ||
            (cond (Nat.ble m (Nat.succ k))
              ((cond (sub a.f c1) (cond (Nat.beq (Nat.lor base a.s) L)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: a :: rest) c1 c2 c3 g) false) false) false) ||
               (cond (sub b.f c1) (cond (Nat.beq (Nat.lor base b.s) L)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: b :: rest) c1 c2 c3 g) false) false) false) ||
               (cond (Nat.ble m k) (cond (sub a.f c1) (cond (sub b.f c1)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: a :: b :: rest) c1 c2 c3 g) false) false)
                  false) false))
              false))
        false)
      false)))

def plainP (L : ℕ) (r : Next) (k m c1 c2 c3 last : ℕ) (a b : Wr) (rest : List Wr) : Bool :=
  force (Nat.lor a.f b.f) fun K =>
    cond (sub K c1)
      (force (Nat.lor c2 (Nat.xor c1 (Nat.land c1 K))) fun d1 =>
       force (Nat.lor c3 (Nat.xor c2 (Nat.land c2 K))) fun d2 =>
       force (Nat.xor c3 (Nat.land c3 K)) fun d3 =>
        cond (sub (flL rest) d1)
          (force (covL rest) fun cr =>
            force (Nat.land a.w b.w) fun ab =>
              tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last) ab K ||
              (tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.lor a.w b.w) (Nat.land a.f b.f) ||
              (tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.xor a.w ab) a.f ||
              tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.xor b.w ab) b.f)))
          false)
      false

def ownSide (s other cr : ℕ) : ℕ :=
  Nat.xor s (Nat.land s (Nat.lor other cr))

def leftNeed (t : Fin 4) : Bool :=
  match t with
  | 0 => true
  | 1 => false
  | 2 => false
  | 3 => true

def rightNeed (t : Fin 4) : Bool :=
  match t with
  | 0 => true
  | 1 => false
  | 2 => true
  | 3 => false

def agreePart (want : Bool) (masked original : ℕ) :=
  if want then Nat.beq masked original else Nat.beq masked 0

def canUse (t : Fin 4) (loose : Bool) (ua ub pa pb : ℕ) :=
  loose || (agreePart (leftNeed t) pa ua && agreePart (rightNeed t) pb ub)

def withCheck (b : Bool) (act : Unit → Bool) := cond b (act ()) false


def tryP (L : ℕ) (r : Next) (k m c1 c2 c3 last : ℕ) (a b : Wr) (rest : List Wr) : Bool :=
  if Nat.ble m (Nat.succ k) then plainP L r k m c1 c2 c3 last a b rest else
  force (Nat.lor a.f b.f) fun K =>
    cond (sub K c1)
      (force (Nat.lor c2 (Nat.xor c1 (Nat.land c1 K))) fun d1 =>
       force (Nat.lor c3 (Nat.xor c2 (Nat.land c2 K))) fun d2 =>
       force (Nat.xor c3 (Nat.land c3 K)) fun d3 =>
        cond (sub (flL rest) d1)
          (force (covL rest) fun cr =>
            force (ownSide a.s b.s cr) fun ua =>
            force (ownSide b.s a.s cr) fun ub =>
            force (Nat.land ua b.w) fun pa =>
            force (Nat.land ub a.w) fun pb =>
            let ok (t : Fin 4) := canUse t (Nat.ble m (Nat.succ k)) ua ub pa pb
            let uses := Nat.beq a.w last || Nat.beq b.w last
            let go := tryG L r k m rest cr d1 d2 d3 a b last uses
            (withCheck (ok 0) fun _ => go (Nat.land a.w b.w) K) ||
            ((withCheck (ok 1) fun _ => go (Nat.lor a.w b.w) (Nat.land a.f b.f)) ||
            ((withCheck (ok 2) fun _ => go (Nat.xor a.w (Nat.land a.w b.w)) a.f) ||
             (withCheck (ok 3) fun _ => go (Nat.xor b.w (Nat.land a.w b.w)) b.f))))
          false)
      false

def pairsB (a : Wr) : List Wr → List Wr → List (Wr × Wr × List Wr)
  | _, [] => []
  | acc, b :: l => (a, b, app acc l) :: pairsB a (b :: acc) l

def pairsA : List Wr → List Wr → List (Wr × Wr × List Wr)
  | _, [] => []
  | acc, a :: l => pairsB a acc l ++ pairsA (a :: acc) l

def anyP (p : Wr → Wr → List Wr → Bool) : List (Wr × Wr × List Wr) → Bool
  | [] => false
  | x :: l => p x.1 x.2.1 x.2.2 || anyP p l

def isT (y : ℕ) : List Wr → Bool
  | [a] => Nat.beq a.w y
  | _ => false

def search (L y : ℕ) : ℕ → Next
  | 0, v, _, _, _, _ => isT y v
  | k + 1, v, c1, c2, c3, last =>
    isT y v || anyP (tryP L (search L y k) k (lenL v) c1 c2 c3 last) (pairsA [] v)

def originalSearch (L y : ℕ) : ℕ → Next
  | 0, v, _, _, _, _ => isT y v
  | k + 1, v, c1, c2, c3, last =>
    isT y v || anyP (plainP L (originalSearch L y k) k (lenL v) c1 c2 c3 last) (pairsA [] v)

def LO : ℕ := 0x7fffffffffffffffffffffffffffffffffff

def kv17 : List Wr := [⟨0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f, 0x6b29aca6b28535800000b03620c010005005, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 144⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 264⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 129⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 288⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

end Co4358Timing
