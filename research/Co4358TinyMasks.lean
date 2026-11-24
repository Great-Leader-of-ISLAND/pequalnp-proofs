import PEqualNP.Co4358TinyRect
namespace CoNum4358.Tiny.Masks
open CoAO3143
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def posMask (x : Nat) :=
  let u := (x ||| (x<<<24)) &&& 0xf000000f
  let u := (u ||| (u<<<12)) &&& 0xc003000c003
  ((u ||| (u<<<6)) &&& columnMask)*127

def negMask (x : Nat) := fullMask ^^^ (x*columnMask)

theorem pos_bits : ∀ (x : Fin 256) (p : Fin 8) (n : Fin 7),
    (posMask x.val).testBit (p.val*7+n.val)=x.val.testBit p.val := by decide +kernel

theorem neg_bits : ∀ (x : Fin 128) (p : Fin 8) (n : Fin 7),
    (negMask x.val).testBit (p.val*7+n.val)= !(x.val.testBit n.val) := by decide +kernel

theorem cells_bit (w : K) (p : Fin 8) (n : Fin 7) :
    (cells w).testBit (p.val*7+n.val)=directed w p n := by
  have loEq : (w.toNat &&& 255)=w.toNat%2^8 := Nat.and_two_pow_sub_one_eq_mod _ 8
  let lo : Fin 256 := ⟨w.toNat%2^8,Nat.mod_lt _ (by decide)⟩
  have high : w.toNat>>>8<128 := by
    rw [Nat.shiftRight_eq_div_pow]
    have lim : w.toNat<32768 := w.isLt
    omega
  let hi : Fin 128 := ⟨w.toNat>>>8,high⟩
  change ((posMask (w.toNat &&& 255) &&& negMask (w.toNat>>>8)).testBit _)=_
  rw [loEq]
  change ((posMask lo.val &&& negMask hi.val).testBit _)=_
  rw [Nat.testBit_and,pos_bits,neg_bits]
  change ((w.toNat%2^8).testBit p.val && !(w.toNat>>>8).testBit n.val)=_
  simp only [directed,BitVec.getLsbD,Nat.testBit_mod_two_pow,p.isLt,decide_true,
    Bool.true_and,Nat.testBit_shiftRight]

def used : List W → Nat
  | [] => 0
  | w::ws => cells w.1 ||| used ws

theorem used_bit (ws : List W) (p : Fin 8) (n : Fin 7) :
    (used ws).testBit (p.val*7+n.val)=
    (unionSep false ((ws.map Prod.fst).map wide)).getLsbD (p.val*7+n.val) := by
  induction ws with
  | nil => simp [used,unionSep]
  | cons w ws ih =>
    simp only [used,Nat.testBit_or,cells_bit,List.map_cons,unionSep,BitVec.getLsbD_or,
      joint_bit,ih]

def complete (mask : Nat) := (mask &&& fullMask)==fullMask

theorem needed {k : Nat} {ws : List W} (h : Live k 0 ((ws.map Prod.fst).map wide).toFinset) :
    complete (used ws)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  have mask : fullMask.testBit i=decide (i<56) := Nat.testBit_two_pow_sub_one 56 i
  rw [Nat.testBit_and,mask]
  by_cases hi : i<56
  · let p : Fin 8 := ⟨i/7,by omega⟩
    let n : Fin 7 := ⟨i%7,Nat.mod_lt _ (by decide)⟩
    have eq : p.val*7+n.val=i := by dsimp [p,n]; omega
    have cov : unionSep false ((ws.map Prod.fst).map wide)=top := live_cover h rfl
    have hit := used_bit ws p n
    have bd : i<160 := by omega
    rw [eq,cov] at hit
    simp only [top,BitVec.getLsbD_allOnes,bd,decide_true] at hit
    simp [hi,hit]
  · simp [hi]

end CoNum4358.Tiny.Masks
