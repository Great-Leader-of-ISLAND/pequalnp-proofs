import PEqualNP.Co4358Shadow

namespace CoNum4358.Tiny
open CoAO3143

abbrev K := BitVec 15
abbrev W := K × PairFlag

def pack (f : Fin 160 → Bool) : B :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem pack_bit (f : Fin 160 → Bool) (i : Nat) (hi : i<160) :
    (pack f).getLsbD i = f ⟨i,hi⟩ := by
  rw [pack,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  have h : i<(List.ofFn f).length := by simpa only [List.length_ofFn] using hi
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

def wide (w : K) : Sig :=
  (pack fun i => w.getLsbD (i.val%56/7), pack fun i => w.getLsbD (8+i.val%7))

def lift (w : W) : AugWire := (wide w.1,w.2)

def pos (i : Fin 8) : Row := ⟨i.val*7,by omega⟩
def negRow (i : Fin 7) : Row := ⟨i.val,by omega⟩

theorem pos_bit (w : K) (i : Fin 8) : bit true (pos i) (wide w)=w.getLsbD i.val := by
  change (pack _).getLsbD (i.val*7)=_
  rw [pack_bit _ _ (by omega)]
  have sm : i.val*7<56 := by omega
  have P : (i.val*7)%56/7=i.val := by rw [Nat.mod_eq_of_lt sm]; omega
  exact congrArg (fun n => w.getLsbD n) P

theorem neg_bit (w : K) (i : Fin 7) : bit false (negRow i) (wide w)=w.getLsbD (8+i.val) := by
  change (pack _).getLsbD i.val=_
  rw [pack_bit _ _ (by omega)]
  simp [Nat.mod_eq_of_lt i.isLt]

theorem wide_inj : Function.Injective wide := by
  intro u v eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i<8
  · let j : Fin 8 := ⟨i,h⟩
    simpa only [pos_bit] using congrArg (bit true (pos j)) eq
  · let j : Fin 7 := ⟨i-8,by omega⟩
    have e := congrArg (bit false (negRow j)) eq
    rw [neg_bit,neg_bit] at e
    have val : 8+j.val=i := by dsimp [j]; omega
    rwa [val] at e

theorem lift_inj : Function.Injective lift := by
  intro x y eq
  exact Prod.ext (wide_inj (congrArg Prod.fst eq)) (congrArg Prod.snd eq)

def makeKW (d : Bool) (a b : K) : K := if d then a|||b else a&&&b

theorem wide_bin (d : Bool) (a b : K) : wide (makeKW d a b)=bin d (wide a) (wide b) := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;> cases d <;>
    simp only [wide,makeKW,bin,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_or,
      BitVec.getLsbD_and,pack_bit _ _ hj]

def make (d : Bool) (a b : W) : W := (makeKW d a.1 b.1,mergePair d a.2 b.2)

theorem lift_make (d : Bool) (a b : W) : lift (make d a b)=augGate d (lift a) (lift b) :=
  Prod.ext (wide_bin d a.1 b.1) rfl

def bare : List K := [18693,8715,7442,1952,5700,22568,24784]
def roots : List W := bare.zip rawPair
theorem bare_ground : bare.map wide=rawKW := by decide +kernel
theorem ground : roots.map lift=augRoots := by decide +kernel
theorem middle : wide 7442=twoKW := by decide +kernel
theorem zero_value : wide 0=zero := by decide +kernel
theorem one_value : wide 32767=CoAO3143.one := by decide +kernel
theorem target_value : wide 255=CoAO3143.target := by decide +kernel

def pay (d : Bool) (a b : W) := if d && (a.1==7442 || b.1==7442) then 1 else 0

theorem charge_eq (d : Bool) (a b : W) : pay d a b=augPay d (lift a) (lift b) := by
  have one (v : K) : (wide v==twoKW)=(v==7442) := by
    by_cases eq : v=7442
    · subst v; rw [middle]; simp
    · have neq : wide v≠twoKW := fun e => eq (wide_inj (e.trans middle.symm))
      simp [eq,neq]
  simp only [pay,augPay,lift,one]

def emit (w : W) : Nat := (w.1.toNat<<<4) ||| (w.2.2.original.toNat<<<3) |||
  (w.2.1.original.toNat<<<2) ||| (w.2.2.separates.toNat<<<1) ||| w.2.1.separates.toNat

def read (n : Nat) : W :=
  (BitVec.ofNat 15 (n>>>4),(⟨n.testBit 2,n.testBit 0⟩,⟨n.testBit 3,n.testBit 1⟩))

end CoNum4358.Tiny
