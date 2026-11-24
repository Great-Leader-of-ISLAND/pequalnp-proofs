import PEqualNP.CoFormula1963Shapes

namespace CoFormula1963Packed
open CoFormula1963Area

/-- Finite helper facts on nibbles allow the semantic proof to inspect just
    the four real rows. No appeal to any bit numbered four or above is needed. -/
theorem or_small : ∀ a b : Fin 16, a.val ||| b.val < 16 := by decide +kernel
theorem and_zero : ∀ a b : Fin 16, (∀ i : Fin 4, a.val.testBit i = true →
    b.val.testBit i = false) → a.val &&& b.val = 0 := by decide +kernel

def cnt {R : Type*} (m : R → ℕ) (active : R → Bool) (xs : List R) (i : Fin 4) : ℕ :=
  (xs.map fun r => if active r && (m r).testBit i then 1 else 0).sum

theorem test_count {R : Type*} (m : R → ℕ) (active : R → Bool) (xs : List R) (i : Fin 4) :
    (unionAt m active xs).testBit i = true ↔ 0 < cnt m active xs i := by
  induction xs with
  | nil => simp [unionAt,cnt]
  | cons x xs ih =>
    change _ ↔ 0 < (if active x && (m x).testBit i then 1 else 0) + cnt m active xs i
    cases a : active x <;> cases b : (m x).testBit i <;> simp [unionAt,a,b,Nat.testBit_or,ih]

theorem union_small {R : Type*} (m : R → ℕ) (active : R → Bool) (xs : List R)
    (valid : ∀ r ∈ xs, m r < 16) : unionAt m active xs < 16 := by
  induction xs with
  | nil => change 0 < 16; decide
  | cons x xs ih =>
    have hm := valid x (by simp)
    have ht := ih (fun r hr => valid r (List.mem_cons_of_mem _ hr))
    cases a : active x with
    | false => simpa [unionAt,a] using ht
    | true => simpa [unionAt,a] using or_small ⟨m x,hm⟩ ⟨unionAt m active xs,ht⟩

/-- This version keeps all instances of the original leaf list, even equal
    empty rectangles. Multiplicity at most one directly gives the disjoint
    union rule, without requiring a list with no duplicate rectangle values. -/
theorem from_cells {R : Type*} (m : R → ℕ) (active : R → Bool) (xs : List R)
    (valid : ∀ r ∈ xs, m r < 16) (limAll : ∀ i : Fin 4, cnt m active xs i ≤ 1) :
    Selection (xs.map m) (unionAt m active xs) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    have head (i : Fin 4) : (if active x && (m x).testBit i then 1 else 0) +
        cnt m active xs i ≤ 1 := limAll i
    have tail : ∀ i : Fin 4, cnt m active xs i ≤ 1 := fun i => by have h := head i; omega
    have vr : ∀ r ∈ xs, m r < 16 := fun r hr => valid r (List.mem_cons_of_mem _ hr)
    have rest := ih vr tail
    cases a : active x with
    | false => simpa [unionAt,a] using Selection.skip (m x) rest
    | true =>
      have dis := and_zero ⟨unionAt m active xs,union_small m active xs vr⟩
        ⟨m x,valid x (by simp)⟩
      have z : unionAt m active xs &&& m x = 0 := dis fun i hi => by
        have pos := (test_count m active xs i).mp hi
        have lim := head i
        cases b : (m x).testBit i with
        | false => rfl
        | true => simp [a,b] at lim; omega
      simpa [unionAt,a,Nat.or_comm] using Selection.take rest z

#print axioms from_cells
end CoFormula1963Packed
