import Mathlib

namespace CoLeafBudget4938
abbrev V := Fin 10
def near : V → V → Bool :=
  fun v u => ((![50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : V → Nat) v).testBit u.val

def count (f : V → Nat) := ((List.finRange 10).map f).sum
def isolated (S : V → Bool) : Bool :=
  (List.finRange 10).all fun v => (List.finRange 10).all fun u =>
    !(S v && S u && near v u)

def neighbors (S : V → Bool) (v : V) := (List.finRange 10).countP fun u => S u && near v u
def need (S : V → Bool) (v : V) := if S v then 1 else if 2≤neighbors S v then 3 else 2
def meets (S : V → Bool) := (List.finRange 10).all fun v => S v || decide (0<neighbors S v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finite_lower : ∀ S : V→Bool,isolated S=true → 18≤count (need S) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finite_tight : ∀ S : V→Bool,isolated S=true → count (need S)=18 →
    meets S=true ∧ 17≤count (fun v => if S v then 1 else 2) := by decide +kernel

theorem count_mono {f g : V→Nat} (h : ∀ v,f v≤g v) : count f≤count g := by
  change (List.map f (List.finRange 10)).sum ≤ (List.map g (List.finRange 10)).sum
  generalize List.finRange 10 = vs
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.map_cons,List.sum_cons]; exact Nat.add_le_add (h v) ih

theorem lower (m : V → Nat) (S : V→Bool) (ok : isolated S=true)
    (budget : ∀ v,need S v≤m v) : 18≤count m := (finite_lower S ok).trans (count_mono budget)

theorem tight (m : V → Nat) (S : V→Bool) (ok : isolated S=true)
    (budget : ∀ v,need S v≤m v) (upper : count m≤18) :
    meets S=true ∧ 17≤count (fun v => if S v then 1 else 2) := by
  exact finite_tight S ok (Nat.le_antisymm ((count_mono budget).trans upper) (finite_lower S ok))
end CoLeafBudget4938
