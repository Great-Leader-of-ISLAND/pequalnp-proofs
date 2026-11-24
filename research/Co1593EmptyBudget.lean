import PEqualNP.Defs

namespace Co1593EmptyBudget

open Finset

variable {W : Type*} [DecidableEq W]

structure Step (W : Type*) where
  out : W
  left : W
  right : W
  deriving DecidableEq

def before (g : Step W) (seen : Finset W) :=
  if g.out∈seen then insert g.left (insert g.right (seen.erase g.out)) else seen

def emptyCount (empty : W→Bool) (seen : Finset W) :=
  (seen.filter (fun w => empty w=true)).card

def birth (e : W→Bool) (g : Step W) (seen : Finset W) : Nat :=
  if g.out∈seen ∧ e g.out=true ∧ e g.left=false ∧ e g.right=false then 1 else 0

def other (e : W→Bool) (g : Step W) : Nat :=
  if e g.left || e g.right then 1 else 0

private lemma add_bound (e : W→Bool) (a : W) (s : Finset W) :
    emptyCount e (insert a s) ≤ emptyCount e s + (if e a then 1 else 0) := by
  cases h : e a
  · simp [emptyCount, Finset.filter_insert, h]
  · simpa [emptyCount, Finset.filter_insert, h] using
      Finset.card_insert_le a (s.filter fun w => e w=true)

private lemma erase_balance (e : W→Bool) (a : W) (s : Finset W) (ha : a∈s) :
    emptyCount e (s.erase a) + (if e a then 1 else 0) = emptyCount e s := by
  cases h : e a
  · have eq : (s.erase a).filter (fun w => e w=true) = s.filter (fun w => e w=true) := by
      ext x
      by_cases ax : x=a <;> simp [ax,h]
    simp [emptyCount,h,eq]
  · have eq : (s.erase a).filter (fun w => e w=true) = (s.filter (fun w => e w=true)).erase a := by
      ext x
      simp [and_assoc,and_comm,and_left_comm]
    have hit : a ∈ s.filter (fun w => e w=true) := Finset.mem_filter.mpr ⟨ha,h⟩
    simpa [emptyCount,h,eq] using Finset.card_erase_add_one hit

/-- Reverse one reachable AND/OR gate. A pair of empty inputs always yields an empty output. -/
theorem local_balance (e : W→Bool) (g : Step W) (seen : Finset W)
    (both : e g.left=true → e g.right=true → e g.out=true) :
    emptyCount e (before g seen) + birth e g seen ≤ emptyCount e seen + other e g := by
  by_cases hit : g.out∈seen
  · have l := add_bound e g.left (insert g.right (seen.erase g.out))
    have r := add_bound e g.right (seen.erase g.out)
    have z := erase_balance e g.out seen hit
    cases el : e g.left <;> cases er : e g.right <;> cases eo : e g.out <;>
      simp_all [before,other,birth] <;> omega
  · simp [before,hit,birth]

def births (e : W→Bool) : List (Step W) → Finset W → Nat
  | [],_ => 0
  | g::gs,seen => birth e g seen + births e gs (before g seen)

/-- One final wire can collect at most one more active generator than the number of
    remaining gates with at least one empty input. The list is in reverse circuit order. -/
theorem global_balance (e : W→Bool) (gs : List (Step W)) (seen : Finset W)
    (both : ∀ g∈gs,e g.left=true → e g.right=true → e g.out=true) :
    births e gs seen ≤ emptyCount e seen + (gs.map (other e)).sum := by
  induction gs generalizing seen with
  | nil => simp [births]
  | cons g gs ih =>
    have l := local_balance e g seen (both g List.mem_cons_self)
    have h := ih (before g seen) (fun g' hg => both g' (List.mem_cons_of_mem _ hg))
    simp only [births,List.map_cons,List.sum_cons]
    omega

theorem one_output (e : W→Bool) (gs : List (Step W)) (out : W)
    (both : ∀ g∈gs,e g.left=true → e g.right=true → e g.out=true) :
    births e gs {out} ≤ (gs.map (other e)).sum+1 := by
  have h := global_balance e gs {out} both
  have one : emptyCount e {out} ≤ 1 := by
    simpa [emptyCount] using (Finset.card_filter_le (s:=({out}:Finset W)) (fun w => e w=true))
  omega

end Co1593EmptyBudget
