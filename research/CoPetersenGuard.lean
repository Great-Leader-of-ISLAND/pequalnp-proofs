import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research.PetersenGuard

def graph (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def row (b : Bool) (m : Fin 256) (i : Fin 9) : Bool :=
  if i.val = 0 then b else m.val.testBit (i.val-1)

def sensitive (m : Fin 256) : Bool :=
  !graph (row false m) && graph (row true m)

set_option maxRecDepth 8000 in
theorem sensitive_count : (Finset.univ.filter (fun m : Fin 256 => sensitive m = true)).card = 32 := by
  decide +kernel

-- On a sensitive assignment the sole reader of the switching input cannot
-- have a controlling value on its other pin.
theorem sole_and_transmits {u v a : Bool} {post : Bool → Bool}
    (hs : post (u && a) ≠ post (v && a)) : a = true := by
  cases a <;> simp_all

theorem sole_or_transmits {u v a : Bool} {post : Bool → Bool}
    (hs : post (u || a) ≠ post (v || a)) : a = false := by
  cases a <;> simp_all

-- Both values of every remaining raw coordinate occur in that derivative.
set_option maxRecDepth 8000 in
theorem both_values : ∀ i : Fin 8, ∀ b : Bool,
    ∃ m : Fin 256, sensitive m = true ∧ m.val.testBit i.val = b := by
  decide +kernel

theorem signed_pin_cannot_be_constant (i : Fin 8) (b : Bool) :
    ¬ (∀ m : Fin 256, sensitive m = true → m.val.testBit i.val = b) := by
  intro h
  obtain ⟨m, hs, hv⟩ := both_values i (!b)
  have eq := (h m hs).symm.trans hv
  cases b <;> contradiction

end PEqualNP.Research.PetersenGuard
