import Init

namespace CoThetaTransfer

def panel (p q : Bool) : Bool × Bool × Bool :=
  -- Other primaries are respectively all zero, just x1, and just x3.
  (p && q, (p && q) || p, (p && q) || q)

theorem three_bits_collide : ∀ a b c : Bool, a = b ∨ a = c ∨ b = c := by decide

/-- No other scalar wire can complement the fixed OR head to convey both endpoints. -/
theorem no_second_scalar (wire : Bool → Bool → Bool)
    (read : Bool → Bool → Bool × Bool × Bool) :
    ¬ ∀ p q, read (p || q) (wire p q) = panel p q := by
  intro h
  have a : read true (wire false true) = (false,false,true) := h false true
  have b : read true (wire true false) = (false,true,false) := h true false
  have c : read true (wire true true) = (true,true,true) := h true true
  rcases three_bits_collide (wire false true) (wire true false) (wire true true) with ab | ac | bc
  · rw [ab] at a
    exact (show (false,false,true) ≠ (false,true,false) by decide) (a.symm.trans b)
  · rw [ac] at a
    exact (show (false,false,true) ≠ (true,true,true) by decide) (a.symm.trans c)
  · rw [bc] at b
    exact (show (false,true,false) ≠ (true,true,true) by decide) (b.symm.trans c)

end CoThetaTransfer
