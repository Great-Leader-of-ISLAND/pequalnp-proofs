import Mathlib.Data.Finset.Basic

namespace CoBankRepair3004

theorem remove_edge_term {X : Type} (f h edge : X → Bool) (context : X → Bool → Bool)
    (safe : ∀ x, edge x=true → f x=true) (original : ∀ x, context x (h x || edge x)=f x) :
    ∀ x, (context x (h x) || edge x)=f x := by
  intro x
  cases e : edge x with
  | false => simpa only [e,Bool.or_false] using original x
  | true => simp only [Bool.or_true,safe x e]

theorem replacement {X : Type} (f z v patch : X → Bool) (context : X → Bool → Bool)
    (mono : ∀ x, context x false=true → context x true=true)
    (original : ∀ x, context x (z x)=f x)
    (negative : ∀ x, f x=false → v x=true → z x=true)
    (missing : ∀ x, f x=true → z x=true → v x=false → patch x=true)
    (sound : ∀ x, patch x=true → f x=true) :
    ∀ x, (context x (v x) || patch x)=f x := by
  intro x
  have old := original x
  cases F : f x with
  | false =>
    have pa : patch x=false := Bool.eq_false_iff.mpr fun hx => Bool.noConfusion ((sound x hx).symm.trans F)
    simp only [pa,Bool.or_false]
    cases V : v x with
    | false =>
      apply Bool.eq_false_iff.mpr
      intro h
      cases Z : z x with
      | false => simp only [Z,F] at old; exact Bool.noConfusion (h.symm.trans old)
      | true => simp only [Z,F] at old; exact Bool.noConfusion ((mono x h).symm.trans old)
    | true => simpa only [negative x F V,F] using old
  | true =>
    cases V : v x with
    | false =>
      cases Z : z x with
      | true => simp only [missing x F Z V,Bool.or_true]
      | false => simp only [Z,F] at old; simp only [old,Bool.true_or]
    | true =>
      have res : context x true=true := by
        cases Z : z x with
        | false => exact mono x (by simpa only [Z,F] using old)
        | true => simpa only [Z,F] using old
      simp only [res,Bool.true_or]

-- A binary formula for disjointly assigned stars uses one leaf per
-- edge and one leaf per nonempty star. Joining it to the modified suffix
-- costs the same number of gates as the patch has leaves.
theorem repair_budget (construction suffix cheaper correction : Nat)
    (h : cheaper+correction≤construction) : cheaper+suffix+correction≤construction+suffix := by
  omega

#print axioms replacement
end CoBankRepair3004
