import Mathlib

namespace PEqualNP.Research.TouchedEdges

-- Square-freeness bounds the total degree of an arbitrary k selected points
-- by the number of lines plus k squared, even for highly irregular systems.
theorem bound {P L : Type*} [DecidableEq P] [DecidableEq L] [Fintype P] [Fintype L]
    (I : P → L → Prop) [DecidableRel I] (U : Finset P)
    (single : ∀ ⦃p q : P⦄ ⦃a b : L⦄, p ≠ q → I p a → I q a → I p b → I q b → a=b) :
    (Finset.univ.filter (fun e : ↥U × L => I e.1.val e.2)).card ≤
      Fintype.card L + U.card * U.card := by
  classical
  let E := Finset.univ.filter (fun e : ↥U × L => I e.1.val e.2)
  let T := Finset.univ.filter (fun l : L => ∃ p : ↥U, I p.val l)
  have adj (e : ↥E) : I e.val.1.val e.val.2 := (Finset.mem_filter.mp e.property).2
  let line (e : ↥E) : ↥T :=
    ⟨e.val.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.val.1,adj e⟩⟩
  have hasRoot (l : ↥T) : ∃ p : ↥U, I p.val l.val := (Finset.mem_filter.mp l.property).2
  let root (l : ↥T) : ↥U := (hasRoot l).choose
  have rootAdj (e : ↥E) : I (root (line e)).val e.val.2 := (hasRoot (line e)).choose_spec
  let f (e : ↥E) : L ⊕ (↥U × ↥U) :=
    if e.val.1 = root (line e) then Sum.inl e.val.2 else Sum.inr (e.val.1,root (line e))
  have inject : Function.Injective f := by
    intro x y hh
    change (if x.val.1 = root (line x) then Sum.inl x.val.2 else Sum.inr (x.val.1,root (line x))) =
      (if y.val.1 = root (line y) then Sum.inl y.val.2 else Sum.inr (y.val.1,root (line y))) at hh
    by_cases hx : x.val.1 = root (line x)
    · rw [if_pos hx] at hh
      by_cases hy : y.val.1 = root (line y)
      · rw [if_pos hy] at hh
        have hl := Sum.inl.inj hh
        have e : line x = line y := Subtype.ext hl
        exact Subtype.ext (Prod.ext (hx.trans ((congrArg root e).trans hy.symm)) hl)
      · rw [if_neg hy] at hh
        cases hh
    · rw [if_neg hx] at hh
      by_cases hy : y.val.1 = root (line y)
      · rw [if_pos hy] at hh
        cases hh
      · rw [if_neg hy] at hh
        have eqp := Sum.inr.inj hh
        have hp : x.val.1 = y.val.1 := congrArg (fun z : ↥U × ↥U => z.1) eqp
        have hr : root (line x) = root (line y) := congrArg (fun z : ↥U × ↥U => z.2) eqp
        have hdiff : x.val.1.val ≠ (root (line x)).val := fun he => hx (Subtype.ext he)
        have hyr : I (root (line x)).val y.val.2 := hr.symm ▸ rootAdj y
        have hyp : I x.val.1.val y.val.2 := hp.symm ▸ adj y
        exact Subtype.ext (Prod.ext hp (single hdiff (adj x) (rootAdj x) hyp hyr))
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_coe] using
    Fintype.card_le_of_injective f inject

end PEqualNP.Research.TouchedEdges
