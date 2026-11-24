import Mathlib

namespace PEqualNP.Research.BadNeighborhood

variable {P L : Type*} [DecidableEq P] [DecidableEq L]

def edgeIn (I : P → L → Prop) (X : Finset P) (Y : Finset L) : Prop :=
  ∃ p ∈ X, ∃ l ∈ Y, I p l

def mono (F : Finset P → Finset L → Prop) : Prop :=
  ∀ ⦃X X' : Finset P⦄ ⦃Y Y' : Finset L⦄, X ⊆ X' → Y ⊆ Y' → F X Y → F X' Y'

theorem restrict_to_anticomplete (I : P → L → Prop) (A B : Finset P → Finset L → Prop)
    (ha : mono A) (hb : mono B) (spec : ∀ X Y, A X Y ∧ B X Y ↔ edgeIn I X Y)
    (U : Finset P) (V : Finset L) (hA : A U V) (hind : ¬ edgeIn I U V)
    (X : Finset P) (Y : Finset L) (h₁ : ¬ edgeIn I U Y) (h₂ : ¬ edgeIn I X V) :
    B X Y ↔ edgeIn I X Y := by
  refine ⟨?_, fun h => ((spec _ _).mpr h).2⟩
  intro hB
  have h1 : A (U ∪ X) (V ∪ Y) := ha Finset.subset_union_left Finset.subset_union_left hA
  have h2 : B (U ∪ X) (V ∪ Y) := hb Finset.subset_union_right Finset.subset_union_right hB
  obtain ⟨p, hp, l, hl, h⟩ := (spec _ _).mp ⟨h1,h2⟩
  rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hl with hl | hl
  · exact (hind ⟨p,hp,l,hl,h⟩).elim
  · exact (h₁ ⟨p,hp,l,hl,h⟩).elim
  · exact (h₂ ⟨p,hp,l,hl,h⟩).elim
  · exact ⟨p,hp,l,hl,h⟩

-- Count all incidences lost by removing points neighboring a set of lines.
-- Each marked line contributes at most one point for any different second line.
theorem incident_neighborhood_cost [Fintype P] [Fintype L]
    (I : P → L → Prop) [DecidableRel I] (U : Finset L)
    (unique : ∀ ⦃p q : P⦄ ⦃a b : L⦄, a ≠ b → I p a → I p b → I q a → I q b → p = q) :
    (Finset.univ.filter (fun e : P × L => I e.1 e.2 ∧ ∃ a ∈ U, I e.1 a)).card
      ≤ U.card * (Fintype.card P + Fintype.card L) := by
  classical
  let E := Finset.univ.filter (fun e : P × L => I e.1 e.2 ∧ ∃ a ∈ U, I e.1 a)
  have prop (e : ↥E) : I e.val.1 e.val.2 ∧ ∃ a ∈ U, I e.val.1 a :=
    (Finset.mem_filter.mp e.property).2
  let tag (e : ↥E) : ↥U := ⟨(prop e).2.choose, (prop e).2.choose_spec.1⟩
  have tagInc (e : ↥E) : I e.val.1 (tag e).val := (prop e).2.choose_spec.2
  let code (e : ↥E) : ↥U × (P ⊕ L) :=
    (tag e, if e.val.2 = (tag e).val then Sum.inl e.val.1 else Sum.inr e.val.2)
  have inj : Function.Injective code := by
    intro x y h
    have ht : tag x = tag y := congrArg Prod.fst h
    have hv := congrArg Prod.snd h
    change (if x.val.2 = (tag x).val then Sum.inl x.val.1 else Sum.inr x.val.2) =
      (if y.val.2 = (tag y).val then Sum.inl y.val.1 else Sum.inr y.val.2) at hv
    rw [← ht] at hv
    have hy : I y.val.1 (tag x).val := ht ▸ tagInc y
    apply Subtype.ext
    apply Prod.ext
    · split_ifs at hv with hx hy' hy'
      · exact Sum.inl.inj hv
      · cases hv
      · cases hv
      · have hl := Sum.inr.inj hv
        exact unique (Ne.symm hx) (tagInc x) (prop x).1 hy (hl ▸ (prop y).1)
    · split_ifs at hv with hx hy' hy'
      · exact hx.trans hy'.symm
      · cases hv
      · cases hv
      · exact Sum.inr.inj hv
  simpa only [Fintype.card_prod, Fintype.card_sum, Fintype.card_coe] using
    Fintype.card_le_of_injective code inj

end PEqualNP.Research.BadNeighborhood
