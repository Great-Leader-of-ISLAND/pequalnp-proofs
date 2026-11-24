import PEqualNP.CoBadNeighborhood

namespace PEqualNP.Research.AnchorReduction

open PEqualNP.Research.BadNeighborhood

variable {P L : Type*} [DecidableEq P] [DecidableEq L]

-- Every genuine error of the guarded factor can be realized at a singleton
-- marked input. The point set is held fixed during this reduction.
theorem one_mark {B : Finset P → Finset L → Prop} (bm : mono B)
    (small : ∀ X Y, B X Y → ∃ T ⊆ Y, T.card ≤ 1 ∧ B X T)
    {X : Finset P} {Y : Finset L} (hb : B X Y) (hy : Y.Nonempty) :
    ∃ l ∈ Y, B X {l} := by
  obtain ⟨T,sub,card,ht⟩ := small X Y hb
  by_cases h : T.Nonempty
  · obtain ⟨l, hl⟩ := h
    refine ⟨l,sub hl,bm (Finset.Subset.refl _) ?_ ht⟩
    intro t hmem
    exact Finset.mem_singleton.mpr (Finset.card_le_one.mp card t hmem l hl)
  · obtain ⟨l,hl⟩ := hy
    have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst T
    exact ⟨l,hl,bm (Finset.Subset.refl _) (Finset.empty_subset _) ht⟩

-- Each surviving line may use a completely different witness for the first
-- factor. Its number of points and the degree of that factor are unrestricted.
theorem exact_on_anchored_lines (I : P → L → Prop) (A B : Finset P → Finset L → Prop)
    (am : mono A) (bm : mono B) (spec : ∀ X Y, A X Y ∧ B X Y ↔ edgeIn I X Y)
    (small : ∀ X Y, B X Y → ∃ T ⊆ Y, T.card ≤ 1 ∧ B X T)
    (K J : Finset L)
    (anchor : ∀ l ∈ J, ∃ U : Finset P, A U K ∧ ¬ edgeIn I U K ∧ ¬ edgeIn I U {l})
    (X : Finset P) (Y : Finset L) (hK : ¬ edgeIn I X K) (hJ : Y ⊆ J) :
    (B X Y ∧ Y.Nonempty) ↔ edgeIn I X Y := by
  constructor
  · rintro ⟨hb,hy⟩
    obtain ⟨l,hl,hb'⟩ := one_mark bm small hb hy
    obtain ⟨U,ha,hn,hna⟩ := anchor l (hJ hl)
    obtain ⟨p,hp,a,ha',hadj⟩ :=
      (restrict_to_anticomplete I A B am bm spec U K ha hn X {l} hna hK).mp hb'
    obtain rfl := Finset.mem_singleton.mp ha'
    exact ⟨p,hp,_,hl,hadj⟩
  · intro h
    obtain ⟨p,hp,l,hl,hadj⟩ := h
    exact ⟨((spec X Y).mpr ⟨p,hp,l,hl,hadj⟩).2, l,hl⟩

-- If every small extension of the anchor remains rejected on its largest
-- independent point set, the first factor is exact on the entire restriction.
theorem exact_if_extensions_reject [Fintype P] (I : P → L → Prop) [DecidableRel I]
    (A B : Finset P → Finset L → Prop) (am : mono A)
    (spec : ∀ X Y, A X Y ∧ B X Y ↔ edgeIn I X Y) (r : ℕ)
    (small : ∀ X Y, A X Y → ∃ T ⊆ Y, T.card ≤ r ∧ A X T)
    (K J : Finset L)
    (reject : ∀ T ⊆ J, T.card ≤ r →
      ¬ A (Finset.univ.filter (fun p => ∀ l ∈ K ∪ T, ¬ I p l)) (K ∪ T))
    (X : Finset P) (Y : Finset L) (avoid : ¬ edgeIn I X K) (active : Y ⊆ J) :
    A X Y ↔ edgeIn I X Y := by
  refine ⟨?_, fun h => ((spec _ _).mpr h).1⟩
  intro ha
  by_contra hn
  obtain ⟨T,hT,hcard,ht⟩ := small X Y ha
  apply reject T (hT.trans active) hcard
  refine am ?_ Finset.subset_union_right ht
  intro p hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro l hl hpl
  rcases Finset.mem_union.mp hl with hk | ht
  · exact avoid ⟨p,hp,l,hk,hpl⟩
  · exact hn ⟨p,hp,l,hT ht,hpl⟩

end PEqualNP.Research.AnchorReduction
