import Mathlib

namespace PEqualNP.Research.FactorSlice

variable {P L : Type*} [DecidableEq P] [DecidableEq L]

def hit (I : P → L → Prop) (X : Finset P) (Y : Finset L) : Prop :=
  ∃ p ∈ X, ∃ l ∈ Y, I p l

def inc (F : Finset P → Finset L → Prop) : Prop :=
  ∀ ⦃X X' : Finset P⦄ ⦃Y Y' : Finset L⦄, X ⊆ X' → Y ⊆ Y' → F X Y → F X' Y'

-- A root AND may choose its exact factor separately for each entire point set.
theorem exact_on_each_slice [Fintype L] (I : P → L → Prop)
    (A B : Finset P → Finset L → Prop) (am : inc A) (bm : inc B)
    (spec : ∀ X Y, A X Y ∧ B X Y ↔ hit I X Y) (X : Finset P) :
    (∀ Y, A X Y ↔ hit I X Y) ∨ (∀ Y, B X Y ↔ hit I X Y) := by
  classical
  let miss := Finset.univ.filter fun l : L => ∀ p ∈ X, ¬ I p l
  have sub : ∀ Y, ¬ hit I X Y → Y ⊆ miss := by
    intro Y hn l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp h => hn ⟨p,hp,l,hl,h⟩⟩
  have neg : ¬ hit I X miss := by
    rintro ⟨p,hp,l,hl,hi⟩
    exact (Finset.mem_filter.mp hl).2 p hp hi
  by_cases h : A X miss
  · right
    intro Y
    refine ⟨?_, fun e => ((spec _ _).mpr e).2⟩
    intro hb
    by_contra hn
    exact neg ((spec _ _).mp ⟨h, bm (Finset.Subset.refl _) (sub _ hn) hb⟩)
  · left
    intro Y
    refine ⟨?_, fun e => ((spec _ _).mpr e).1⟩
    intro ha
    by_contra hn
    exact h (am (Finset.Subset.refl _) (sub _ hn) ha)

-- Add one independently false row to a positive witness of the other factor.
private theorem force_mark (I : P → L → Prop) (A B : Finset P → Finset L → Prop)
    (am : inc A) (bm : inc B) (spec : ∀ X Y, A X Y ∧ B X Y ↔ hit I X Y)
    (p : P) (U : Finset L) (X : Finset P) (T : Finset L)
    (ha : A {p} U) (hb : B X T) (hu : ∀ l ∈ U, ¬ I p l)
    (hx : ∀ q ∈ X, ∀ l ∈ U, ¬ I q l) (hn : ¬ hit I X T) :
    ∃ l ∈ T, I p l := by
  have hA : A ({p} ∪ X) (U ∪ T) := am Finset.subset_union_left Finset.subset_union_left ha
  have hB : B ({p} ∪ X) (U ∪ T) := bm Finset.subset_union_right Finset.subset_union_right hb
  obtain ⟨q,hq,l,hl,h⟩ := (spec _ _).mp ⟨hA,hB⟩
  rcases Finset.mem_union.mp hq with hq | hq
  · obtain rfl := Finset.mem_singleton.mp hq
    rcases Finset.mem_union.mp hl with hU | hT
    · exact (hu l hU h).elim
    · exact ⟨l,hT,h⟩
  · rcases Finset.mem_union.mp hl with hU | hT
    · exact (hx q hq l hU h).elim
    · exact (hn ⟨q,hq,l,hT,h⟩).elim

-- Two erroneous singleton-point rows force a degree-one factor to compute
-- the remaining incidence function, including inputs with many points and lines.
theorem two_bad_rows (I : P → L → Prop) (A B : Finset P → Finset L → Prop)
    (am : inc A) (bm : inc B) (spec : ∀ X Y, A X Y ∧ B X Y ↔ hit I X Y)
    (small : ∀ X Y, B X Y → ∃ T ⊆ Y, T.card ≤ 1 ∧ B X T)
    (p r : P) (U V : Finset L) (hp : A {p} U) (hr : A {r} V)
    (hu : ∀ l ∈ U, ¬ I p l) (hv : ∀ l ∈ V, ¬ I r l)
    (X : Finset P) (Y : Finset L)
    (avoid : ∀ q ∈ X, ∀ l ∈ U ∪ V, ¬ I q l)
    (common : ∀ l ∈ Y, ¬ (I p l ∧ I r l)) :
    B X Y ↔ hit I X Y := by
  refine ⟨?_, fun h => ((spec _ _).mpr h).2⟩
  intro hb
  by_contra hn
  obtain ⟨T, hT, hcard, hbt⟩ := small X Y hb
  have hne : ¬ hit I X T := by
    rintro ⟨q,hq,l,hl,hi⟩
    exact hn ⟨q,hq,l,hT hl,hi⟩
  obtain ⟨a, ha, hpa⟩ := force_mark I A B am bm spec p U X T hp hbt hu
    (fun q hq l hl => avoid q hq l (Finset.mem_union_left _ hl)) hne
  obtain ⟨b, hbb, hrb⟩ := force_mark I A B am bm spec r V X T hr hbt hv
    (fun q hq l hl => avoid q hq l (Finset.mem_union_right _ hl)) hne
  have he := Finset.card_le_one.mp hcard a ha b hbb
  exact common a (hT ha) ⟨hpa, he.symm ▸ hrb⟩

end PEqualNP.Research.FactorSlice
