import Mathlib
import PEqualNP.MetaComplexity.Helpers.Support
import PEqualNP.Defs

namespace PEqualNP.Research.DiagonalInputs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def read {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem joint_budget {n J : ℕ} (C : Circuit) (hm : Monotone2 C)
    (a b : Fin J → ℕ) (T : Finset (Fin n))
    (sensitive : ∀ i ∈ T, ∃ (j : Fin J) (x y : Fin n → Bool),
      (∀ k, k ≠ i → x k = y k) ∧
      (read C (a j) x = true ∧ read C (b j) x = true) ∧
      ¬ (read C (a j) y = true ∧ read C (b j) y = true)) :
    T.card ≤ C.size + 2 * J := by
  classical
  let W := Finset.univ.image a ∪ Finset.univ.image b
  let supports := Helpers.suppsFrom C.gates (Helpers.inputSupps n)
  let S := W.biUnion fun w => supports.getD w ∅
  have ok : ∀ g ∈ C.gates, Helpers.Ok g := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hm g hg
    refine ⟨?_,hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    tauto
  have inS : T ⊆ S := by
    intro i hi
    by_contra outside
    obtain ⟨j,x,y,eq,yes,no⟩ := sensitive i hi
    have same (w : ℕ) (hw : w ∈ W) : read C w x = read C w y := by
      apply (Helpers.agree_wiresFrom x y C.gates _ _ _ (Helpers.agree_inputs x y)).2.2 w
      intro k hk
      apply eq
      rintro rfl
      exact outside (Finset.mem_biUnion.mpr ⟨w,hw,hk⟩)
    have ha : a j ∈ W := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
    have hb : b j ∈ W := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
    exact no ⟨(same _ ha).symm.trans yes.1,(same _ hb).symm.trans yes.2⟩
  have bound := Helpers.cnt_suppsFrom C.gates 0 (Helpers.inputSupps n) ok Helpers.cnt_inputs W
  change S.card ≤ 0 + C.gates.length + W.card at bound
  have wc := Finset.card_union_le (Finset.univ.image a) (Finset.univ.image b)
  have ca : (Finset.univ.image a).card ≤ J := by simpa using (Finset.card_image_le (s := Finset.univ) (f := a))
  have cb : (Finset.univ.image b).card ≤ J := by simpa using (Finset.card_image_le (s := Finset.univ) (f := b))
  change W.card ≤ _ at wc
  have hsub := Finset.card_le_card inS
  change T.card ≤ C.gates.length + 2*J
  omega

end PEqualNP.Research.DiagonalInputs
