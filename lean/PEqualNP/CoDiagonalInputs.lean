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


private def pair (N : ℕ) (p l : Fin N) (v : Fin (N+N)) : Bool :=
  decide (v = Fin.castAdd N p ∨ v = Fin.natAdd N l)

private def singleton {n : ℕ} (p v : Fin n) : Bool := decide (v=p)

private theorem split_ne {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro eq
  have hh := congrArg Fin.val eq
  change p.val = N + l.val at hh
  omega

theorem incident_endpoints {N J : ℕ} (C : Circuit) (hm : Monotone2 C)
    (I : Fin N → Fin N → Prop) (a b : Fin J → ℕ) (T : Finset (Fin N × Fin N))
    (hit : ∀ e ∈ T, ∃ j, read C (a j) (pair N e.1 e.2) = true ∧
      read C (b j) (pair N e.1 e.2) = true)
    (sound : ∀ j (x : Fin (N+N) → Bool), read C (a j) x = true → read C (b j) x = true →
      ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) :
    (T.biUnion (fun e => ({Fin.castAdd N e.1, Fin.natAdd N e.2} : Finset (Fin (N+N))))).card
      ≤ C.size + 2*J := by
  classical
  apply joint_budget C hm a b
  intro i hi
  obtain ⟨e,he,hi⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨j,hj⟩ := hit e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with h | h
  · subst i
    refine ⟨j, pair N e.1 e.2, singleton (Fin.natAdd N e.2), ?_, hj, ?_⟩
    · intro v hv
      simp only [pair, singleton, hv, false_or, or_false]
    · rintro ⟨ha,hb⟩
      obtain ⟨p,l,hI,hp,hl⟩ := sound j _ ha hb
      exact split_ne p e.2 (of_decide_eq_true hp)
  · subst i
    refine ⟨j, pair N e.1 e.2, singleton (Fin.castAdd N e.1), ?_, hj, ?_⟩
    · intro v hv
      simp only [pair, singleton, hv, false_or, or_false]
    · rintro ⟨ha,hb⟩
      obtain ⟨p,l,hI,hp,hl⟩ := sound j _ ha hb
      exact (split_ne e.1 l).symm (of_decide_eq_true hl)

end PEqualNP.Research.DiagonalInputs
