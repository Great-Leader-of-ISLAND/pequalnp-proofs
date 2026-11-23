import Mathlib
import PEqualNP.Outside.L_meta_1377

namespace CoResearch.PlaneCases

open PEqualNP.CircuitLowerBounds

lemma pair_penalty {n m : ℕ} (S : Fin m → Finset (Fin n)) (p r : Fin n)
    (hp : p ≠ r) (linear : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∑ i : Fin m, ((S i ∩ {p,r}).card - 1) ≤ 1 := by
  classical
  have cardPair : ({p,r} : Finset (Fin n)).card = 2 := by simp [hp]
  have zero (i : Fin m) (h : ¬ ({p,r} : Finset (Fin n)) ⊆ S i) :
      (S i ∩ {p,r}).card - 1 = 0 := by
    have sub : S i ∩ {p,r} ⊆ ({p,r} : Finset (Fin n)) := Finset.inter_subset_right
    have neq : S i ∩ {p,r} ≠ ({p,r} : Finset (Fin n)) := by
      intro equal
      apply h
      rw [← equal]
      exact Finset.inter_subset_left
    have lt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub, neq⟩)
    omega
  by_cases found : ∃ k, ({p,r} : Finset (Fin n)) ⊆ S k
  · obtain ⟨k, hk⟩ := found
    rw [Finset.sum_eq_single k]
    · have hi := Finset.card_le_card (show S k ∩ {p,r} ⊆ ({p,r} : Finset (Fin n)) from Finset.inter_subset_right)
      omega
    · intro i _ different
      apply zero
      intro hi
      have sm : ({p,r} : Finset (Fin n)) ⊆ S i ∩ S k := fun x hx => Finset.mem_inter.mpr ⟨hi hx,hk hx⟩
      have first := Finset.card_le_card sm
      have second := linear i k different
      omega
    · simp
  · have allZero : ∀ i : Fin m, (S i ∩ {p,r}).card - 1 = 0 :=
      fun i => zero i (fun hi => found ⟨i,hi⟩)
    simp [allZero]

theorem one_not_with_two_point_transversal
    (q n m : ℕ) (S : Fin m → Finset (Fin n)) (p r : Fin n) (hp : p ≠ r)
    (hq : 2 ≤ q) (sizes : ∀ i, (S i).card = q+1)
    (linear : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ) (j : Fin gates.length)
    (ops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (neg : (gates.get j).op = GateOp.not)
    (unique : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (correct : ∀ w (x : Fin n → Bool), Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
      decide (∃ v ∈ S w, x v = true))
    (transversal : ∀ x : Fin n → Bool, x p = false → x r = false →
      Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = true) :
    m * q ≤ gates.length := by
  classical
  have off (x : Fin n → Bool) (h : ∀ v ∈ ({p,r} : Finset (Fin n)), x v = false) :=
    transversal x (h p (by simp)) (h r (by simp))
  have bound := PEqualNP.Outside.L_meta_1377 q n m S {p,r} hq sizes linear gates out j ops neg unique correct off
  have loss := pair_penalty S p r hp linear
  omega

end CoResearch.PlaneCases

#print axioms CoResearch.PlaneCases.one_not_with_two_point_transversal
