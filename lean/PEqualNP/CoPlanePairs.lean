import PEqualNP.CoArcGreedy
import PEqualNP.CoPairedArc
import PEqualNP.CoSevenBlocks

namespace PEqualNP.Research.PlanePairs

open PEqualNP.CircuitLowerBounds

-- The chosen trigger pairs depend only on the plane. The conclusion applies
-- to every circuit whose inverted signal is true whenever a pair is present.
theorem pair_trigger_lower_bound (q m : ℕ) (S : Fin m → Finset (Fin m))
    (hq : 77 ≤ q) (hm : m = q*q+q+1) (hsize : ∀ i, (S i).card = q+1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hcover : ∀ p : Fin m, ∃ i, p ∈ S i) :
    ∃ B : Fin 7 → Finset (Fin m),
      (∀ k, (B k).card = 2) ∧ (∀ k l, k ≠ l → Disjoint (B k) (B l)) ∧
      ∀ (gates : List Gate) (out : Fin m → ℕ) (j : Fin gates.length),
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) →
      (gates.get j).op = GateOp.not →
      (∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j) →
      (∀ (i : Fin m) (x : Fin m → Bool),
        Circuit.eval ⟨gates, out i⟩ (List.ofFn x) = decide (∃ v ∈ S i, x v = true)) →
      (∀ (k : Fin 7) (U : Finset (Fin m)), B k ⊆ U →
        Circuit.eval ⟨gates, m+(j : ℕ)⟩ (List.ofFn (fun v : Fin m => decide (v ∈ U))) = false) →
      m*q + (Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ m+(j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  subst m
  obtain ⟨A, ha, ht⟩ := PEqualNP.Research.ArcGreedy.arc14 S hq hsize hinter
  obtain ⟨B, hpairs, _, hd, hthin⟩ :=
    PEqualNP.Research.PairedArc.seven_pairs_of_arc14 S A ha ht
  refine ⟨B, hpairs, hd, ?_⟩
  intro gates out j hg hj hu hf hswitch
  exact PEqualNP.Outside.CoSevenBlocks.seven_blocks S B (by omega) (by positivity)
    hsize (fun i k h => (hinter i k h).le) hcover hthin gates out j hg hj hu hf hswitch

end PEqualNP.Research.PlanePairs
