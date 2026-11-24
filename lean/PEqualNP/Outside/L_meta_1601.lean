import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_1601 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ y : Fin m → Bool, PEqualNP.EdgeOwnership.gateVal m D k y = true → PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ y = true) → ∃ S : Finset (Fin m), (∀ e w : Fin m, H.Adj e w → e ∈ S ∨ w ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 ∧ H.edgeFinset.card ≤ D.size + 1 := by
  intro transfer m H _ D mono computes girth clean
  have noSquare : ∀ a b c d : Fin m, a ≠ c → b ≠ d →
      ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a) := by
    intro a b c d hac hbd
    rintro ⟨hab, hbc, hcd, hda⟩
    -- Use the explicit four-edge cycle from the checked L-meta-603 square argument.
    let W : H.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
    have len : W.length = 4 := rfl
    have cyc : W.IsCycle := by
      apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨?_, by omega⟩
      simp only [W, SimpleGraph.Walk.tail_cons, SimpleGraph.Walk.isPath_copy,
        SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
      simp [hbd, hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hac.symm]
    have bound := girth a W cyc
    omega
  have ops : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := mono g hg
    exact ⟨by simpa using hop, hlen⟩
  have output : ∀ x : Fin m → Bool,
      Circuit.eval ⟨D.gates, D.output⟩ (List.ofFn x) =
        decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    simpa [circuitFun, NestedCover.graphFun] using congrFun computes x
  have clean' : ∀ (i : Fin D.gates.length) (x : Fin m → Bool),
      (D.gates.get i).op = GateOp.and →
      (Circuit.wires ⟨D.gates, 0⟩ (List.ofFn x)).getD (m + (i : ℕ)) false = true →
      ∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true := by
    intro i x hop hv
    have opAt : (NestedCover.gateAt D i.val).op = GateOp.and := by
      unfold NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ i.isLt]
      exact hop
    have hg := clean i.val i.isLt opAt x (by exact hv)
    simpa [NestedCover.graphFun] using hg
  obtain ⟨S, covers, cost⟩ := transfer m H noSquare D.gates D.output ops output clean'
  change H.edgeFinset.card + S.card ≤ D.size + 1 at cost
  exact ⟨S, covers, cost, by omega⟩
