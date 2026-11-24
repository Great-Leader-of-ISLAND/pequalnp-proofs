import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2473 : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x5]? = Option.some x6 → x1 x2 x3 x6 → x5 ∈ x4) → ∃ x6 ⊆ x4, x6 ⊆ Finset.range x3.size ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x7]? = Option.some x8 → (x7 ∈ x6 ↔ x1 x2 x3 x8) := by
  classical
  dsimp only
  intro n C S cover
  let P := fun j : ℕ => ∃ g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    ((∀ k ∈ g.inputs, ∃ x : Fin n → Bool,
        (C.wires (List.ofFn x ++ List.replicate n false)).getD k false ≠
        (C.wires (List.ofFn x ++ List.replicate n true)).getD k false) ∨
      ∀ k ∈ g.inputs, ∃ x : Fin n → Bool,
        (C.wires (List.replicate n false ++ List.ofFn x)).getD k false ≠
        (C.wires (List.replicate n true ++ List.ofFn x)).getD k false)
  refine ⟨(Finset.range C.size).filter P, ?_, Finset.filter_subset _ _, ?_⟩
  · intro j hj
    obtain ⟨g,hg,hh⟩ := (Finset.mem_filter.mp hj).2
    exact cover j g hg hh
  · intro j g hg
    constructor
    · intro h
      obtain ⟨g',hg',hh⟩ := (Finset.mem_filter.mp h).2
      have eq : g' = g := Option.some.inj (hg'.symm.trans hg)
      exact eq ▸ hh
    · intro h
      have hj : j < C.gates.length := by
        by_contra! hn
        rw [List.getElem?_eq_none hn] at hg
        contradiction
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, g,hg,h⟩
