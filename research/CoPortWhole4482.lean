import PEqualNP.CoAllPorts4482

namespace CoPortRoots4482
open CoPortTrace4482 CoPortCut4482 PEqualNP.CircuitLowerBounds

theorem conditional
    (excluded : ∀ k ≤ 7, ¬ Path join (cleanCut model label 6) k raws.toFinset ∧
      ¬ Path join (cleanCut model label 6) k init.toFinset) : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : List PEqualNP.CircuitLowerBounds.Gate),   x2.length = (7 : ℕ) →     (∀ (x4 : ℕ) (x5 : x4 < x2.length), (x2[x4].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2[x4].op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x2[x4].inputs.length ≤ (2 : ℕ) ∧ ∀ x6 ∈ x2[x4].inputs, x6 < (10 : ℕ) + x4 ∨ x6 = (17 : ℕ)) →       have x5 : PEqualNP.CircuitLowerBounds.Circuit := { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (2 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };       ∀ x6 ⊆ (Finset.range (17 : ℕ)).erase (9 : ℕ), x6.card ≤ (6 : ℕ) → (∃ x9 ∈ x6, (10 : ℕ) ≤ x9) → ∃ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ) → Bool), x1 x10 ≠ x1 x11 ∧ ∀ x12 ∈ x6, (x5.wires (List.ofFn x10)).getD x12 Bool.false = (x5.wires (List.ofFn x11)).getD x12 Bool.false := by
  dsimp only
  intro gs len valid O _ cap _
  by_contra absent
  have legal : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
    intro g hg
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hg
    exact ⟨(valid i hi).1,(valid i hi).2.1⟩
  obtain ⟨k,hk,p⟩ := roots_of_collision_free gs legal O cap absent
  obtain ⟨a,b⟩ := excluded k (by omega)
  exact p.elim a b

#print axioms conditional
end CoPortRoots4482
