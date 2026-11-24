import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research.PetersenStarWitness
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[
  ⟨.and, [0, 1]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.and, [0, 10]⟩,
  ⟨.or, [2, 6]⟩,
  ⟨.and, [1, 12]⟩,
  ⟨.or, [2, 4]⟩,
  ⟨.or, [14, 8]⟩,
  ⟨.and, [3, 15]⟩,
  ⟨.or, [2, 5]⟩,
  ⟨.and, [7, 17]⟩,
  ⟨.or, [6, 5]⟩,
  ⟨.and, [8, 19]⟩,
  ⟨.or, [9, 11]⟩,
  ⟨.or, [21, 13]⟩,
  ⟨.or, [22, 16]⟩,
  ⟨.or, [23, 18]⟩,
  ⟨.or, [24, 20]⟩], 25⟩

def target := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

-- The first AND is live: its output is read by the first final OR.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem verified_live17 : FanInTwo circuit ∧ circuit.size = 17 ∧
    (∃ g ∈ circuit.gates, 9 ∈ g.inputs) ∧
    (∀ x : Fin 9 → Bool, (circuit.wires (List.ofFn x)).getD 9 false = (x 0 && x 1)) ∧
    (∀ x : Fin 9 → Bool, circuitFun 9 circuit x = target x) := by
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · refine ⟨⟨.or, [9,11]⟩, ?_, by decide⟩
    simp [circuit]
  · decide +kernel
  · decide +kernel

end PEqualNP.Research.PetersenStarWitness
