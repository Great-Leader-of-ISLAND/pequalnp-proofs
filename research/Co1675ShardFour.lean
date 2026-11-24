import PEqualNP.Co1675SliceBridge
import PEqualNP.Outside.L_meta_1668
import PEqualNP.Outside.L_meta_1673

namespace Co1675ShardFour
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoCommute1675

private theorem siblings (b : Bool) : ∀ D : Circuit, FanInTwo D →
    (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = signal b x) →
    circuitFun 9 D = graph → 16 ≤ D.size := by
  cases b
  · exact PEqualNP.Outside.L_meta_1668
  · exact PEqualNP.Outside.L_meta_1673

theorem exhausted (C : Circuit) (fan : FanInTwo C)
    (head : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3))
    (second : (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 10 false = (y 0 || y 1)) ∨
              (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 10 false = (y 0 && y 2)))
    (solves : circuitFun 9 C = graph) : 16 ≤ C.size := splice siblings C fan head second solves

#print axioms exhausted
end Co1675ShardFour
