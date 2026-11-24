import PEqualNP.CoCommute1675

namespace Co1675ShardFour
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoCommute1675

def graph (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

private theorem of_signal (siblings : ∀ b : Bool, ∀ D : Circuit, FanInTwo D →
    (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = signal b x) →
    circuitFun 9 D = graph → 16 ≤ D.size) (b : Bool) (C : Circuit) (fan : FanInTwo C)
    (head : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 3))
    (next : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 10 false = signal b x)
    (solves : circuitFun 9 C = graph) : 16 ≤ C.size := by
  obtain ⟨gs,out⟩ := C
  have nonzero : signal b (fun _ => true) = true := by cases b <;> rfl
  have h := (next (fun _ => true)).trans nonzero
  cases gs with
  | nil =>
    change (List.ofFn (fun _ : Fin 9 => true)).getD 10 false = true at h
    rw [List.getD_eq_default _ _ (by simp)] at h
    cases h
  | cons a rest =>
    cases rest with
    | nil =>
      change ((List.ofFn (fun _ : Fin 9 => true)) ++ [_]).getD 10 false = true at h
      rw [List.getD_eq_default _ _ (by simp)] at h
      cases h
    | cons c tail => exact quotient b graph 16 (siblings b) a c tail out fan head next solves

theorem splice (siblings : ∀ b : Bool, ∀ D : Circuit, FanInTwo D →
    (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = signal b x) →
    circuitFun 9 D = graph → 16 ≤ D.size) (C : Circuit) (fan : FanInTwo C)
    (head : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3))
    (second : (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 10 false = (y 0 || y 1)) ∨
              (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 10 false = (y 0 && y 2)))
    (solves : circuitFun 9 C = graph) : 16 ≤ C.size := by
  rcases second with hor | hand
  · exact of_signal siblings true C fan head hor solves
  · exact of_signal siblings false C fan head hand solves

#print axioms splice
end Co1675ShardFour
