import PEqualNP.CoCommute1675
import PEqualNP.Outside.L_meta_1668
import PEqualNP.Outside.L_meta_1673

/- Research certificate for the two cases of shard 4 of L-meta-1675.
The two full sibling lower bounds, including their respective finite certificates,
are the merged L-meta-1668 and L-meta-1673. No imports of Outside are proposed
for an official proof of the full L-meta-1675 statement. -/
namespace Co1675ShardFour
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoCommute1675

def graph (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

private theorem siblings (b : Bool) : ∀ D : Circuit, FanInTwo D →
    (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = signal b x) →
    circuitFun 9 D = graph → 16 ≤ D.size := by
  cases b
  · exact PEqualNP.Outside.L_meta_1668
  · exact PEqualNP.Outside.L_meta_1673

private theorem of_signal (b : Bool) (C : Circuit) (fan : FanInTwo C)
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

theorem exhausted (C : Circuit) (fan : FanInTwo C)
    (head : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3))
    (second : (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 10 false = (y 0 || y 1)) ∨
              (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 10 false = (y 0 && y 2)))
    (solves : circuitFun 9 C = graph) : 16 ≤ C.size := by
  rcases second with hor | hand
  · exact of_signal true C fan head hor solves
  · exact of_signal false C fan head hand solves

end Co1675ShardFour
