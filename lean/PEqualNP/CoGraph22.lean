import Mathlib
import PEqualNP.Defs

-- Positive control only. A concrete clean 22-gate star cover.

namespace PEqualNP.ResearchControls.Graph1342Control22

open PEqualNP.CircuitLowerBounds

private def candidate : Circuit :=
  ⟨[⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.and, [0, 11]⟩,
    ⟨GateOp.or, [4, 8]⟩,
    ⟨GateOp.and, [1, 13]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.and, [3, 15]⟩,
    ⟨GateOp.or, [2, 8]⟩,
    ⟨GateOp.or, [17, 9]⟩,
    ⟨GateOp.and, [5, 18]⟩,
    ⟨GateOp.or, [6, 9]⟩,
    ⟨GateOp.and, [7, 20]⟩,
    ⟨GateOp.or, [4, 9]⟩,
    ⟨GateOp.and, [8, 22]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [24, 6]⟩,
    ⟨GateOp.and, [10, 25]⟩,
    ⟨GateOp.or, [12, 14]⟩,
    ⟨GateOp.or, [27, 16]⟩,
    ⟨GateOp.or, [28, 19]⟩,
    ⟨GateOp.or, [29, 21]⟩,
    ⟨GateOp.or, [30, 23]⟩,
    ⟨GateOp.or, [31, 26]⟩], 32⟩

private def natEdges : List (ℕ × ℕ) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
private def finEdges : List (Fin 11 × Fin 11) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

set_option maxRecDepth 8192 in
private theorem memEdges : ∀ u v : Fin 11,
    (u, v) ∈ finEdges ↔ (u.val, v.val) ∈ natEdges := by decide

private def edgeValue (x : Fin 11 → Bool) : Bool :=
  finEdges.any fun e => x e.1 && x e.2

private theorem edgeSpec (x : Fin 11 → Bool) : edgeValue x = true ↔
    ∃ u v : Fin 11, (u.val, v.val) ∈ natEdges ∧ x u = true ∧ x v = true := by
  rw [edgeValue, List.any_eq_true]
  constructor
  · rintro ⟨⟨u, v⟩, hmem, hval⟩
    exact ⟨u, v, (memEdges u v).mp hmem, Bool.and_eq_true_iff.mp hval⟩
  · rintro ⟨u, v, hmem, hu, hv⟩
    exact ⟨(u, v), (memEdges u v).mpr hmem, Bool.and_eq_true_iff.mpr ⟨hu, hv⟩⟩

private def circuitExpr (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool) : Bool :=
  let w11 := ([b9, b10] : List Bool).any id
  let w12 := ([b0, w11] : List Bool).all id
  let w13 := ([b4, b8] : List Bool).any id
  let w14 := ([b1, w13] : List Bool).all id
  let w15 := ([b6, b7] : List Bool).any id
  let w16 := ([b3, w15] : List Bool).all id
  let w17 := ([b2, b8] : List Bool).any id
  let w18 := ([w17, b9] : List Bool).any id
  let w19 := ([b5, w18] : List Bool).all id
  let w20 := ([b6, b9] : List Bool).any id
  let w21 := ([b7, w20] : List Bool).all id
  let w22 := ([b4, b9] : List Bool).any id
  let w23 := ([b8, w22] : List Bool).all id
  let w24 := ([b2, b4] : List Bool).any id
  let w25 := ([w24, b6] : List Bool).any id
  let w26 := ([b10, w25] : List Bool).all id
  let w27 := ([w12, w14] : List Bool).any id
  let w28 := ([w27, w16] : List Bool).any id
  let w29 := ([w28, w19] : List Bool).any id
  let w30 := ([w29, w21] : List Bool).any id
  let w31 := ([w30, w23] : List Bool).any id
  let w32 := ([w31, w26] : List Bool).any id
  w32

private def edgeExpr (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool) : Bool :=
  ([(b0, b9), (b0, b10), (b1, b4), (b1, b8), (b2, b5), (b2, b10), (b3, b6), (b3, b7), (b4, b8), (b4, b10), (b5, b8), (b5, b9), (b6, b7), (b6, b10), (b7, b9), (b8, b9)] : List (Bool × Bool)).any fun e => e.1 && e.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem agreement : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    circuitExpr b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 = edgeExpr b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 := by decide

private def stepWire (vs : List Bool) (g : Gate) : List Bool :=
  vs ++ [g.op.eval (g.inputs.map fun i => vs.getD i false)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem evalEdge (x : Fin 11 → Bool) : candidate.eval (List.ofFn x) = edgeValue x := by
  have hin : List.ofFn x = [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10)] := by simp [List.ofFn_succ]
  let vs11 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10)]
  let w11 := ([(x 9), (x 10)] : List Bool).any id
  let vs12 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11]
  have step11 : stepWire vs11 ⟨GateOp.or, [9, 10]⟩ = vs12 := rfl
  let w12 := ([(x 0), w11] : List Bool).all id
  let vs13 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12]
  have step12 : stepWire vs12 ⟨GateOp.and, [0, 11]⟩ = vs13 := rfl
  let w13 := ([(x 4), (x 8)] : List Bool).any id
  let vs14 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13]
  have step13 : stepWire vs13 ⟨GateOp.or, [4, 8]⟩ = vs14 := rfl
  let w14 := ([(x 1), w13] : List Bool).all id
  let vs15 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14]
  have step14 : stepWire vs14 ⟨GateOp.and, [1, 13]⟩ = vs15 := rfl
  let w15 := ([(x 6), (x 7)] : List Bool).any id
  let vs16 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15]
  have step15 : stepWire vs15 ⟨GateOp.or, [6, 7]⟩ = vs16 := rfl
  let w16 := ([(x 3), w15] : List Bool).all id
  let vs17 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16]
  have step16 : stepWire vs16 ⟨GateOp.and, [3, 15]⟩ = vs17 := rfl
  let w17 := ([(x 2), (x 8)] : List Bool).any id
  let vs18 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17]
  have step17 : stepWire vs17 ⟨GateOp.or, [2, 8]⟩ = vs18 := rfl
  let w18 := ([w17, (x 9)] : List Bool).any id
  let vs19 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18]
  have step18 : stepWire vs18 ⟨GateOp.or, [17, 9]⟩ = vs19 := rfl
  let w19 := ([(x 5), w18] : List Bool).all id
  let vs20 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19]
  have step19 : stepWire vs19 ⟨GateOp.and, [5, 18]⟩ = vs20 := rfl
  let w20 := ([(x 6), (x 9)] : List Bool).any id
  let vs21 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20]
  have step20 : stepWire vs20 ⟨GateOp.or, [6, 9]⟩ = vs21 := rfl
  let w21 := ([(x 7), w20] : List Bool).all id
  let vs22 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21]
  have step21 : stepWire vs21 ⟨GateOp.and, [7, 20]⟩ = vs22 := rfl
  let w22 := ([(x 4), (x 9)] : List Bool).any id
  let vs23 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22]
  have step22 : stepWire vs22 ⟨GateOp.or, [4, 9]⟩ = vs23 := rfl
  let w23 := ([(x 8), w22] : List Bool).all id
  let vs24 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23]
  have step23 : stepWire vs23 ⟨GateOp.and, [8, 22]⟩ = vs24 := rfl
  let w24 := ([(x 2), (x 4)] : List Bool).any id
  let vs25 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24]
  have step24 : stepWire vs24 ⟨GateOp.or, [2, 4]⟩ = vs25 := rfl
  let w25 := ([w24, (x 6)] : List Bool).any id
  let vs26 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25]
  have step25 : stepWire vs25 ⟨GateOp.or, [24, 6]⟩ = vs26 := rfl
  let w26 := ([(x 10), w25] : List Bool).all id
  let vs27 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26]
  have step26 : stepWire vs26 ⟨GateOp.and, [10, 25]⟩ = vs27 := rfl
  let w27 := ([w12, w14] : List Bool).any id
  let vs28 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27]
  have step27 : stepWire vs27 ⟨GateOp.or, [12, 14]⟩ = vs28 := rfl
  let w28 := ([w27, w16] : List Bool).any id
  let vs29 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28]
  have step28 : stepWire vs28 ⟨GateOp.or, [27, 16]⟩ = vs29 := rfl
  let w29 := ([w28, w19] : List Bool).any id
  let vs30 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29]
  have step29 : stepWire vs29 ⟨GateOp.or, [28, 19]⟩ = vs30 := rfl
  let w30 := ([w29, w21] : List Bool).any id
  let vs31 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30]
  have step30 : stepWire vs30 ⟨GateOp.or, [29, 21]⟩ = vs31 := rfl
  let w31 := ([w30, w23] : List Bool).any id
  let vs32 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31]
  have step31 : stepWire vs31 ⟨GateOp.or, [30, 23]⟩ = vs32 := rfl
  let w32 := ([w31, w26] : List Bool).any id
  let vs33 := [(x 0), (x 1), (x 2), (x 3), (x 4), (x 5), (x 6), (x 7), (x 8), (x 9), (x 10), w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32]
  have step32 : stepWire vs32 ⟨GateOp.or, [31, 26]⟩ = vs33 := rfl
  have hw : candidate.wires (List.ofFn x) = vs33 := by
    rw [hin]
    change List.foldl stepWire vs11 candidate.gates = vs33
    simp only [candidate, List.foldl_cons, List.foldl_nil, step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22, step23, step24, step25, step26, step27, step28, step29, step30, step31, step32]
  calc
    candidate.eval (List.ofFn x) = w32 := by
      change (candidate.wires (List.ofFn x)).getD 32 false = _
      rw [hw] <;> rfl
    _ = edgeValue x := agreement (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 candidate := by
  simp [PEqualNP.MetaComplexity.Monotone2, candidate]

end PEqualNP.ResearchControls.Graph1342Control22

open PEqualNP.ResearchControls.Graph1342Control22 in
theorem PEqualNP.ResearchControls.Graph1342Control22.upperBound22 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∀ x : Fin 11 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧ C.size ≤ 22 := by
  refine ⟨candidate, monotone, ?_, by decide⟩
  intro x
  rw [evalEdge]
  exact edgeSpec x

#print axioms PEqualNP.ResearchControls.Graph1342Control22.upperBound22
