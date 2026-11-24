import PEqualNP.Defs

namespace PhaseTwo.Heawood

theorem refute : ¬ (∀ (x1 : (Fin (14 : ℕ) → Bool) → Prop),   ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.GateOp) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ × ℕ),     PEqualNP.MetaComplexity.Monotone2 x2 ∧       x2.size ≤ (25 : ℕ) ∧         (14 : ℕ) ≤ x4 ∧           x4 < x5 ∧             x5 < (14 : ℕ) + x2.size ∧               (x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x6 ∈ [((129 : ℕ), (130 : ℕ)), ((129 : ℕ), (260 : ℕ)), ((129 : ℕ), (544 : ℕ))]) ∧                 have x7 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x7 : ℕ) (x8 : Fin (14 : ℕ) → Bool) => (x2.wires (List.ofFn x8)).getD x7 Bool.false;                 have x8 : Fin (14 : ℕ) → Bool := fun (x8 : Fin (14 : ℕ)) => x6.1.testBit ↑x8;                 have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => x6.2.testBit ↑x9;                 have x10 : (Fin (14 : ℕ) → Bool) → Bool := fun (x10 : Fin (14 : ℕ) → Bool) => x3.eval [x7 x4 x10, x7 x5 x10];                 x7 x4 x8 ≠ x7 x5 x8 ∧ x7 x4 x8 = x7 x5 x9 ∧ x7 x5 x8 = x7 x4 x9 ∧ (∀ (x11 : Fin (14 : ℕ) → Bool), Minimal x1 x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.true) ∧ ∀ (x11 : Fin (14 : ℕ) → Bool), Maximal (fun (x12 : Fin (14 : ℕ) → Bool) => ¬x1 x12) x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.false) := by
  classical
  intro h
  let r : Fin 14 → Bool := fun i => (129 : Nat).testBit i.val
  obtain ⟨C, op, a, b, z, _, _, _, _, _, ⟨rfl, hz⟩, diff, _, _, _, hn⟩ :=
    h (fun x => x ≠ r)
  have key : z.1 = 129 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> rfl
  have maximal : Maximal (fun x : Fin 14 → Bool => ¬ x ≠ r) r := by
    constructor
    · simp
    · intro y hy _
      have yr : y = r := Classical.not_not.mp hy
      subst y
      exact le_rfl
  have no := hn r maximal
  change (C.wires (List.ofFn (fun i : Fin 14 => z.1.testBit i.val))).getD a false ≠
    (C.wires (List.ofFn (fun i : Fin 14 => z.1.testBit i.val))).getD b false at diff
  rw [key] at diff
  change (C.wires (List.ofFn r)).getD a false ≠ (C.wires (List.ofFn r)).getD b false at diff
  rcases no with ⟨bad, _⟩ | off
  · cases bad
  · change PEqualNP.CircuitLowerBounds.GateOp.or.eval
      [(C.wires (List.ofFn r)).getD a false, (C.wires (List.ofFn r)).getD b false] = false at off
    cases ha : (C.wires (List.ofFn r)).getD a false <;> cases hb : (C.wires (List.ofFn r)).getD b false <;>
      simp [ha, hb, PEqualNP.CircuitLowerBounds.GateOp.eval] at diff off

end PhaseTwo.Heawood
