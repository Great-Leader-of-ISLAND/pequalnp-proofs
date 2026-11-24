import Mathlib

namespace CoFlagBudget2990

inductive Walk {σ : Type} (step : σ→σ→Prop) : σ→Nat→σ→Prop
  | nil (x) : Walk step x 0 x
  | cons {x y z n} : step x y → Walk step y n z → Walk step x (n+1) z

/-- A failed flag step strictly decreases the number of remaining all-false
ANDs. Its witness can be chosen adaptively. The initial admissible state
can carry the sparse-line invariant and any coordinates already fixed. -/
theorem finite_flag_steps {σ : Type} (done : σ→Prop) (step : σ→σ→Prop)
    (fuel : σ→Nat) (admissible : σ→Prop)
    (advance : ∀ x, admissible x → ¬done x → ∃ y, step x y ∧ admissible y ∧ fuel y<fuel x)
    (x : σ) (hx : admissible x) :
    ∃ n≤fuel x, ∃ y, Walk step x n y ∧ admissible y ∧ done y := by
  classical
  have solve (k : Nat) : ∀ x, fuel x=k → admissible x →
      ∃ n≤k, ∃ y, Walk step x n y ∧ admissible y ∧ done y := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro s hsz hs
      by_cases fin : done s
      · exact ⟨0,Nat.zero_le k,s,Walk.nil s,hs,fin⟩
      · obtain ⟨t,act,ok,less⟩ := advance s hs fin
        obtain ⟨n,le,y,rest,ad,endp⟩ := ih (fuel t) (by omega) t rfl ok
        exact ⟨n+1,by omega,y,Walk.cons act rest,ad,endp⟩
  exact solve _ x rfl hx

theorem nine_tenths (q t N s : Nat) (q0 : 300 ≤ q) (ht : 10 * t ≤ 9 * q)
    (plane : N = q * q + q + 1)
    (cost : (q + 1) * (q - t) * (q + 1 - t) ≤ s) : t + 1 ≤ q ∧ N * q ≤ 100 * s := by
  have inside : t ≤ q := by omega
  let r := q - t
  have add : q + 1 - t = r + 1 := by dsimp [r]; omega
  have hr : q ≤ 10 * r := by dsimp [r]; omega
  change (q + 1) * r * (q + 1 - t) ≤ s at cost
  rw [add] at cost
  have square := Nat.mul_le_mul hr hr
  have cube := Nat.mul_le_mul_left (q + 1) square
  subst N
  refine ⟨by omega,?_⟩
  nlinarith only [cube,cost,hr,Nat.zero_le (q * r)]

theorem six_sevenths (q t N s : Nat) (q0 : 300 ≤ q) (ht : 7 * t ≤ 6 * q)
    (plane : N = q * q + q + 1)
    (cost : (q + 1) * (q - t) * (q + 1 - t) ≤ 2 * s + 1) : t + 1 ≤ q ∧ N * q ≤ 100 * s := by
  have inside : t ≤ q := by omega
  let r := q - t
  have add : q + 1 - t = r + 1 := by dsimp [r]; omega
  have hr : q ≤ 7 * r := by dsimp [r]; omega
  change (q + 1) * r * (q + 1 - t) ≤ 2 * s + 1 at cost
  rw [add] at cost
  have square := Nat.mul_le_mul hr hr
  have cube := Nat.mul_le_mul_left (q + 1) square
  have coarse : 1 ≤ r := by omega
  have qr : q ≤ q * r := by simpa using Nat.mul_le_mul_left q coarse
  subst N
  refine ⟨by omega,?_⟩
  nlinarith only [cube,cost,hr,qr,q0,Nat.zero_le (r * r),Nat.zero_le (q * (r * r))]

#print axioms finite_flag_steps
#print axioms nine_tenths
#print axioms six_sevenths
end CoFlagBudget2990
