import Mathlib

namespace PEqualNP.Research.CoDiagonalDensity

/-- The lower chord of the integer factorial second moment between m and m+1. -/
private theorem degree_chord (m d : ℕ) :
    (2 * m) * d ≤ d * (d - 1) + m * (m + 1) := by
  cases d with
  | zero => simp
  | succ d =>
    change (2 * m) * (d + 1) ≤ (d + 1) * d + m * (m + 1)
    have hn : 0 ≤ ((d : ℤ) + 1 - m) * ((d : ℤ) - m) := by
      by_cases h : (d : ℤ) < m
      · apply mul_nonneg_of_nonpos_of_nonpos <;> omega
      · apply mul_nonneg <;> omega
    exact_mod_cast (show (2 * (m : ℤ)) * ((d : ℤ) + 1) ≤
        ((d : ℤ) + 1) * (d : ℤ) + (m : ℤ) * (m + 1) by nlinarith [hn])

/-- A finite sum version, valid also for empty supports and zero degrees. -/
theorem sum_degree_chord {α : Type*} (s : Finset α) (d : α → ℕ) (m : ℕ) :
    (2 * m) * (∑ v ∈ s, d v) ≤ (∑ v ∈ s, d v * (d v - 1)) + m * (m + 1) * s.card := by
  classical
  calc
    _ = ∑ v ∈ s, (2 * m) * d v := by rw [Finset.mul_sum]
    _ ≤ ∑ v ∈ s, (d v * (d v - 1) + m * (m + 1)) :=
      Finset.sum_le_sum (fun v _ => degree_chord m (d v))
    _ = _ := by rw [Finset.sum_add_distrib]; simp [Nat.mul_comm]

/-- Number of vertices per side forced by an integer average degree exceeding m. -/
theorem side_lower_bound {α : Type*} (s : Finset α) (d : α → ℕ) (m N : ℕ)
    (hm : 1 ≤ m)
    (pairs : (∑ v ∈ s, d v * (d v - 1)) ≤ (N - 1) * s.card)
    (dense : m * s.card < ∑ v ∈ s, d v) :
    m * (m - 1) + 2 ≤ N := by
  by_contra hN
  have hN' : N - 1 ≤ m * (m - 1) := by omega
  have hpairs := pairs.trans (Nat.mul_le_mul_right s.card hN')
  have hmoment := sum_degree_chord s d m
  have hstrict := Nat.mul_lt_mul_of_pos_left dense (by omega : 0 < 2 * m)
  have hid : (2 * m) * (m * s.card) =
      m * (m - 1) * s.card + m * (m + 1) * s.card := by
    cases m with
    | zero => simp
    | succ k =>
      change (2 * (k + 1)) * ((k + 1) * s.card) =
        (k + 1) * k * s.card + (k + 1) * (k + 1 + 1) * s.card
      ring
  rw [hid] at hstrict
  omega

theorem bound416 {α : Type*} (s : Finset α) (d : α → ℕ) (N : ℕ)
    (pairs : (∑ v ∈ s, d v * (d v - 1)) ≤ (N - 1) * s.card)
    (dense : 416 * s.card < ∑ v ∈ s, d v) : 172642 ≤ N :=
  side_lower_bound s d 416 N (by decide) pairs dense

theorem bound432 {α : Type*} (s : Finset α) (d : α → ℕ) (N : ℕ)
    (pairs : (∑ v ∈ s, d v * (d v - 1)) ≤ (N - 1) * s.card)
    (dense : 432 * s.card < ∑ v ∈ s, d v) : 186194 ≤ N :=
  side_lower_bound s d 432 N (by decide) pairs dense

theorem bound816 {α : Type*} (s : Finset α) (d : α → ℕ) (N : ℕ)
    (pairs : (∑ v ∈ s, d v * (d v - 1)) ≤ (N - 1) * s.card)
    (dense : 816 * s.card < ∑ v ∈ s, d v) : 665042 ≤ N :=
  side_lower_bound s d 816 N (by decide) pairs dense

/-- Numerical use of the component count, once proved for the circuit. -/
theorem dense816_of_components (U S J N edges : ℕ)
    (components : U ≤ S + J) (sides : U ≤ 2 * N)
    (counter : 400 * (S + J) + 16 * N < edges) :
    816 * U < 2 * edges := by omega

/-- Numerical use of the point-input pin count, when available. -/
theorem dense432_of_pins (p l S J N edges : ℕ)
    (roots : p + l ≤ S + 2 * J) (point_pins : p ≤ 2 * S) (line_bound : l ≤ N)
    (counter : 400 * (S + J) + 16 * N < edges) :
    432 * (p + l) < 2 * edges := by omega

end PEqualNP.Research.CoDiagonalDensity
