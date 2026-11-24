import Mathlib

namespace CoStrip2990

/-- Core-plus-protected-suffix invariant in the prescribed-point deletion:
the core stays sound through t+1 lines, although the moved signal only has
to be sound through t lines. Arbitrary remaining live fanout is permitted
in the mask hypothesis. -/
theorem protected_companion {P L : Type} [DecidableEq L] (I : P→L→Prop)
    (l : L) (t : Nat) (core : Bool→Finset P→Finset L→Bool)
    (comp : Finset P→Finset L→Bool)
    (spare : ∀ x : P, ¬ I x l)
    (increasing : ∀ X Y, comp X Y=true → comp X (insert l Y)=true)
    (masked : ∀ X Y, comp X Y=true → core false X Y=core true X Y)
    (upper : ∀ (X : Finset P) (Y : Finset L), Y.card≤t+1 →
      (¬ ∃ a∈X, ∃ b∈Y, I a b) → core false X Y=false)
    (lower : ∀ X Y, l∈Y → core true X Y=true)
    (X : Finset P) (Y : Finset L) (sparse : Y.card≤t)
    (ind : ¬∃ a∈X, ∃ b∈Y, I a b) : comp X Y=false := by
  classical
  have neigh : ¬∃ a∈X, ∃ b∈insert l Y,I a b := by
    rintro ⟨a,ha,b,hb,e⟩
    rcases Finset.mem_insert.mp hb with rfl|kept
    · exact spare a e
    · exact ind ⟨a,ha,b,kept,e⟩
  have size := Finset.card_insert_le l Y
  have lo := upper X (insert l Y) (by omega) neigh
  have hi := lower X (insert l Y) (Finset.mem_insert_self _ _)
  cases h : comp X Y with
  | false => rfl
  | true =>
    have eq := masked X (insert l Y) (increasing X Y h)
    rw [lo,hi] at eq
    contradiction

/-- The two paid projections and the residual star/parallel-path prices. -/
theorem strip_sum (q N s : ℕ) (h3 : 3 ≤ q) (plane : N = q * q + q + 1)
    (paid : 2 * (N - (2 * q + 1)) + (2 * (q * q - q + 1) - 1) + (q + 1) + (3 * q + 2) ≤ s) :
    4 * N ≤ s + 4 * q :=  by
  have sq : 2 * q ≤ q * q :=  Nat.mul_le_mul_right q (by omega)
  omega

theorem finite_range (q N s : ℕ) (lo : 300 ≤ q) (hi : q ≤ 399)
    (plane : N = q * q + q + 1) (bound : 4 * N ≤ s + 4 * q) : N * q ≤ 100 * s :=  by
  by_cases h : q = 399
  · subst q
    norm_num at plane
    omega
  · have hn : 200 * q ≤ N :=  by
      have step : q * 200 ≤ q * q :=  Nat.mul_le_mul_left q (by omega)
      omega
    have hq : q ≤ 398 :=  by omega
    have step : N * q ≤ N * 398 :=  Nat.mul_le_mul_left N hq
    omega

#print axioms protected_companion
#print axioms finite_range
end CoStrip2990
