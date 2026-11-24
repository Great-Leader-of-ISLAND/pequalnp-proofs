import Mathlib

namespace CoTwoSidedPrices

/-- Every singleton witness for the side signal of a unique OR reader
masks a required positive incidence, even if rejection is only known with
at most two opposite inputs active. -/
theorem invisible_singletons {α β : Type*} [DecidableEq β]
    (I : α → β → Prop) (a : α) (neighbor : ∃ y, I a y)
    (T : Finset β → Prop) (up : ∀ U V, U ⊆ V → T U → T V)
    (K : Prop → Finset β → Prop)
    (factor : ∀ b : Bool, ∀ W : Finset β, W.card ≤ 2 →
      ((b = true ∧ ∃ y ∈ W, I a y) ↔ K (b = true ∨ T W) W)) :
    ∀ t, ¬T {t} := by
  intro t ht
  obtain ⟨y,hy⟩ := neighbor
  let W : Finset β := insert y {t}
  have count : W.card ≤ 2 := by
    exact (Finset.card_insert_le y {t}).trans (by simp)
  have on : T W := up _ _ (Finset.subset_insert _ _) ht
  have yes := (factor true W count).mp ⟨rfl,y,Finset.mem_insert_self _ _,hy⟩
  have no := factor false W count
  simp [on] at yes no
  exact no yes

def deficit : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | _ => 0

theorem point_price (a j : ℕ) (ha : 3 ≤ a) :
    deficit j * a * (a+1) ≤ 2 * ((j : ℤ) - a) * (j - a - 1) := by
  have hi : (3:ℤ) ≤ a := by exact_mod_cast ha
  cases j with
  | zero => simp [deficit]; ring_nf; exact le_rfl
  | succ j =>
    cases j with
    | zero =>
      change 1 * (a : ℤ) * (a+1) ≤ 2 * (1-a) * (1-a-1)
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ a) (by linarith : (0:ℤ) ≤ a-3)]
    | succ j =>
      simp only [deficit,zero_mul]
      have h : ((j+2:ℕ):ℤ) ≤ a ∨ (a:ℤ)+1 ≤ ((j+2:ℕ):ℤ) := by omega
      rcases h with h|h
      · have hp : 0 ≤ (((j+2:ℕ):ℤ)-a) * (((j+2:ℕ):ℤ)-a-1) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
        change 0 ≤ 2 * (((j+2:ℕ):ℤ)-a) * (((j+2:ℕ):ℤ)-a-1)
        linarith only [show 0 ≤ 2 * ((((j+2:ℕ):ℤ)-a) * (((j+2:ℕ):ℤ)-a-1)) from
          mul_nonneg (by decide) hp]
      · have hp : 0 ≤ (((j+2:ℕ):ℤ)-a) * (((j+2:ℕ):ℤ)-a-1) :=
          mul_nonneg (by linarith) (by linarith)
        change 0 ≤ 2 * (((j+2:ℕ):ℤ)-a) * (((j+2:ℕ):ℤ)-a-1)
        linarith only [show 0 ≤ 2 * ((((j+2:ℕ):ℤ)-a) * (((j+2:ℕ):ℤ)-a-1)) from
          mul_nonneg (by decide) hp]

theorem moment_price {X : Type*} [Fintype X] (j : X → ℕ) (a : ℕ) (ha : 3≤a) :
    (∑ x, deficit (j x)) * a * (a+1) ≤
      ∑ x, 2 * (((j x):ℤ)-a) * (((j x):ℤ)-a-1) := by
  simp only [Finset.sum_mul]
  exact Finset.sum_le_sum (fun x _ => point_price a (j x) ha)

def n (q : ℕ) := q*q+q+1
def weight (q : ℕ) := Nat.sqrt q
def retained (q : ℕ) := weight q*(q+1) - weight q*(weight q+1)/2
def den (q : ℕ) := weight q*(weight q+1)
def twiceMoment (q : ℕ) :=
  2 * (n q * den q + retained q*(retained q-1) - 2*weight q*retained q*(q+1))

theorem range_prices : ∀ i : Fin 381, 100 < i.val →
    3 ≤ weight i.val ∧ 1 < retained i.val ∧ retained i.val < n i.val ∧
    n i.val < retained i.val * (i.val+1) ∧
    i.val * n i.val ≤
      100 * (4 * n i.val - 2 * retained i.val - twiceMoment i.val / den i.val) := by
  decide +kernel

theorem target_to_380 {q size lost : ℕ} (lo : 100<q) (hi : q≤380)
    (gate_bound : 4*n q ≤ size + 2*retained q + lost)
    (geometry : lost ≤ twiceMoment q / den q) :
    n q * q ≤ 100*size := by
  have bound := (range_prices ⟨q,by omega⟩ lo).2.2.2.2
  change q*n q ≤ 100*(4*n q-2*retained q-twiceMoment q/den q) at bound
  rw [Nat.mul_comm (n q) q]
  omega

end CoTwoSidedPrices
