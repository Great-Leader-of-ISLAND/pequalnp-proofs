import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Ladder1395

def Pays (q h b : ℕ) : List ℕ → Prop
  | [] => True
  | k :: ks => k ≤ q ∧ h ≤ k * (q + 1 - b) ∧ Pays q h (b + k) ks

lemma pays_append (q h b : ℕ) (l r : List ℕ) :
    Pays q h b (l ++ r) ↔ Pays q h b l ∧ Pays q h (b + l.sum) r := by
  induction l generalizing b with
  | nil => simp [Pays]
  | cons a l ih =>
    simp only [List.cons_append, Pays, ih, List.sum_cons, Nat.add_assoc]
    tauto

lemma member_le_max (f : ℕ → ℕ) (l : List ℕ) (j : ℕ) (hj : j ∈ l) :
    f j ≤ l.foldr (fun i acc => max acc (f i)) 0 := by
  induction l with
  | nil => simp at hj
  | cons a l ih =>
    rcases List.mem_cons.mp hj with e | he
    · subst j
      exact le_max_right _ _
    · exact (ih he).trans (le_max_left _ _)

lemma base_factor (q b : ℕ) :
    q * (q + 1 - b) ≤ (q ^ 2 + q + 1) -
      (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1)) := by
  by_cases hb : b = 0
  · subst b
    simp [pow_two, Nat.mul_add]
  · rw [if_neg hb]
    by_cases small : b ≤ q + 1
    · have add : q * (q + 1 - b) + b * q = q ^ 2 + q := by
        rw [Nat.mul_comm b q, ← Nat.mul_add, Nat.sub_add_cancel small]
        ring
      have le : b*q+1 ≤ q^2+q+1 := by omega
      rw [min_eq_right le]
      omega
    · simp [Nat.sub_eq_zero_of_le (by omega : q+1 ≤ b)]

lemma tree (q h : ℕ) (G : ℕ → ℕ → ℕ → ℕ)
    (base : ∀ b K, G 0 b K = ((q ^ 2 + q + 1) - (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q)
    (node : ∀ t b K, G (t + 1) b K = (List.range (K + 1)).foldr (fun (j acc : ℕ) => max acc (min (G t (b + j) (K - j)) (G t b j))) 0)
    (s b K : ℕ) (ks : List ℕ) (hlen : ks.length = 2^s) (hfit : ks.sum ≤ K)
    (good : Pays q h b ks) : q*h ≤ G s b K := by
  induction s generalizing b K ks with
  | zero =>
    cases ks with
    | nil => simp at hlen
    | cons k tail =>
      have empty : tail = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons, pow_zero] at hlen
        omega
      subst tail
      have hgood : k ≤ q ∧ h ≤ k * (q+1-b) ∧ True := good
      have hkK : k ≤ K := by simpa using hfit
      rw [base]
      calc
        q*h ≤ q*(k*(q+1-b)) := Nat.mul_le_mul_left _ hgood.2.1
        _ = q*(q+1-b)*k := by ring
        _ ≤ _ := Nat.mul_le_mul (base_factor q b) (le_min hkK hgood.1)
  | succ s ih =>
    let d := 2^s
    let left := ks.take d
    let right := ks.drop d
    have splitList : left ++ right = ks := List.take_append_drop _ _
    have mylen : ks.length = d+d := by simpa [d, pow_succ, Nat.mul_two] using hlen
    have lenL : left.length = 2^s := by simp [left, List.length_take, min_eq_left (show d ≤ ks.length by omega), d]
    have lenR : right.length = 2^s := by simp [right, List.length_drop, mylen, d]
    have sumSplit : left.sum + right.sum = ks.sum := by rw [← List.sum_append, splitList]
    have good' := (pays_append q h b left right).mp (splitList.symm ▸ good)
    have liftL := ih b left.sum left lenL (le_refl _) good'.1
    have liftR := ih (b+left.sum) (K-left.sum) right lenR (by omega) good'.2
    rw [node]
    exact (le_min liftR liftL).trans (member_le_max _ _ left.sum (List.mem_range.mpr (by omega)))

lemma buildChain (q h : ℕ) (Ready : ℕ → ℕ → Prop)
    (advance : ∀ x t : ℕ, x ≤ q + 1 → Ready x (t + 1) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ q ∧ k ≤ x ∧ h ≤ k * x ∧ Ready (x-k) t)
    (x n : ℕ) (hx : x ≤ q + 1) (hr : Ready x n) :
    ∃ ks : List ℕ, ks.length = n ∧ ks.sum ≤ x ∧ Pays q h (q + 1 - x) ks := by
  induction n generalizing x with
  | zero => exact ⟨[], rfl, by simp, by trivial⟩
  | succ t ih =>
    obtain ⟨k, _, hkq, hkx, hkpay, hnext⟩ := advance x t hx hr
    obtain ⟨ks, hlen, hsum, hpays⟩ := ih (x - k) (by omega) hnext
    refine ⟨k :: ks, by simp [hlen], ?_, ?_⟩
    · rw [List.sum_cons]
      omega
    · change k ≤ q ∧ h ≤ k * (q + 1 - (q + 1 - x)) ∧
        Pays q h ((q + 1 - x) + k) ks
      have back : q + 1 - (q + 1 - x) = x := by omega
      have pos : (q + 1 - x) + k = q + 1 - (x - k) := by omega
      rw [back, pos]
      exact ⟨hkq, hkpay, hpays⟩

end PEqualNP.Outside.Ladder1395
