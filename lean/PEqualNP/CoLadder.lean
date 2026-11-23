import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1395

-- An integral potential for the remaining intervals.
def Cap (h x k n : ℕ) : Prop :=
  h * (k + 1) + n * k ^ 2 * (2 * k + 1) ≤ x * k * (2 * k + 1)

theorem cap_init {h x k n : ℕ} (hk : 0 < k) (hlo : (k-1)*x ≤ h)
    (hhi : h ≤ k*x) (hroot : n*(2*h+x) ≤ x^2) (hx : 0 < x) : Cap h x k n := by
  have hlo' : k*x ≤ h+x := by
    cases k with
    | zero => simp
    | succ a =>
      have ha : a*x ≤ h := by simpa using hlo
      simpa [Nat.succ_mul] using Nat.add_le_add_right ha x
  unfold Cap
  zify at hk hlo' hhi hroot hx ⊢
  have hA : 0 ≤ (k : ℤ)*x-h := sub_nonneg.mpr hhi
  have hB0 : 0 ≤ (h : ℤ)+x-k*x := sub_nonneg.mpr hlo'
  have hB : 0 ≤ 2*(h : ℤ)*(k+1)-((k : ℤ)-1)*(2*k+1)*x := by
    nlinarith only [mul_nonneg hB0 (show 0 ≤ 2*(k : ℤ)+1 by positivity),
      show 0 ≤ (h : ℤ) by positivity]
  by_contra! hbad
  have hb := mul_pos (sub_pos.mpr hbad) (show 0 < 2*(h : ℤ)+x by positivity)
  have hw := mul_nonneg (sub_nonneg.mpr hroot) (show 0 ≤ (k : ℤ)^2*(2*k+1) by positivity)
  nlinarith only [hb, hw, mul_nonneg hA hB]

theorem cap_raise {h x k n : ℕ} (hk : 0 < k) (hsmall : k*x ≤ h)
    (hc : Cap h x k n) : Cap h x (k+1) n := by
  unfold Cap at hc ⊢
  zify at hk hsmall hc ⊢
  have hs := mul_nonneg (sub_nonneg.mpr hsmall)
    (show 0 ≤ ((k : ℤ)+1)*(2*k+1)*(2*k+3) by positivity)
  have hw := mul_nonneg (sub_nonneg.mpr hc)
    (show 0 ≤ ((k : ℤ)+1)^2*(2*k+3) by positivity)
  by_contra! hbad
  have hb := mul_pos (sub_pos.mpr hbad) (show 0 < (k : ℤ)^2*(2*k+1) by positivity)
  nlinarith only [hb, hw, hs, show 0 ≤ (h : ℤ)*(k : ℤ)^2 by positivity]

theorem cap_width {h x k n : ℕ} (hk : 0 < k) (hc : Cap h x k (n+1)) : k ≤ x := by
  unfold Cap at hc
  by_contra! hbad
  have hs := Nat.mul_lt_mul_of_pos_right hbad (show 0 < k*(2*k+1) by positivity)
  nlinarith only [hc, hs, Nat.zero_le (h*(k+1)), Nat.zero_le (n*k^2*(2*k+1))]

theorem cap_width_lt {h x k n : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hc : Cap h x k (n+1)) : k < x := by
  have hle := cap_width hk hc
  by_contra! hbad
  have he : x=k := by omega
  subst x
  unfold Cap at hc
  have hp : 0 < h*(k+1) := by positivity
  nlinarith only [hc, hp, Nat.zero_le (n*k^2*(2*k+1))]

theorem cap_step {h x k n : ℕ} (hk : 0 < k) (hc : Cap h x k (n+1)) :
    Cap h (x-k) k n := by
  have he := Nat.sub_add_cancel (cap_width hk hc)
  unfold Cap at hc ⊢
  rw [← he] at hc
  nlinarith only [hc]

theorem cap_legalize {h x k n u : ℕ} (hk : 0 < k) (hku : k ≤ u) (hu : h ≤ u*x)
    (hc : Cap h x k n) : ∃ j, k ≤ j ∧ j ≤ u ∧ h ≤ j*x ∧ Cap h x j n := by
  have aux : ∀ d t : ℕ, 0 < t → u=t+d → Cap h x t n →
      ∃ j, t ≤ j ∧ j ≤ u ∧ h ≤ j*x ∧ Cap h x j n := by
    intro d
    induction d with
    | zero =>
      intro t ht he hs
      have he' : u=t := by omega
      exact ⟨t, le_rfl, by omega, by simpa [he'] using hu, hs⟩
    | succ d ih =>
      intro t ht he hs
      by_cases hgood : h ≤ t*x
      · exact ⟨t, le_rfl, by omega, hgood, hs⟩
      · obtain ⟨j, htj, hju, hjx, hj⟩ :=
          ih (t+1) (by omega) (by omega) (cap_raise ht (by omega) hs)
        exact ⟨j, by omega, hju, hjx, hj⟩
  exact aux (u-k) k hk (by omega) hc

theorem cap_select {h x k n : ℕ} (hk : 0 < k) (hx : 0 < x) (hc : Cap h x k n) :
    ∃ j, k ≤ j ∧ h ≤ j*x ∧ Cap h x j n := by
  have hu : h ≤ (h+k)*x := by
    calc
      h ≤ h+k := by omega
      _ = (h+k)*1 := by simp
      _ ≤ (h+k)*x := Nat.mul_le_mul_left _ hx
  obtain ⟨j, hkj, _, hjx, hj⟩ := cap_legalize hk (by omega : k ≤ h+k) hu hc
  exact ⟨j, hkj, hjx, hj⟩

end PEqualNP.Outside.L_meta_1395

namespace PEqualNP.Outside.L_meta_1395

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
    exact (le_min liftR liftL).trans (member_le_max (fun j => min (G s (b+j) (K-j)) (G s b j)) (List.range (K+1)) left.sum (List.mem_range.mpr (by omega)))

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

end PEqualNP.Outside.L_meta_1395

open PEqualNP.Outside.L_meta_1395 in
theorem PEqualNP.Outside.L_meta_1395 : ∀ (q s : ℕ), 2 ≤ q → ∀ G : ℕ → ℕ → ℕ → ℕ, (∀ b K : ℕ, G 0 b K = ((q ^ 2 + q + 1) - (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q) → (∀ t b K : ℕ, G (t + 1) b K = (List.range (K + 1)).foldr (fun (j acc : ℕ) => max acc (min (G t (b + j) (K - j)) (G t b j))) 0) → q * (q * (q + 1 - 2 ^ s) / 2 ^ (s + 1)) ≤ G s 0 (q ^ 2 + q + 1) := by
  intro q s hq G base node
  let d := 2 ^ s
  let h := q * (q + 1 - d) / (2 * d)
  change q * h ≤ G s 0 (q^2 + q + 1)
  by_cases zero : h = 0
  · simp [zero]
  have hh : 0 < h := by omega
  have hdq : d ≤ q+1 := by
    by_contra! hn
    have e : q+1-d = 0 := Nat.sub_eq_zero_of_le (by omega)
    exact zero (by simp [h,e])
  have divbound : h * (2*d) ≤ q*(q+1-d) := Nat.div_mul_le_self _ _
  have sum := Nat.sub_add_cancel hdq
  have mulsum := congrArg (fun v : ℕ => q*v) sum
  have root : d*(2*h+(q+1)) ≤ (q+1)^2 := by nlinarith only [divbound, mulsum,hdq]
  let k := (h-1)/(q+1)+1
  have hk : 0 < k := by simp [k]
  have hlo : (k-1)*(q+1) ≤ h := by
    have small := Nat.div_mul_le_self (h-1) (q+1)
    simp only [k, Nat.add_sub_cancel] 
    omega
  have hhi : h ≤ k*(q+1) := by
    have upper := Nat.lt_mul_div_succ (h-1) (show 0<q+1 by omega)
    rw [Nat.mul_comm (q+1)] at upper
    dsimp [k]
    omega
  let Ready := fun x n => ∃ a : ℕ, 0 < a ∧ Cap h x a n
  have start : Ready (q+1) d := ⟨k,hk,cap_init hk hlo hhi root (by omega)⟩
  have advance (x n : ℕ) (hx : x ≤ q+1) (hr : Ready x (n+1)) :
      ∃ t, 1 ≤ t ∧ t ≤ q ∧ t ≤ x ∧ h ≤ t*x ∧ Ready (x-t) n := by
    obtain ⟨a, ha, ac⟩ := hr
    have ax := cap_width_lt hh ha ac
    obtain ⟨t,atle,hit,tc⟩ := cap_select ha (by omega) ac
    have ht : 0 < t := by omega
    have tx := cap_width_lt hh ht tc
    exact ⟨t,ht,by omega,by omega,hit,t,ht,cap_step ht tc⟩
  obtain ⟨ks,hlen,hfit,hp⟩ := buildChain q h Ready advance (q+1) d (by omega) start
  have paid : Pays q h 0 ks := by simpa using hp
  exact tree q h G base node s 0 (q^2+q+1) ks hlen (by omega) paid

#print axioms PEqualNP.Outside.L_meta_1395
