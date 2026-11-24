import PEqualNP.CoMerge4055

namespace CoZone4055
open CoMerge4055

variable {W U I : Type} [DecidableEq W] [DecidableEq U] [Fintype U]

/-- A shared binary DAG, described by its successive output values. -/
def Good (f : W → W → W) (bank : Finset W) : List W → Prop
  | [] => True
  | z :: zs => (∃ a ∈ bank, ∃ b ∈ bank, z = f a b) ∧ Good f (insert z bank) zs

def spent (V : I → W → Finset U) (i : I) : List W → Nat
  | [] => 0
  | z :: zs => (if 2 ≤ (V i z).card then 1 else 0) + spent V i zs

private theorem attain (f : W → W → W) (V : I → W → Finset U) (i : I)
    (step : ∀ i a b, 2 ≤ (V i (f a b)).card → V i (f a b) ⊆ V i a ∪ V i b)
    (zs : List W) (A : Finset W) (hg : Good f A zs)
    (T : Finset (Finset U)) (n : Nat) (hb : Budget T n)
    (tiny : ∀ u : Finset U, u.card ≤ 1 → u ∈ T)
    (ha : ∀ w ∈ A, V i w ∈ T) :
    ∃ R : Finset (Finset U), Budget R (n + spent V i zs) ∧
       ∀ w ∈ A ∪ zs.toFinset, V i w ∈ R := by
  classical
  induction zs generalizing A T n with
  | nil => exact ⟨T, by simpa [spent] using hb, by simpa using ha⟩
  | cons z zs ih =>
    obtain ⟨⟨a, aa, b, ab, e⟩, good⟩ := hg
    have areas : A ∪ (z::zs).toFinset = insert z A ∪ zs.toFinset := by
      ext w
      simp [or_left_comm,or_assoc,or_comm]
    by_cases big : 2 ≤ (V i z).card
    · have p : V i z ⊆ V i a ∪ V i b := by
        simpa only [e] using step i a b (by simpa only [e] using big)
      have hb' := CoMerge4055.add hb (ha _ aa) (ha _ ab) p
      have small' : ∀ u : Finset U, u.card ≤ 1 → u ∈ insert (V i z) T :=
        fun u hu => Finset.mem_insert_of_mem (tiny _ hu)
      have ha' : ∀ w ∈ insert z A, V i w ∈ insert (V i z) T := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | h
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (ha _ h)
      obtain ⟨R, budget, cov⟩ := ih _ good _ _ hb' small' ha'
      refine ⟨R, ?_, ?_⟩
      · simpa [spent,big,Nat.add_assoc] using budget
      · simpa only [areas] using cov
    · have mz : V i z ∈ T := tiny _ (by omega)
      have ha' : ∀ w ∈ insert z A, V i w ∈ T := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | h
        · exact mz
        · exact ha _ h
      obtain ⟨R, budget, cov⟩ := ih _ good _ _ hb tiny ha'
      refine ⟨R, ?_, ?_⟩
      · simpa [spent,big] using budget
      · simpa only [areas] using cov

theorem wire_bound (f : W → W → W) (V : I → W → Finset U)
    (step : ∀ i a b, 2 ≤ (V i (f a b)).card → V i (f a b) ⊆ V i a ∪ V i b)
    (zs : List W) (A : Finset W) (hg : Good f A zs)
    (base : ∀ i w, w ∈ A → (V i w).card ≤ 1) (i : I) (w : W) (hw : w ∈ A ∪ zs.toFinset) :
    (V i w).card ≤ spent V i zs + 1 := by
  classical
  let T := Finset.univ.filter (fun s : Finset U => s.card ≤ 1)
  have hb : Budget T 0 := CoMerge4055.initial (by intro a ha; exact (Finset.mem_filter.mp ha).2)
  have tiny (u : Finset U) (hu : u.card ≤ 1) : u ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩
  obtain ⟨R, budget, cov⟩ := attain f V i step zs A hg T 0 hb tiny (fun y hy => tiny _ (base i y hy))
  exact CoMerge4055.single (by simpa using budget) (cov _ hw)

private theorem one_charge [DecidableEq I] (V : I → W → Finset U)
    (single : ∀ w i j, 2 ≤ (V i w).card → 2 ≤ (V j w).card → i=j) (J : Finset I) (w : W) :
    (∑ i ∈ J, (if 2 ≤ (V i w).card then 1 else 0 : Nat)) ≤ 1 := by
  classical
  by_cases h : ∃ j ∈ J, 2 ≤ (V j w).card
  · obtain ⟨j, hj, bj⟩ := h
    calc
      _ = ∑ i ∈ J, (if i=j then 1 else 0 : Nat) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases b : 2 ≤ (V i w).card
        · rw [if_pos b, if_pos (single w i j b bj)]
        · have ne : i ≠ j := fun e => b (e ▸ bj)
          simp [b,ne]
      _ ≤ 1 := by simp [hj]
  · have no (i : I) (hi : i∈J) : ¬2≤(V i w).card := fun b => h ⟨i,hi,b⟩
    have z : (∑ i ∈ J, (if 2 ≤ (V i w).card then 1 else 0 : Nat)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [no i hi]
    omega

theorem disjoint_prices [DecidableEq I] (f : W → W → W) (V : I → W → Finset U)
    (step : ∀ i a b, 2 ≤ (V i (f a b)).card → V i (f a b) ⊆ V i a ∪ V i b)
    (single : ∀ w i j, 2 ≤ (V i w).card → 2 ≤ (V j w).card → i=j)
    (zs : List W) (A : Finset W) (hg : Good f A zs)
    (base : ∀ i w, w ∈ A → (V i w).card ≤ 1) (J : Finset I) (d : I → Nat)
    (found : ∀ i ∈ J, ∃ w ∈ A ∪ zs.toFinset, d i ≤ (V i w).card) :
    (∑ i ∈ J, (d i - 1)) ≤ zs.length := by
  classical
  have quota (xs : List W) : (∑ i ∈ J, spent V i xs) ≤ xs.length := by
    induction xs with
    | nil => simp [spent]
    | cons z xs ih =>
      simp only [spent,Finset.sum_add_distrib,List.length_cons]
      have one := one_charge V single J z
      omega
  apply le_trans _ (quota zs)
  apply Finset.sum_le_sum
  intro i hi
  obtain ⟨w,hw,hit⟩ := found i hi
  have cap := wire_bound f V step zs A hg base i w hw
  omega

end CoZone4055
