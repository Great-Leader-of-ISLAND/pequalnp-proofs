import Mathlib

namespace CoThinCross2008
noncomputable section
open Finset
variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def pts (l : Fin N) := Finset.univ.filter fun p => I p l
def lines (p : Fin N) := Finset.univ.filter fun l => I p l

/-- A complete point-by-line rectangle in a no-four-cycle incidence graph
    of maximum degree d has at most d cells. -/
theorem rectangle_card (d : ℕ) (pd : ∀ p,(lines I p).card ≤ d) (ld : ∀ l,(pts I l).card ≤ d)
    (uniq : ∀ p r : Fin N,p ≠ r → ∃! l,I p l ∧ I r l)
    (P L : Finset (Fin N)) (inc : ∀ p∈P,∀ l∈L,I p l) : (P ×ˢ L).card ≤ d := by
  classical
  rw [Finset.card_product]
  by_cases pe : P.Nonempty
  · by_cases le : L.Nonempty
    · obtain ⟨p,hp⟩ := pe
      obtain ⟨l,hl⟩ := le
      have cb : L.card ≤ d := (Finset.card_le_card (show L ⊆ lines I p from
        fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc p hp z hz⟩)).trans (pd p)
      have rb : P.card ≤ d := (Finset.card_le_card (show P ⊆ pts I l from
        fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc z hz l hl⟩)).trans (ld l)
      by_cases small : P.card ≤ 1
      · simpa using Nat.mul_le_mul small cb
      · obtain ⟨p₁,h₁,p₂,h₂,ne⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge small)
        have one : L.card ≤ 1 := Finset.card_le_one_iff.mpr (by
          intro a b ha hb
          exact (uniq p₁ p₂ ne).unique ⟨inc p₁ h₁ a ha,inc p₂ h₂ a ha⟩
            ⟨inc p₁ h₁ b hb,inc p₂ h₂ b hb⟩)
        simpa using Nat.mul_le_mul rb one
    · simp [Finset.not_nonempty_iff_eq_empty.mp le]
  · simp [Finset.not_nonempty_iff_eq_empty.mp pe]

def one (a : Fin N) : Fin N → Bool := fun p => decide (p=a)
def anti (l : Fin N) : Fin N → Bool := fun p => decide (¬I p l)
def empty : Fin N → Bool := fun _ => false
abbrev Value (N : ℕ) := ℕ → (Fin N → Bool) → (Fin N → Bool) → Bool

private def yesPts (F : Value N) (j : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun p => F j (one p) empty=true
private def holdLines (F : Value N) (j : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun l => ∀ p∈yesPts F j,I p l

private def row (l : Fin N) : Finset (Fin N × Fin N) := (pts I l).image fun p => (p,l)

def insensitive (F : Value N) (D : Finset ℕ) (T : Finset (Fin N)) : Prop :=
  ∀ j∈D,∀ l∉T,∀ x : Fin N → Bool,F j x (one l)=F j x empty

def separates (F : Value N) (D : Finset ℕ) (p l : Fin N) : Prop :=
  I p l ∧ ∃ j∈D,F j (one p) (one l)=true ∧ F j (anti I l) (one l)=false

/-- Only singleton line slices matter here. Each exceptional line costs at
    most d incidences. A gate separates at most d further incidences. -/
theorem combined_card (d : ℕ) (pd : ∀ p,(lines I p).card ≤ d) (ld : ∀ l,(pts I l).card ≤ d)
    (uniq : ∀ p r : Fin N,p ≠ r → ∃! l,I p l ∧ I r l)
    (F : Value N) (D : Finset ℕ) (T : Finset (Fin N))
    (mono : ∀ j∈D,∀ x y : Fin N→Bool,(∀ p,x p=true → y p=true) → F j x empty=true → F j y empty=true)
    (small : insensitive F D T) (E : Finset (Fin N × Fin N))
    (which : ∀ e∈E,I e.1 e.2 ∧ (e.2∉T → separates I F D e.1 e.2)) :
    E.card ≤ (T.card+D.card)*d := by
  classical
  let rect := fun j => yesPts F j ×ˢ holdLines I F j
  have contained : E ⊆ T.biUnion (row I) ∪ D.biUnion rect := by
    rintro ⟨p,l⟩ he
    obtain ⟨inc,outside⟩ := which _ he
    by_cases h : l∈T
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨l,h,Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨by simp,inc⟩,rfl⟩⟩
    · obtain ⟨_,j,hj,on,off⟩ := outside h
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨j,hj,Finset.mem_product.mpr ⟨?_,?_⟩⟩
      · exact Finset.mem_filter.mpr ⟨by simp,(small j hj l h (one p)) ▸ on⟩
      · apply Finset.mem_filter.mpr
        refine ⟨by simp,?_⟩
        intro v hv
        by_contra nv
        have order (a) (ha : one v a=true) : anti I l a=true := by
          have eq : a=v := by simpa [one] using ha
          simpa [anti,eq] using nv
        have wrong := mono j hj _ _ order (Finset.mem_filter.mp hv).2
        rw [small j hj l h (anti I l)] at off
        exact Bool.false_ne_true (off.symm.trans wrong)
  have rc (l : Fin N) : (row I l).card ≤ d := Finset.card_image_le.trans (ld l)
  have cc (j : ℕ) : (rect j).card ≤ d := rectangle_card I d pd ld uniq _ _ (by
    intro p hp l hl
    exact (Finset.mem_filter.mp hl).2 p hp)
  have sumr : (T.biUnion (row I)).card ≤ T.card*d := by
    calc _ ≤ ∑ i ∈ T,(row I i).card := Finset.card_biUnion_le
         _ ≤ ∑ _i ∈ T,d := Finset.sum_le_sum (fun l _ => rc l)
         _ = _ := by simp
  have sumc : (D.biUnion rect).card ≤ D.card*d := by
    calc _ ≤ ∑ i ∈ D,(rect i).card := Finset.card_biUnion_le
         _ ≤ ∑ _i ∈ D,d := Finset.sum_le_sum (fun j _ => cc j)
         _ = _ := by simp
  calc E.card ≤ (T.biUnion (row I) ∪ D.biUnion rect).card := Finset.card_le_card contained
       _ ≤ (T.biUnion (row I)).card+(D.biUnion rect).card := Finset.card_union_le
       _ ≤ T.card*d+D.card*d := Nat.add_le_add sumr sumc
       _ = _ := (Nat.add_mul _ _ _).symm

theorem focused_card (d : ℕ) (ld : ∀ l,(pts I l).card ≤ d)
    (F : Value N) (D : Finset ℕ) (T : Finset (Fin N)) (owner : ℕ → Fin N)
    (small : insensitive F D T) (base : ∀ j∈D,F j (one (owner j)) empty=false)
    (E : Finset (Fin N × Fin N))
    (which : ∀ e∈E,I e.1 e.2 ∧ ∃ j∈D,e.1=owner j ∧ F j (one e.1) (one e.2)=true) :
    E.card ≤ T.card*d := by
  classical
  have sub : E ⊆ T.biUnion (row I) := by
    rintro ⟨p,l⟩ he
    obtain ⟨inc,j,hj,rfl,hit⟩ := which _ he
    have hl : l∈T := by
      by_contra miss
      rw [small j hj l miss _,base j hj] at hit
      exact Bool.false_ne_true hit
    exact Finset.mem_biUnion.mpr ⟨l,hl,Finset.mem_image.mpr ⟨_,Finset.mem_filter.mpr ⟨by simp,inc⟩,rfl⟩⟩
  calc E.card ≤ (T.biUnion (row I)).card := Finset.card_le_card sub
       _ ≤ ∑ l ∈ T,(row I l).card := Finset.card_biUnion_le
       _ ≤ ∑ _l ∈ T,d := Finset.sum_le_sum (fun l _ => Finset.card_image_le.trans (ld l))
       _ = _ := by simp

/-- Column regularity and unique joining lines give the required dual degree
    bound by disjoint counting, with no duality assumption. -/
theorem point_degree {q : ℕ} (positive : 0<q) (order : N=q^2+q+1)
    (deg : ∀ l,(pts I l).card=q+1)
    (uniq : ∀ p r : Fin N,p ≠ r → ∃! l,I p l ∧ I r l)
    (p : Fin N) : (lines I p).card≤q+1 := by
  classical
  let rest := fun l => (pts I l).erase p
  have disjoint : (↑(lines I p) : Set (Fin N)).PairwiseDisjoint rest := by
    intro a ha b hb ne
    refine Finset.disjoint_left.mpr ?_
    intro r ra rb
    obtain ⟨rp,ina⟩ := Finset.mem_erase.mp ra
    have inb := (Finset.mem_erase.mp rb).2
    exact ne ((uniq r p rp).unique
      ⟨(Finset.mem_filter.mp ina).2,(Finset.mem_filter.mp ha).2⟩
      ⟨(Finset.mem_filter.mp inb).2,(Finset.mem_filter.mp hb).2⟩)
  have each (l : Fin N) (hl : l∈lines I p) : (rest l).card=q := by
    have m : p∈pts I l := Finset.mem_filter.mpr ⟨by simp,(Finset.mem_filter.mp hl).2⟩
    simp [rest,Finset.card_erase_of_mem m,deg]
  have inclusion : (lines I p).biUnion rest ⊆ Finset.univ.erase p := by
    intro r hr
    obtain ⟨l,_,through⟩ := Finset.mem_biUnion.mp hr
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp through).1,Finset.mem_univ _⟩
  have bound := Finset.card_le_card inclusion
  rw [Finset.card_biUnion disjoint,Finset.sum_congr rfl each] at bound
  have out_card : (Finset.univ.erase p).card=N-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  simp only [Finset.sum_const,smul_eq_mul,out_card] at bound
  have Npred : N-1=q*(q+1) := by rw [order]; simp <;> ring
  rw [Npred] at bound
  by_contra! greater
  have bad := Nat.mul_lt_mul_of_pos_right greater positive
  nlinarith

/-- In particular, 100 times this upper bound is strictly below the
    48-percent hard-case threshold in R_meta_2008_401. -/
theorem thin_threshold {N q t r : ℕ} (qbig : 100<q) (positive : 0<N) (thin : 3*(t+r)≤N) :
    100*((t+r)*(q+1))<48*(N*q) := by
  have one : 100*(q+1)<144*q := by omega
  have many := Nat.mul_lt_mul_of_pos_left one positive
  have cap := Nat.mul_le_mul_right (100*(q+1)) thin
  nlinarith

end
end CoThinCross2008
