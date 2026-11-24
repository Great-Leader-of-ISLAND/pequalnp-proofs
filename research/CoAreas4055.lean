import PEqualNP.CoZone4055

namespace CoAreas4055
open CoZone4055

variable {I : Type} [Fintype I] [DecidableEq I]
abbrev Wire (I : Type) := Finset I × Finset I

def fuse (a b : Wire I) : Wire I := (a.1 ∪ b.1, a.2 ∪ b.2)
def view (N : I → Finset I) : Option I → Wire I → Finset I
  | none, w => if w.2 = ∅ then w.1 else ∅
  | some i, w => if w.2 ⊆ N i then w.2 else ∅

private theorem gate_subset (N : I → Finset I) (i : Option I) (a b : Wire I)
    (big : 2 ≤ (view N i (fuse a b)).card) :
    view N i (fuse a b) ⊆ view N i a ∪ view N i b := by
  cases i with
  | none =>
    by_cases h : a.2 ∪ b.2 = ∅
    · have h1 : a.2 = ∅ := (Finset.union_eq_empty.mp h).1
      have h2 : b.2 = ∅ := (Finset.union_eq_empty.mp h).2
      simp [fuse,view,h,h1,h2]
    · simp [fuse,view,h] at big
  | some p =>
    by_cases h : a.2 ∪ b.2 ⊆ N p
    · have h1 : a.2 ⊆ N p := fun j hj => h (Finset.mem_union_left _ hj)
      have h2 : b.2 ⊆ N p := fun j hj => h (Finset.mem_union_right _ hj)
      simp [fuse,view,h,h1,h2]
    · simp [fuse,view,h] at big

private theorem no_two (N : I → Finset I) (hN : ∀ p q, p ≠ q → (N p ∩ N q).card ≤ 1)
    (w : Wire I) (i j : Option I) (a : 2 ≤ (view N i w).card)
    (b : 2 ≤ (view N j w).card) : i = j := by
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some q =>
      by_cases h : w.2=∅
      · simp [view,h] at b
      · simp [view,h] at a
  | some p =>
    cases j with
    | none =>
      by_cases h : w.2=∅
      · simp [view,h] at a
      · simp [view,h] at b
    | some q =>
      by_cases e : p=q
      · rw [e]
      · by_cases hp : w.2 ⊆ N p
        · by_cases hq : w.2 ⊆ N q
          · have sub : w.2 ⊆ N p ∩ N q := fun x hx => Finset.mem_inter.mpr ⟨hp hx,hq hx⟩
            have bound := (Finset.card_le_card sub).trans (hN p q e)
            simp only [view,if_pos hp] at a
            omega
          · simp [view,hq] at b
        · simp [view,hp] at a

/-- Price all line-neighborhood factors and a pure-point factor in one shared OR network. -/
theorem neighborhood_prices (N : I → Finset I) (hN : ∀ p q, p ≠ q → (N p ∩ N q).card ≤ 1)
    (zs : List (Wire I)) (A : Finset (Wire I)) (hg : Good fuse A zs)
    (base : ∀ i w, w ∈ A → (view N i w).card ≤ 1)
    (J : Finset (Option I)) (d : Option I → Nat)
    (req : ∀ i ∈ J, ∃ w ∈ A ∪ zs.toFinset, d i ≤ (view N i w).card) :
    (∑ i ∈ J, (d i - 1)) ≤ zs.length :=
  disjoint_prices fuse (view N) (gate_subset N) (no_two N hN) zs A hg base J d req

end CoAreas4055
