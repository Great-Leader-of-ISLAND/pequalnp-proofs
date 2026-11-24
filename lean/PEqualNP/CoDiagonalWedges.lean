import Mathlib

namespace PEqualNP.Research.CoDiagonalWedges

theorem side_count {P L : Type*} [DecidableEq P] [DecidableEq L]
    (points : Finset P) (lines : Finset L) (neighbors : P → Finset L)
    (inside : ∀ p ∈ points, neighbors p ⊆ lines)
    (squareFree : ∀ p ∈ points, ∀ q ∈ points, p ≠ q → ∀ a ∈ neighbors p,
      ∀ b ∈ neighbors p, a ≠ b → a ∈ neighbors q → b ∈ neighbors q → False) :
    (∑ p ∈ points, (neighbors p).card * ((neighbors p).card - 1)) ≤ lines.card * (lines.card-1) := by
  classical
  have size (s : Finset L) : s.offDiag.card = s.card * (s.card-1) := by
    rw [Finset.offDiag_card, Nat.mul_sub, Nat.mul_one]
  let pairs := fun p => (neighbors p).offDiag
  have hdis : ∀ p ∈ points, ∀ q ∈ points, p ≠ q → Disjoint (pairs p) (pairs q) := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro ab hx hy
    obtain ⟨a,b,ne⟩ := Finset.mem_offDiag.mp hx
    obtain ⟨c,d,_⟩ := Finset.mem_offDiag.mp hy
    exact squareFree p hp q hq hpq ab.1 a ab.2 b ne c d
  have sub : points.biUnion pairs ⊆ lines.offDiag := by
    intro ab h
    obtain ⟨p,hp,hab⟩ := Finset.mem_biUnion.mp h
    obtain ⟨a,b,ne⟩ := Finset.mem_offDiag.mp hab
    exact Finset.mem_offDiag.mpr ⟨inside p hp a, inside p hp b, ne⟩
  have card := Finset.card_le_card sub
  rw [Finset.card_biUnion hdis, size] at card
  simpa only [pairs,size] using card

theorem combine_sides (P L N A B : ℕ) (hp : P ≤ N) (hl : L ≤ N)
    (ha : A ≤ L * (L-1)) (hb : B ≤ P * (P-1)) :
    A+B ≤ (N-1)*(P+L) := by
  have h1 := ha.trans (Nat.mul_le_mul_left L (Nat.sub_le_sub_right hl 1))
  have h2 := hb.trans (Nat.mul_le_mul_left P (Nat.sub_le_sub_right hp 1))
  calc
    A+B ≤ L*(N-1)+P*(N-1) := Nat.add_le_add h1 h2
    _ = (N-1)*(P+L) := by ring

end PEqualNP.Research.CoDiagonalWedges
