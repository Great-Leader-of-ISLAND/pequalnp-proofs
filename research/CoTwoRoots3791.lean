import PEqualNP.CoFormula1963Geometry

namespace CoTwoRoots3791
open CoFormula1963Geometry

abbrev X := Sum V V
abbrev Y := Fin 18 × V

def onRow (y : Y) : X → Prop
  | .inl p => p ∈ quad y.1 y.2
  | .inr l => clear (quad y.1 y.2) l

def flag : X → X → Prop
  | .inl p, .inr l => inc p l
  | .inr l, .inl p => inc p l
  | _, _ => False

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem pp : ∀ p q : V, ∃ r ∈ ([4,6] : List (Fin 18)), ∃ s : V,
    p ∈ quad r s ∧ q ∈ quad r s := by
  intro p
  fin_cases p <;> decide +kernel

private theorem ll : ∀ l m : V, ∃ r ∈ ([4,6] : List (Fin 18)), ∃ s : V,
    clear (quad r s) l ∧ clear (quad r s) m := by
  intro l
  fin_cases l <;> decide +kernel

theorem joint (a b : X) (h : ¬flag a b) : ∃ y : Y, onRow y a ∧ onRow y b := by
  cases a with
  | inl p =>
    cases b with
    | inl q =>
      obtain ⟨r,_,s,hp,hq⟩ := pp p q
      exact ⟨(r,s),hp,hq⟩
    | inr l =>
      obtain ⟨s,hp,hl⟩ := cooccur p l h
      exact ⟨(0,s),hp,hl⟩
  | inr l =>
    cases b with
    | inl q =>
      obtain ⟨s,hq,hl⟩ := cooccur q l h
      exact ⟨(0,s),hl,hq⟩
    | inr m =>
      obtain ⟨r,_,s,hl,hm⟩ := ll l m
      exact ⟨(r,s),hl,hm⟩

/-- Two raw disjunctions whose product is false on every tested negative
    have only incidence flags across the two supports. -/
theorem rectangle (A B : Set X)
    (clean : ∀ y : Y, ¬((∃ a ∈ A, onRow y a) ∧ (∃ b ∈ B, onRow y b))) :
    ∀ a ∈ A, ∀ b ∈ B, flag a b := by
  intro a ha b hb
  by_contra bad
  obtain ⟨y,hya,hyb⟩ := joint a b bad
  exact clean y ⟨⟨a,ha,hya⟩,⟨b,hb,hyb⟩⟩

theorem star (A B : Set V)
    (clean : ∀ p ∈ A, ∀ l ∈ B, inc p l)
    (p q : V) (hp : p ∈ A) (hq : q ∈ A) (different : q ≠ p) :
    ∀ l ∈ B, ∀ m ∈ B, m = l := by
  intro l hl m hm
  by_contra ne
  exact no_four p l m q (clean p hp l hl) (clean p hp m hm)
    (clean q hq l hl) ne different (clean q hq m hm)

#print axioms rectangle
#print axioms star
end CoTwoRoots3791
