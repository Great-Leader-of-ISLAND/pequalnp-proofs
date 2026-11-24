import PEqualNP.CoUnique3321

namespace CoUnique3321
open CoClean3321

/-- A monotone tail, interpreted after the unique raw reader of one point. -/
def tailGrows {P L : Type} (tail : Side P→Side L→Bool→Bool) :=
  ∀ {x x' y y' p p'}, (∀ i, x i=true → x' i=true) →
    (∀ l, y l=true → y' l=true) → (p=true → p'=true) →
    tail x y p=true → tail x' y' p'=true

theorem bypass_or {P L : Type} (I : P→L→Prop) (T : L→Prop)
    (B : Signal P L) (tail : Side P→Side L→Bool→Bool) (mono : tailGrows tail)
    (original : ∀ x y p, tail x y (p || B x y)=true ↔
       edge I x y ∨ (p=true ∧ neighbor T y))
    (pairOff : ∀ i l, I i l → B (single i) (single l)=false) :
    ∀ x y p, tail x y p=true ↔ edge I x y ∨ (p=true ∧ neighbor T y) := by
  classical
  intro x y p
  constructor
  · intro yes
    apply (original x y p).mp
    exact mono (fun _ h => h) (fun _ h => h) (fun h => by simp [h]) yes
  · rintro (⟨i,l,link,xi,yl⟩|⟨pOn,meet⟩)
    · have sx (j : P) (hj : single i j=true) : x j=true := by
        have e : j=i := of_decide_eq_true hj
        simpa [e] using xi
      have sy (j : L) (hj : single l j=true) : y j=true := by
        have e : j=l := of_decide_eq_true hj
        simpa [e] using yl
      have base : edge I (single i) (single l) :=
        ⟨i,l,link,by simp [single],by simp [single]⟩
      have orig := (original (single i) (single l) false).mpr (Or.inl base)
      have reduced : tail (single i) (single l) false=true := by
        simpa [pairOff i l link] using orig
      exact mono sx sy (by simp) reduced
    · have orig := (original x y p).mpr (Or.inr ⟨pOn,meet⟩)
      simpa [pOn] using orig

/-- A monotone exact graph function with an OR of two adjacent raw inputs as
head. The first subsequent individual read cannot be an indispensable AND if
the other operand sees the two raw bits symmetrically and if toggling the
first vertex at the second singleton may change only that AND. -/
theorem first_separate_and_alias {R : Type} (z : R) (B : Bool→R→Bool)
    (up : ∀ r, B true z=true → B true r=true)
    (tail : Bool→Bool→R→Bool)
    (low : tail true (false && B true z) z=false)
    (high : tail true (true && B true z) z=true) :
    ∀ (p l : Bool) (r : R), (p && B (p || l) r)=p := by
  have atBase : B true z=true := by
    cases v : B true z with
    | true => rfl
    | false =>
      have a : tail true false z=false := by simpa using low
      have b : tail true false z=true := by simpa [v] using high
      rw [a] at b
      contradiction
  intro p l r
  cases p <;> simp [up r atBase]

#print axioms CoUnique3321.bypass_or
#print axioms CoUnique3321.first_separate_and_alias
end CoUnique3321
