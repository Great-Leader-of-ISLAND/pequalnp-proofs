import PEqualNP.CoFormula1963Link

namespace CoFormula1963Mass
open CoFormula1963Geometry CoFormula1963Protocol CoFormula1963Private CoFormula1963Link
open scoped BigOperators

/-- Reorganize an occurrence sum by the raw label. No assumption on unique
    leaf labels or unique rectangles is involved. -/
theorem by_label {I A : Type*} [Fintype A] [DecidableEq A]
    (label : I → A) (w : I → ℕ) (xs : List I) :
    (∑ a : A, ((xs.filter fun x => label x = a).map w).sum) = (xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    calc
      _ = ∑ a : A, ((if label x=a then w x else 0) +
          ((xs.filter fun z => label z=a).map w).sum) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : label x=a <;> simp [h]
      _ = _ := by rw [Finset.sum_add_distrib,ih]; simp

def area (r : Rect X E Y) : ℕ := ∑ e : E, ∑ y : Y, hits e y r

theorem cell_sum (rs : List (Rect X E Y)) :
    (rs.map area).sum = ∑ e : E, ∑ y : Y, multiplicity e y rs := by
  induction rs with
  | nil => simp [multiplicity]
  | cons r rs ih =>
    change area r + (rs.map area).sum =
      ∑ e : E, ∑ y : Y, (hits e y r + multiplicity e y rs)
    simp only [Finset.sum_add_distrib,← ih,area]

theorem flag_count : Fintype.card E = 52 := by decide +kernel

theorem area_total (t : Expr X) :
    ∑ a : X, (((rs t).filter fun r => r.label=a).map area).sum = 12168 := by
  rw [by_label,cell_sum]
  simp [exact_cell,flag_count,Y,V]

private theorem ones {A : Type*} (xs : List A) : (xs.map (fun _ => (1:ℕ))).sum = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih,Nat.add_comm]

theorem occurrence_total (t : Expr X) :
    ∑ a : X, ((rs t).filter fun r => r.label=a).length = t.leaves := by
  have h := by_label Rect.label (fun _ : Rect X E Y => 1) (rs t)
  simpa only [ones,rects_count] using h

noncomputable def privatePoint (t : Expr X) (p : V) : ℕ := by
  classical
  exact ∑ e : E, if e.val.1=p then
    (if PointPrivate (fun f : E => f.val.1) (fun k : ID t => k.val.label)
      (fun k f => f∈k.val.rows) e then 1 else 0) else 0

noncomputable def privateLine (t : Expr X) (l : V) : ℕ := by
  classical
  exact ∑ e : E, if e.val.2=l then
    (if LinePrivate (fun f : E => f.val.2) (fun k : ID t => k.val.label)
      (fun k f => f∈k.val.rows) e then 1 else 0) else 0

theorem private_total (t : Expr X) (accept : ∀ e : E, t.eval (pos e) = true)
    (reject : ∀ y : Y, t.eval (neg y) = false) :
    52 ≤ (∑ p : V, privatePoint t p) + (∑ l : V, privateLine t l) := by
  classical
  unfold privatePoint privateLine
  conv_rhs =>
    lhs
    rw [Finset.sum_comm]
  conv_rhs =>
    rhs
    rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib,← flag_count]
  calc
    Fintype.card E = ∑ _e : E, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun e _ => by
      rcases flag_private t accept reject e with hp | hl
      · simp [hp]
      · simp [hl]

#print axioms area_total
#print axioms private_total
end CoFormula1963Mass
