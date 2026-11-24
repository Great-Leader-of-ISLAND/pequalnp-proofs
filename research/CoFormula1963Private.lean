import Mathlib

namespace CoFormula1963Private

variable {P L E N K : Type*}

/-- Every row of a labeled rectangle carrying f also carries e. -/
def Dominates (lab : K → P ⊕ L) (rows : K → E → Prop)
    (v : P ⊕ L) (f e : E) : Prop :=
  ∀ k, lab k = v → rows k f → rows k e

/-- A private incidence has no other row at that endpoint whose rectangle
    membership profile is contained in the given edge's profile. -/
def PointPrivate (pt : E → P) (lab : K → P ⊕ L) (rows : K → E → Prop) (e : E) : Prop :=
  ∀ f, pt f = pt e → f ≠ e → ¬ Dominates lab rows (.inl (pt e)) f e

def LinePrivate (ln : E → L) (lab : K → P ⊕ L) (rows : K → E → Prop) (e : E) : Prop :=
  ∀ g, ln g = ln e → g ≠ e → ¬ Dominates lab rows (.inr (ln e)) g e

/-- At an incidence e, choose any other row f at its point and any other row
    g at its line. A negative containing the opposite endpoints of f and g
    forces their KW labels. If both profiles lay below e's, disjointness at
    the single cell (e,y) would identify a point label with a line label. -/
theorem every_edge (pt : E → P) (ln : E → L)
    (yp : N → P → Bool) (yl : N → L → Bool)
    (lab : K → P ⊕ L) (rows : K → E → Prop) (cols : K → N → Prop)
    (cover : ∀ e y, ∃ k, rows k e ∧ cols k y)
    (unique : ∀ e y a b, rows a e → cols a y → rows b e → cols b y → a = b)
    (labelled : ∀ e y k, rows k e → cols k y →
      (lab k = .inl (pt e) ∧ yp y (pt e) = false) ∨
      (lab k = .inr (ln e) ∧ yl y (ln e) = false))
    (cross : ∀ e f g, pt f = pt e → f ≠ e → ln g = ln e → g ≠ e →
      ∃ y, yl y (ln f) = true ∧ yp y (pt g) = true)
    (e : E) : PointPrivate pt lab rows e ∨ LinePrivate ln lab rows e := by
  classical
  by_cases h : PointPrivate pt lab rows e
  · exact Or.inl h
  right
  unfold PointPrivate at h
  push_neg at h
  obtain ⟨f,fp,fe,fd⟩ := h
  intro g gl ge gd
  obtain ⟨y,yf,yg⟩ := cross e f g fp fe gl ge
  obtain ⟨a,ra,ca⟩ := cover f y
  obtain ⟨b,rb,cb⟩ := cover g y
  have la : lab a = .inl (pt e) := by
    rcases labelled f y a ra ca with ha | ha
    · simpa only [fp] using ha.1
    · exact False.elim (by simpa [yf] using ha.2)
  have lb : lab b = .inr (ln e) := by
    rcases labelled g y b rb cb with hb | hb
    · exact False.elim (by simpa [yg] using hb.2)
    · simpa only [gl] using hb.1
  have eq : a = b := unique e y a b (fd a la ra) ca (gd b lb rb) cb
  subst b
  rw [la] at lb
  cases lb

open scoped BigOperators

theorem count_private [Fintype E] (p l : E → Bool)
    (cover : ∀ e, p e = true ∨ l e = true) :
    Fintype.card E ≤ (∑ e, if p e then 1 else 0) + (∑ e, if l e then 1 else 0) := by
  rw [← Finset.sum_add_distrib]
  calc
    Fintype.card E = ∑ _e : E, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun e _ => by
      rcases cover e with h | h
      · simp [h]
      · simp [h]

#print axioms every_edge
end CoFormula1963Private
