import PEqualNP.CoFormula1963Geometry
import PEqualNP.CoFormula1963Protocol
import PEqualNP.CoFormula1963Private

namespace CoFormula1963Link
open CoFormula1963Geometry CoFormula1963Protocol CoFormula1963Private

section ListCells
variable {ι α β : Type*} [DecidableEq α] [DecidableEq β]

private theorem head_add (i : α) (j : β) (r : Rect ι α β) (rs : List (Rect ι α β)) :
    multiplicity i j (r::rs) = hits i j r + multiplicity i j rs := rfl

theorem present (i : α) (j : β) (rs : List (Rect ι α β)) (h : multiplicity i j rs ≠ 0) :
    ∃ r ∈ rs, i∈r.rows ∧ j∈r.cols := by
  induction rs with
  | nil => exact False.elim (h rfl)
  | cons r rs ih =>
    by_cases here : i∈r.rows ∧ j∈r.cols
    · exact ⟨r,by simp,here⟩
    · have tail : multiplicity i j rs ≠ 0 := by simpa [head_add,hits,here] using h
      obtain ⟨w,mem,iw,jw⟩ := ih tail
      exact ⟨w,List.mem_cons_of_mem _ mem,iw,jw⟩

theorem positive (i : α) (j : β) (rs : List (Rect ι α β)) (r : Rect ι α β)
    (member : r∈rs) (here : i∈r.rows ∧ j∈r.cols) : 1 ≤ multiplicity i j rs := by
  induction rs with
  | nil => simp at member
  | cons w rs ih =>
    rw [head_add]
    rcases List.mem_cons.mp member with eq | m
    · subst w
      simp [hits,here]
    · have := ih m
      omega

theorem at_most_one (i : α) (j : β) (rs : List (Rect ι α β)) (atMost : multiplicity i j rs ≤ 1)
    (a b : Rect ι α β) (ma : a∈rs) (mb : b∈rs)
    (ha : i∈a.rows ∧ j∈a.cols) (hb : i∈b.rows ∧ j∈b.cols) : a=b := by
  induction rs with
  | nil => simp at ma
  | cons w ws ih =>
    rw [head_add] at atMost
    rcases List.mem_cons.mp ma with ea | tailA <;> rcases List.mem_cons.mp mb with eb | tailB
    · exact ea.trans eb.symm
    · subst w
      have hh := positive i j ws b tailB hb
      simp only [hits,if_pos ha] at atMost
      omega
    · subst w
      have hh := positive i j ws a tailA ha
      simp only [hits,if_pos hb] at atMost
      omega
    · exact ih (by omega) tailA tailB

end ListCells

abbrev E := {pl : V × V // inc pl.1 pl.2}
abbrev Y := Fin 18 × V
abbrev X := V ⊕ V

def pos (e : E) : X → Bool
  | .inl p => decide (p = e.val.1)
  | .inr l => decide (l = e.val.2)

def neg (y : Y) : X → Bool
  | .inl p => decide (p ∈ quad y.1 y.2)
  | .inr l => decide (clear (quad y.1 y.2) l)

def rs (t : Expr X) := partition pos neg t Finset.univ Finset.univ
abbrev ID (t : Expr X) := {r // r ∈ rs t}

theorem rects_count (t : Expr X) : (rs t).length = t.leaves :=
  partition_length pos neg _ _ _

theorem exact_cell (t : Expr X) (e : E) (y : Y) : multiplicity e y (rs t) = 1 := by
  simpa [rs] using partition_exact pos neg t Finset.univ Finset.univ e y

set_option maxHeartbeats 2000000

private theorem negative_line (y : Y) (l : V) (h : clear (quad y.1 y.2) l) :
    neg y (.inr l) = true := by
  unfold neg
  apply decide_eq_true
  exact h

private theorem negative_point (y : Y) (p : V) (h : p ∈ quad y.1 y.2) :
    neg y (.inl p) = true := by
  unfold neg
  apply decide_eq_true
  exact h

/-- This statement starts with the circuit-free syntactic formula and its
    two actual Boolean tests. Every flag must have a private endpoint among
    the formula's own labeled rectangles. -/
theorem flag_private (t : Expr X) (accept : ∀ e : E, t.eval (pos e) = true)
    (reject : ∀ y : Y, t.eval (neg y) = false) (e : E) :
    PointPrivate (fun f : E => f.val.1) (fun k : ID t => k.val.label)
      (fun k f => f∈k.val.rows) e ∨
    LinePrivate (fun g : E => g.val.2) (fun k : ID t => k.val.label)
      (fun k g => g∈k.val.rows) e := by
  apply every_edge (yp:=fun y p => neg y (.inl p)) (yl:=fun y l => neg y (.inr l))
    (cols:=fun (k : ID t) y => y∈k.val.cols)
  · intro f y
    obtain ⟨r,h,hr,hc⟩ := present f y (rs t) (by rw [exact_cell]; decide)
    exact ⟨⟨r,h⟩,hr,hc⟩
  · intro f y a b ra ca rb cb
    apply Subtype.ext
    exact at_most_one f y (rs t) (by rw [exact_cell]) a.val b.val a.property b.property ⟨ra,ca⟩ ⟨rb,cb⟩
  · intro f y k hr hc
    obtain ⟨positive,negative⟩ := partition_sound pos neg t Finset.univ Finset.univ
      (fun x _ => accept x) (fun x _ => reject x) k.val k.property f hr y hc
    cases he : k.val.label with
    | inl p =>
      have ep : p = f.val.1 := by simpa [pos,he] using positive
      subst p
      exact Or.inl ⟨rfl,by simpa only [he] using negative⟩
    | inr l =>
      have el : l = f.val.2 := by simpa [pos,he] using positive
      subst l
      exact Or.inr ⟨rfl,by simpa only [he] using negative⟩
  · intro a f g fp fe gl ge
    have fa : f.val.2 ≠ a.val.2 := fun h => fe (Subtype.ext (Prod.ext fp h))
    have gb : g.val.1 ≠ a.val.1 := fun h => ge (Subtype.ext (Prod.ext h gl))
    obtain ⟨s,ha,hb⟩ := crossed a.val.1 a.val.2 f.val.2 g.val.1 a.property
      (by simpa only [←fp] using f.property) (by simpa only [←gl] using g.property) fa gb
    change ∃ y : Y, neg y (.inr f.val.2) = true ∧ neg y (.inl g.val.1) = true
    exact ⟨((0 : Fin 18),s),negative_line (0,s) f.val.2 ha,negative_point (0,s) g.val.1 hb⟩

#print axioms flag_private
end CoFormula1963Link
