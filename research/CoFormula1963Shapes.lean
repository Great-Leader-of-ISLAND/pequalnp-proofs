import PEqualNP.CoFormula1963Area

namespace CoFormula1963Shapes
open CoFormula1963Local CoFormula1963Area

/- No normalization assumptions on the rectangle family. Duplicate row masks
    and empty rectangles with an assigned label are included in the bounds. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem twoAny : ∀ a b : Fin 16, feasible [a.val,b.val] = true → localBound [a.val,b.val] := by
  intro a
  fin_cases a <;> decide +kernel

theorem threeAny : ∀ a b c : Fin 16,
    feasible [a.val,b.val,c.val] = true → localBound [a.val,b.val,c.val] := by
  intro a
  fin_cases a <;> decide +kernel

theorem small {F : List ℕ} (valid : ∀ m ∈ F, m < 16) (short : F.length ≤ 3)
    (h : feasible F = true) : localBound F := by
  cases F with
  | nil => exact (by decide : feasible [] = true → localBound []) h
  | cons a xs =>
    have ha := valid a (by simp)
    cases xs with
    | nil => exact oneMask ⟨a,ha⟩ h
    | cons b ys =>
      have hb := valid b (by simp)
      cases ys with
      | nil => exact twoAny ⟨a,ha⟩ ⟨b,hb⟩ h
      | cons c zs =>
        have hc := valid c (by simp)
        cases zs with
        | nil => exact threeAny ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ h
        | cons d ds => simp at short; omega

theorem private_bound (F : List ℕ) : privateRows F ≤ 4 := by
  unfold privateRows
  exact (List.length_filter_le _ _).trans_eq (by simp)

theorem weight_bound (u : ℕ) : weight u ≤ 4 := by
  unfold weight
  exact (List.length_filter_le _ _).trans_eq (by simp)

theorem feasible_from_columns {α : Type*} (F : List ℕ) (ys : List α) (forced used : α → ℕ)
    (every : ∀ m ∈ one ++ two, ∃ y ∈ ys, forced y = m)
    (selected : ∀ y ∈ ys, Selection F (used y))
    (contains : ∀ y ∈ ys, used y &&& forced y = forced y) : feasible F = true := by
  unfold feasible
  apply List.all_eq_true.mpr
  intro m hm
  obtain ⟨y,hy,rfl⟩ := every m hm
  have low := cost_of_column (selected y hy) (contains y hy)
  have high := weight_bound (used y)
  exact decide_eq_true (by omega)

theorem monotone_weight : ∀ u m : Fin 16, u.val &&& m.val = m.val →
    weight m.val ≤ weight u.val := by decide +kernel

/-- Apply the local certificate to a physical list, keeping its original
    order and multiplicities. For four or more rectangles one only needs to
    count the forced single cells directly. -/
theorem charge (F : List ℕ) (valid : ∀ m ∈ F, m < 16) (ok : feasible F = true) (area : ℕ) :
    (27*singles F + 9*pairs F ≤ area → 216 ≤ area →
      1044+189*privateRows F ≤ 396*F.length+area) ∧
    (18*singles F + 18*pairs F ≤ area → 288 ≤ area →
      1116+189*privateRows F ≤ 396*F.length+area) := by
  by_cases short : F.length ≤ 3
  · have h := expandLocal (small valid short ok) area
    exact ⟨fun a _ => h.1 a,fun a _ => h.2 a⟩
  · have h := fourOrMore F.length (privateRows F) area (by omega) (private_bound F)
    exact ⟨fun _ a => h.1 a,fun _ a => h.2 a⟩

#print axioms charge
end CoFormula1963Shapes
