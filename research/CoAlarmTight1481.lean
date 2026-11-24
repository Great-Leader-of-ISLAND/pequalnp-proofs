import PEqualNP.CoFormula1963Complete
import PEqualNP.CoAlarmDerivative1481

namespace CoAlarmTight1481
open CoFormula1963Geometry CoFormula1963Protocol CoFormula1963Private CoFormula1963Link
open CoFormula1963Area CoFormula1963Packed CoFormula1963Flags CoFormula1963Local CoFormula1963Vertex
open CoFormula1963Complete CoAlarmDerivative1481
open scoped BigOperators

def strictSmall (F : List Nat) : Prop :=
    116 + 21*privateRows F < 44*F.length + 3*singles F + pairs F ∧
    124 + 21*privateRows F < 44*F.length + 2*singles F + 2*pairs F

instance (F : List Nat) : Decidable (strictSmall F) := by unfold strictSmall; infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem strictTwo : ∀ a b : Fin 16, feasible [a.val,b.val]=true → strictSmall [a.val,b.val] := by
  intro a
  fin_cases a <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem three : ∀ a b c : Fin 16, feasible [a.val,b.val,c.val]=true → strictSmall [a.val,b.val,c.val] := by
  intro a
  fin_cases a <;> decide +kernel

theorem charged (F : List Nat) (valid : ∀ m∈F,m < 16) (feas : feasible F=true)
    (twoLeaves : 2 ≤ F.length) (notAll : privateRows F < 4) (area : Nat) :
    (27*singles F+9*pairs F ≤ area → 216 ≤ area → 1044+189*privateRows F < 396*F.length+area) ∧
    (18*singles F+18*pairs F ≤ area → 288 ≤ area → 1116+189*privateRows F < 396*F.length+area) := by
  by_cases large : 4 ≤ F.length
  · constructor <;> omega
  · have cert : strictSmall F := by
      match F with
      | a::b::[] =>
        exact strictTwo ⟨a,valid a (by simp)⟩ ⟨b,valid b (by simp)⟩ feas
      | a::b::c::[] =>
        exact three ⟨a,valid a (by simp)⟩ ⟨b,valid b (by simp)⟩ ⟨c,valid c (by simp)⟩ feas
      | [] | [_] => simp at twoLeaves
      | _::_::_::_::_ => simp at large <;> omega
    rcases cert with ⟨hp,hl⟩
    constructor <;> omega

private theorem low_sum {A : Type*} (xs : List A) (a b : A → ℕ) (h : ∀ x∈xs, a x ≤ b x) :
    (xs.map a).sum ≤ (xs.map b).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact Nat.add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- The forced masks have total Hamming weight 216 at a point and 288 at a
    line. This argument works for any shape or number of local rectangles. -/
private theorem paid_forced {A : Type*} (ys : List A) (m u : A → ℕ) (ref : List ℕ)
    (hist : (ys.map m).Perm ref) (h : ∀ y, weight (m y) ≤ weight (u y)) :
    (ref.map weight).sum ≤ (ys.map fun y => weight (u y)).sum := by
  have sums := (hist.map weight).sum_eq
  rw [← sums,List.map_map]
  exact low_sum _ _ _ (fun y _ => h y)

private theorem present_mask {A : Type*} (ys : List A) (m : A → ℕ) (ref : List ℕ)
    (h : (ys.map m).Perm ref) (all : ∀ z∈one++two,z∈ref) :
    ∀ z∈one++two, ∃ y∈ys,m y=z := by
  intro z hz
  exact List.mem_map.mp (h.mem_iff.mpr (all z hz))

theorem local_strict (t : Expr X) (accept : ∀ e : E, t.eval (pos e) = true)
    (reject : ∀ y : Col, t.eval (neg y) = false) (v : X)
    (r : 2 ≤ (bucket t v).length) (fewPrivate : privateRows (masks t v) < 4) :
    baseCost v + 189*privateRows (masks t v) < 396*(bucket t v).length+localArea t v := by
  have valid : ∀ m ∈ masks t v, m < 16 := by
    intro m hm
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hm
    exact pack_lt _
  have costs (y : Col) : weight (mandatory v y) ≤ weight (used t v y) :=
    CoFormula1963Shapes.monotone_weight
      ⟨used t v y,union_small _ _ _ (fun _ _ => pack_lt _)⟩ ⟨mandatory v y,pack_lt _⟩
      (forced_subset t accept reject v y)
  have f (ys : List Col) {a b : ℕ}
      (hist : (ys.map (mandatory v)).Perm (blocks a one ++ blocks b two))
      (presentAll : ∀ z∈one++two,z ∈ blocks a one ++ blocks b two) :
      feasible (masks t v) = true ∧
      a*singles (masks t v)+b*pairs (masks t v) ≤ (ys.map fun y => weight (used t v y)).sum ∧
      ((blocks a one ++ blocks b two).map weight).sum ≤ (ys.map fun y => weight (used t v y)).sum := by
    refine ⟨CoFormula1963Shapes.feasible_from_columns _ ys _ _
      (present_mask ys _ _ hist presentAll) (fun y _ => selection t v y)
      (fun y _ => forced_subset t accept reject v y),?_,paid_forced ys _ _ _ hist costs⟩
    exact vertex_area _ ys _ _ a b hist (fun y _ => selection t v y)
      (fun y _ => forced_subset t accept reject v y)
  cases v with
  | inl p =>
    have hist := CoFormula1963Frequency.point_freq p
    have eq : mandatory (.inl p) = CoFormula1963Frequency.pointMask p := funext (point_mask p)
    rw [← eq] at hist
    obtain ⟨ok,low,raw⟩ := f _ hist (by decide +kernel)
    have hi := local_area_upper t (.inl p) (fun y => !CoFormula1963Frequency.pointOn y p)
    have mass : ((blocks 27 one ++ blocks 9 two).map weight).sum = 216 := by decide +kernel
    rw [mass] at raw
    simpa [baseCost,masks] using (charged _ valid ok (by simpa [baseCost,masks] using r) fewPrivate _).1 (low.trans hi) (raw.trans hi)
  | inr l =>
    have hist := CoFormula1963Frequency.line_freq l
    have eq : mandatory (.inr l) = CoFormula1963Frequency.lineMask l := funext (line_mask l)
    rw [← eq] at hist
    obtain ⟨ok,low,raw⟩ := f _ hist (by decide +kernel)
    have hi := local_area_upper t (.inr l) (fun y => !CoFormula1963Frequency.lineOn y l)
    have mass : ((blocks 18 one ++ blocks 18 two).map weight).sum = 288 := by decide +kernel
    rw [mass] at raw
    simpa [baseCost,masks] using (charged _ valid ok (by simpa [baseCost,masks] using r) fewPrivate _).2 (low.trans hi) (raw.trans hi)

end CoAlarmTight1481
