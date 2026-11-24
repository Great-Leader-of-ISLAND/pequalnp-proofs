import PEqualNP.CoFormula1963Vertex

namespace CoFormula1963Complete
open CoFormula1963Geometry CoFormula1963Protocol CoFormula1963Private CoFormula1963Link
open CoFormula1963Area CoFormula1963Packed CoFormula1963Flags CoFormula1963Local CoFormula1963Vertex
open scoped BigOperators

def actual (t : Expr X) (v : X) (e : E) : Prop := match v with
  | .inl _ => PointPrivate (fun f : E => f.val.1) (fun k : ID t => k.val.label)
      (fun k f => f∈k.val.rows) e
  | .inr _ => LinePrivate (fun f : E => f.val.2) (fun k : ID t => k.val.label)
      (fun k f => f∈k.val.rows) e

def privateBit (F : List ℕ) (i : ℕ) :=
  (List.range 4).all fun j => i==j || F.any (fun m => m.testBit j && !m.testBit i)

theorem all_flags : ∀ v : X, Finset.univ.image (flag v) =
    Finset.univ.filter (fun e : E => pos e v = true) := by decide +kernel

theorem sum_flags (v : X) (f : E → ℕ) :
    (∑ e : E, if pos e v = true then f e else 0) = ∑ i : Fin 4, f (flag v i) := by
  calc
    _ = ∑ e ∈ Finset.univ.filter (fun e : E => pos e v = true), f e := by simp [Finset.sum_filter]
    _ = _ := by rw [← all_flags,Finset.sum_image (fun a _ b _ h => flag_inj v a b h)]

theorem actual_bit (t : Expr X) (v : X) (i : Fin 4) (hp : actual t v (flag v i)) :
    privateBit (masks t v) i = true := by
  classical
  unfold privateBit
  apply List.all_eq_true.mpr
  intro j hj
  by_cases eq : i.val = j
  · simp [eq]
  let k : Fin 4 := ⟨j,List.mem_range.mp hj⟩
  have ne : flag v k ≠ flag v i := by
    intro z
    exact eq (congrArg Fin.val (flag_inj v k i z)).symm
  have noDom : ¬ Dominates (fun d : ID t => d.val.label) (fun d e => e∈d.val.rows)
      v (flag v k) (flag v i) := by
    cases v with
    | inl p => exact hp _ rfl ne
    | inr l => exact hp _ rfl ne
  unfold Dominates at noDom
  push_neg at noDom
  obtain ⟨d,lab,yes,no⟩ := noDom
  have w : (masks t v).any (fun m => m.testBit j && !m.testBit i) = true := by
    apply List.any_eq_true.mpr
    refine ⟨mask v d.val,List.mem_map.mpr ⟨d.val,?_,rfl⟩,?_⟩
    · exact List.mem_filter.mpr ⟨d.property,by simp [lab]⟩
    · have y : (mask v d.val).testBit k = true := by simp [mask,bit_pack,yes]
      have n : (mask v d.val).testBit i = false := by simp [mask,bit_pack,no]
      simp [show j=k.val from rfl,y,n] 
  simp [w]

noncomputable def fee (P : Prop) : ℕ := by
  classical
  exact if P then 1 else 0

private theorem charge_private (t : Expr X) (v : X) :
    (∑ i : Fin 4, fee (actual t v (flag v i)))
      ≤ privateRows (masks t v) := by
  classical
  unfold privateRows
  rw [filter_four]
  apply Finset.sum_le_sum
  intro i _
  by_cases a : actual t v (flag v i)
  · have pos := actual_bit t v i a
    unfold privateBit at pos
    simp [fee,a,pos]
  · simp [fee,a]

theorem enough_private (t : Expr X) (accept : ∀ e : E, t.eval (pos e) = true)
    (reject : ∀ y : Col, t.eval (neg y) = false) :
    52 ≤ ∑ v : X, privateRows (masks t v) := by
  classical
  have orig := CoFormula1963Mass.private_total t accept reject
  rw [Fintype.sum_sum_type]
  apply orig.trans
  apply Nat.add_le_add
  · apply Finset.sum_le_sum
    intro p _
    have h := charge_private t (.inl p)
    have f := sum_flags (.inl p) (fun e => fee (actual t (.inl p) e))
    rw [← f] at h
    simpa [pos,fee,actual,CoFormula1963Mass.privatePoint,eq_comm] using h
  · apply Finset.sum_le_sum
    intro l _
    have h := charge_private t (.inr l)
    have f := sum_flags (.inr l) (fun e => fee (actual t (.inr l) e))
    rw [← f] at h
    simpa [pos,fee,actual,CoFormula1963Mass.privateLine,eq_comm] using h

/-- A formula over the 26 real variables accepting every incidence flag and
    rejecting the 234 specific geometric negatives requires at least 65 leaves. -/
theorem leaves65 (t : Expr X) (accept : ∀ e : E, t.eval (pos e) = true)
    (reject : ∀ y : Col, t.eval (neg y) = false) : 65 ≤ t.leaves := by
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => local_charge t accept reject v)
  have loc : (∑ v : X, match v with | .inl _ => (1044:ℕ) | .inr _ => 1116) = 28080 := by
    decide +kernel
  have p := enough_private t accept reject
  have a := CoFormula1963Mass.area_total t
  have l := CoFormula1963Mass.occurrence_total t
  change (∑ v : X, localArea t v) = 12168 at a
  change (∑ v : X, (bucket t v).length) = t.leaves at l
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,loc,a,l] at total
  omega

#print axioms leaves65
end CoFormula1963Complete
