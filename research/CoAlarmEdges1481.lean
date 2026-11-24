import PEqualNP.CoFormula1963Complete

namespace CoAlarmEdges1481
open CoFormula1963Geometry CoFormula1963Protocol CoFormula1963Private CoFormula1963Link
open CoFormula1963Area CoFormula1963Packed CoFormula1963Flags CoFormula1963Local CoFormula1963Vertex
open CoFormula1963Complete
open scoped BigOperators

def slot (e : E) : Fin 4 :=
  if e.val.1=e.val.2 then 0 else if e.val.1=e.val.2+1 then 1
  else if e.val.1=e.val.2+3 then 2 else 3

theorem number : ∀ (v : X) (i : Fin 4), slot (flag v i)=i := by decide +kernel
theorem endpoints : ∀ e : E,flag (.inl e.val.1) (slot e)=e ∧ flag (.inr e.val.2) (slot e)=e := by
  decide +kernel

def cost (t : Expr X) (v : X) (e : E) := if privateBit (masks t v) (slot e) then 1 else 0

theorem sum_endpoint (t : Expr X) (v : X) :
    (∑ e : E, if pos e v=true then cost t v e else 0)= privateRows (masks t v) := by
  rw [sum_flags]
  unfold privateRows
  rw [filter_four]
  apply Finset.sum_congr rfl
  intro i _
  simp only [cost,number,privateBit]

theorem counts (t : Expr X) :
    (∑ v : X, privateRows (masks t v)) =
    ∑ e : E, (cost t (.inl e.val.1) e + cost t (.inr e.val.2) e) := by
  classical
  calc
    _ = ∑ v : X, ∑ e : E, if pos e v=true then cost t v e else 0 :=
      Finset.sum_congr rfl fun v _ => (sum_endpoint t v).symm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Fintype.sum_sum_type]
      simp [pos]

theorem covers (t : Expr X) (accept : ∀ e : E, t.eval (pos e)=true)
    (reject : ∀ y : Col,t.eval (neg y)=false) (e : E) :
    1 ≤ cost t (.inl e.val.1) e + cost t (.inr e.val.2) e := by
  obtain ⟨hp,hl⟩ := endpoints e
  rcases flag_private t accept reject e with h|h
  · have f : actual t (.inl e.val.1) (flag (.inl e.val.1) (slot e)) := by rw [hp];exact h
    have a := actual_bit t (.inl e.val.1) (slot e) f
    simp [cost,a]
  · have f : actual t (.inr e.val.2) (flag (.inr e.val.2) (slot e)) := by rw [hl];exact h
    have a := actual_bit t (.inr e.val.2) (slot e) f
    simp [cost,a]

theorem full (F : List Nat) (h : privateRows F=4) (i : Fin 4) : privateBit F i=true := by
  rw [privateRows,filter_four] at h
  change (∑ j : Fin 4, if privateBit F j then 1 else 0)=4 at h
  simp only [Fin.sum_univ_succ] at h
  cases a : privateBit F 0 <;> cases b : privateBit F 1 <;>
    cases c : privateBit F 2 <;> cases d : privateBit F 3 <;>
    fin_cases i <;> simp_all

theorem double (t : Expr X) (accept : ∀ e : E, t.eval (pos e)=true)
    (reject : ∀ y : Col,t.eval (neg y)=false) (both : E)
    (p : privateRows (masks t (.inl both.val.1))=4)
    (l : privateRows (masks t (.inr both.val.2))=4) :
    53 ≤ ∑ v : X, privateRows (masks t v) := by
  classical
  rw [counts]
  have sum := Finset.sum_le_sum (s:=Finset.univ) (f:=fun e : E => 1+(if e=both then 1 else 0))
    (g:=fun e : E => cost t (.inl e.val.1) e + cost t (.inr e.val.2) e) (fun e _ => by
      by_cases same : e=both
      · subst e
        simp [cost,full _ p,full _ l]
      · simpa [same] using covers t accept reject e)
  simpa [Finset.sum_add_distrib,CoFormula1963Mass.flag_count] using sum

#print axioms double
end CoAlarmEdges1481
