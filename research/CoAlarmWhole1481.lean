import PEqualNP.CoAlarmEdges1481
import PEqualNP.CoAlarmTight1481

namespace CoAlarmWhole1481
open CoFormula1963Geometry CoFormula1963Protocol CoFormula1963Private CoFormula1963Link
open CoFormula1963Area CoFormula1963Packed CoFormula1963Flags CoFormula1963Local CoFormula1963Vertex
open CoFormula1963Complete CoAlarmDerivative1481
open scoped BigOperators

private theorem occurrence (v : X) (t : Expr X) (R : Finset E) (C : Finset Col) :
    ((partition pos neg t R C).filter fun r => r.label=v).length = occ v t := by
  induction t generalizing R C with
  | atom i => by_cases eq : i=v <;> simp [partition,occ,eq]
  | conj a b ha hb => simp only [partition,List.filter_append,List.length_append,ha,hb,occ]
  | disj a b ha hb => simp only [partition,List.filter_append,List.length_append,ha,hb,occ]

theorem bucket_occ (t : Expr X) (v : X) : (bucket t v).length=occ v t :=
  occurrence v t _ _

theorem repeated_flag (t : Expr X) (accept : ∀ e : E, t.eval (pos e)=true)
    (reject : ∀ y : Col, t.eval (neg y)=false) (e : E)
    (p : 2 ≤ occ (.inl e.val.1) t) (l : 2 ≤ occ (.inr e.val.2) t) : 66 ≤ t.leaves := by
  classical
  let rank := fun v => baseCost v + 189*privateRows (masks t v)
  let paid := fun v => 396*(bucket t v).length + localArea t v
  have single (v : X) : rank v ≤ paid v := by
    cases v with
    | inl _ => exact local_charge t accept reject _
    | inr _ => exact local_charge t accept reject _
  have loc : (∑ v : X, baseCost v)=28080 := by decide +kernel
  have area := CoFormula1963Mass.area_total t
  have len := CoFormula1963Mass.occurrence_total t
  change (∑ v : X,localArea t v)=12168 at area
  change (∑ v : X,(bucket t v).length)=t.leaves at len
  have enough := enough_private t accept reject
  have bound (v : X) : privateRows (masks t v) ≤ 4 := CoFormula1963Shapes.private_bound _
  by_cases both : privateRows (masks t (.inl e.val.1))=4 ∧ privateRows (masks t (.inr e.val.2))=4
  · have more := CoAlarmEdges1481.double t accept reject e both.1 both.2
    have sum := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => single v)
    simp only [rank,paid,Finset.sum_add_distrib,←Finset.mul_sum,loc,area,len] at sum
    omega
  · have strict : ∃ v : X, rank v < paid v := by
      by_cases pt : privateRows (masks t (.inl e.val.1))=4
      · refine ⟨.inr e.val.2,CoAlarmTight1481.local_strict t accept reject _ ((bucket_occ _ _).symm ▸ l) ?_⟩
        have hh := bound (.inr e.val.2)
        omega
      · refine ⟨.inl e.val.1,CoAlarmTight1481.local_strict t accept reject _ ((bucket_occ _ _).symm ▸ p) ?_⟩
        have hh := bound (.inl e.val.1)
        omega
    obtain ⟨v,hv⟩ := strict
    have sum := Finset.sum_lt_sum (s:=Finset.univ) (fun i _ => single i) ⟨v,Finset.mem_univ _,hv⟩
    simp only [rank,paid,Finset.sum_add_distrib,←Finset.mul_sum,loc,area,len] at sum
    omega

def singleton (v i : X) := decide (i=v)

theorem p_row (e : E) : bumped (singleton (.inr e.val.2)) (.inl e.val.1) = pos e := by
  funext i
  cases i <;> simp [bumped,singleton,pos]
theorem l_row (e : E) : bumped (singleton (.inl e.val.1)) (.inr e.val.2) = pos e := by
  funext i
  cases i <;> simp [bumped,singleton,pos]

theorem flat66 (t : Expr X) (accept : ∀ e : E, t.eval (pos e)=true)
    (reject : ∀ y : Col, t.eval (neg y)=false) (e : E)
    (p0 : t.eval (singleton (.inl e.val.1))=false)
    (l0 : t.eval (singleton (.inr e.val.2))=false)
    (offP : alarm (singleton (.inr e.val.2)) (.inl e.val.1) t=false)
    (offL : alarm (singleton (.inl e.val.1)) (.inr e.val.2) t=false) : 66 ≤ t.leaves :=
  repeated_flag t accept reject e
    (two_reads t _ _ l0 (by rw [p_row];exact accept e) offP)
    (two_reads t _ _ p0 (by rw [l_row];exact accept e) offL)

#print axioms flat66
end CoAlarmWhole1481
