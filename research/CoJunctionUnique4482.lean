import PEqualNP.CoJunctionCost4482
import PEqualNP.CoPortCheckMove4482
namespace CoJunctionUnique4482
open CoPortRoots4482 CoPortFrontier4482 CoBitBlock4482

/-- Rows on which every live signal other than this physical word has equal
endpoints. These masks are computed once per wire, independently of the gate. -/
def privateRows (xs : List Entry) (w : W) : Bits :=
  exclusive (obs (removeEntry xs w true))

/-- OR cannot carry a single surviving difference if its other argument
is identically true there. AND cannot carry it if the argument is false. -/
def allowed (u : Bits) (op : Bool) (other : Mark) : Bool :=
  (u &&& (if op then other.2 else ~~~other.1)) == 0

private theorem source (ms : List Mark) (i : Row) (on : bit (cov ms) i=true) :
    ∃ w∈ms, bit (w.1 ^^^ w.2) i=true := by
  induction ms with
  | nil => simp [cov,bit] at on
  | cons a ms ih =>
    change ((a.1 ^^^ a.2) ||| cov ms).getLsbD i.val=true at on
    rw [BitVec.getLsbD_or,Bool.or_eq_true] at on
    rcases on with aOn|tOn
    · exact ⟨a,List.mem_cons_self,aOn⟩
    · obtain ⟨x,m,one⟩ := ih tOn
      exact ⟨x,List.mem_cons_of_mem _ m,one⟩

private theorem pin (outside live : List Entry) (a b : Entry) (op : Bool)
    (hb : b∈outside) (within : ∀ x∈live,x∈outside)
    (coverage : admitted (make op a b :: live)=true) :
    allowed (exclusive (obs outside)) op b.2=true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  let i : Row := ⟨t,ht⟩
  by_cases yes : bit (exclusive (obs outside)) i=true
  · have eqFor (e : Entry) (m : e∈outside) : bit e.2.1 i = bit e.2.2 i :=
      outside_equal _ i yes e.2 (List.mem_map.mpr ⟨e,m,rfl⟩)
    have cover : cov (obs (make op a b :: live)) = BitVec.allOnes 258 :=
      beq_iff_eq.mp coverage
    have one : bit (cov (obs (make op a b :: live))) i=true := by
      rw [cover]
      simp only [bit,BitVec.getLsbD_allOnes,i.isLt,decide_true]
    obtain ⟨z,hz,diff⟩ := source _ i one
    rcases List.mem_map.mp hz with ⟨v,hv,rfl⟩
    rcases List.mem_cons.mp hv with head|old
    · subst v
      have eqB := eqFor b hb
      change b.2.1.getLsbD t = b.2.2.getLsbD t at eqB
      change ((make op a b).2.1 ^^^ (make op a b).2.2).getLsbD t=true at diff
      change (exclusive (obs outside)).getLsbD t=true at yes
      cases op <;>
        simp only [make,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_xor,
          BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
          ht,decide_true,Bool.true_and,yes,eqB] at diff ⊢ <;>
        cases aa : a.2.1.getLsbD t <;> cases ab : a.2.2.getLsbD t <;>
        cases bb : b.2.2.getLsbD t <;> simp_all
    · have eqV := eqFor v (within v old)
      change v.2.1.getLsbD t=v.2.2.getLsbD t at eqV
      change (v.2.1 ^^^ v.2.2).getLsbD t=true at diff
      simp [BitVec.getLsbD_xor,eqV] at diff
  · have off : (exclusive (obs outside)).getLsbD t=false := by
      cases h : (exclusive (obs outside)).getLsbD t <;> first | rfl | exact (yes h).elim
    simp [BitVec.getLsbD_and,off]

private theorem rem_subset {xs : List Entry} {w : W} {d : Bool} {e : Entry}
    (h : e∈removeEntry xs w d) : e∈xs := by
  cases d with
  | false => exact h
  | true => exact (List.mem_filter.mp h).1

theorem drop_left (xs : List Entry) {a b : Entry} (hb : b∈xs)
    (ne : a.1≠b.1) (op db : Bool)
    (h : admitted (move xs op a b true db)=true) :
    allowed (privateRows xs a.1) op b.2=true := by
  apply pin (removeEntry xs a.1 true) _ a b op _ _ h
  · exact List.mem_filter.mpr ⟨hb,bne_iff_ne.mpr ne.symm⟩
  · intro e he
    exact rem_subset he

theorem drop_right (xs : List Entry) {a b : Entry} (ha : a∈xs)
    (ne : a.1≠b.1) (op da : Bool)
    (h : admitted (move xs op a b da true)=true) :
    allowed (privateRows xs b.1) op a.2=true := by
  have comm : make op a b=make op b a := by
    cases op <;> simp [make,join,BitVec.or_comm,BitVec.and_comm]
  unfold move at h
  rw [comm] at h
  apply pin (removeEntry xs b.1 true) _ b a op _ _ h
  · exact List.mem_filter.mpr ⟨ha,bne_iff_ne.mpr ne⟩
  · intro e he
    obtain ⟨inside,other⟩ := List.mem_filter.mp he
    exact List.mem_filter.mpr ⟨rem_subset inside,other⟩

#print axioms drop_left
#print axioms drop_right
end CoJunctionUnique4482
