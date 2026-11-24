import PEqualNP.CoMaskShape4482
import PEqualNP.CoAnchorMask4482
namespace CoGlobalShape4482
open CoMaskShape4482 CoAnchorMask4482 CoBlockSlots4482

private theorem count_map {A B : Type} (xs : List A) (f : A→B) (p : B→Bool) :
    ((xs.map f).filter p).length=(xs.filter (fun x => p (f x))).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : p (f a) <;> simp only [List.map_cons,List.filter_cons,h,Bool.false_eq_true,
      ↓reduceIte,List.length_cons,ih]

/-- The fixed width cut and the seven varying anchor coordinates can be
turned into a certified required-mask calculation with no large table
of per-state cardinality proofs. -/
def required {n} (ids anchors : List (Fin n)) (inc : Fin n→BitVec (2^n)) : BitVec (2^n) :=
  mask (atMost (ids.map inc) (n-5)) inc anchors

theorem required_at {n} (ids anchors : List (Fin n)) (inc : Fin n→BitVec (2^n))
    (nd : ids.Nodup) (complete : ∀i,i∈ids)
    (digits : ∀i (j : Fin (2^n)), (inc i).getLsbD j.val=j.val.testBit i.val)
    (j : Fin (2^n)) (small : (members j).card+5≤n)
    (two : 2≤((members j)∩anchors.toFinset).card) :
    (required ids anchors inc).getLsbD j.val=true := by
  apply needed _ inc anchors digits j _ two
  rw [atMost_get,count_map]
  let filtered := ids.filter (fun i => (inc i).getLsbD j.val)
  have dis : filtered.Nodup := nd.filter _
  have equal : filtered.toFinset=members j := by
    ext i
    simp only [List.mem_toFinset,filtered,List.mem_filter,members,Finset.mem_filter,
      Finset.mem_univ,true_and,digits]
    exact and_iff_right (complete i)
  have count := List.toFinset_card_of_nodup dis
  rw [equal] at count
  change decide (filtered.length≤n-5)=true
  apply decide_eq_true
  omega

#print axioms required_at
end CoGlobalShape4482
