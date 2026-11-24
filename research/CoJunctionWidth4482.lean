import PEqualNP.CoPortCheckMove4482
namespace CoJunctionWidth4482
open CoPortRoots4482 CoPortFrontier4482 CoPortTrace4482

private theorem discard_subset (s : Finset W) (x : W) (d : Bool) :
    discard s x d ⊆ s := by
  cases d with
  | false => exact fun _ h => h
  | true => exact Finset.erase_subset _ _

/-- Once a candidate gate is fresh, only its two last-use bits affect
the next frontier size. No deduplication of a newly built frontier is needed. -/
theorem size_form {xs : List W} {a b : W} {d : Bool}
    (ha : a∈xs) (hb : b∈xs) (ne : a≠b) (fresh : join d a b∉xs) (da db : Bool) :
    (successor xs d a b da db).toFinset.card =
      xs.toFinset.card+1-(if da then 1 else 0)-(if db then 1 else 0) := by
  let s := xs.toFinset
  have ma : a∈s := List.mem_toFinset.mpr ha
  have mb : b∈s := List.mem_toFinset.mpr hb
  have missing : join d a b ∉ discard (discard s a da) b db :=
    fun m => fresh (List.mem_toFinset.mp (discard_subset s a da (discard_subset _ b db m)))
  have two : 1<s.card := Finset.one_lt_card.mpr ⟨a,ma,b,mb,ne⟩
  have bkept : b ∈ s.erase a := Finset.mem_erase.mpr ⟨ne.symm,mb⟩
  rw [set_successor,Finset.card_insert_of_notMem missing]
  cases da <;> cases db
  · rfl
  · change (s.erase b).card+1=s.card+1-0-1
    rw [Finset.card_erase_of_mem mb]
    omega
  · change (s.erase a).card+1=s.card+1-1-0
    rw [Finset.card_erase_of_mem ma]
    omega
  · change ((s.erase a).erase b).card+1=s.card+1-1-1
    rw [Finset.card_erase_of_mem bkept,Finset.card_erase_of_mem ma]
    omega

#print axioms size_form
end CoJunctionWidth4482
