import PEqualNP.Co4358Walk

namespace CoNum4358.Routes
open CoAO3143

private theorem only_full : ∀ xs∈(List.range 7).sublists,
    unionSep false (xs.map (lookupKW rawKW)) = top → xs=List.range 7 := by
  decide +kernel

theorem all_inputs {S : Finset Nat} (bound : S⊆Finset.range 7)
    (h : Live 11 0 (project rawKW S)) : S=Finset.range 7 := by
  classical
  let xs := (List.range 7).filter fun i => i∈S
  have members : xs.toFinset=S := by
    ext i
    simp only [xs,List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact ⟨And.right,fun hi => ⟨Finset.mem_range.mp (bound hi),hi⟩⟩
  have eq : (xs.map (lookupKW rawKW)).toFinset=project rawKW S := by
    rw [←members]
    ext w
    simp [project]
  have cov : unionSep false (xs.map (lookupKW rawKW))=top := live_cover h eq
  have sub : xs ∈ (List.range 7).sublists := List.mem_sublists.mpr (List.filter_sublist)
  have full := only_full xs sub cov
  rw [←members,full]
  simp

end CoNum4358.Routes
