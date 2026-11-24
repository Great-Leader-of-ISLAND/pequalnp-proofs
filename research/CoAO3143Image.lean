import PEqualNP.CoAO3143Restriction
import PEqualNP.CoAO3143Bridge

namespace CoAO3143Restriction
open CoAO3143

private lemma image_insert3 {α : Type} {q : Wire α→Sig} {a b : Wire α}
    {U : Finset (Wire α)} {x : Sig} [DecidableEq (Wire α)] :
    x∈(insert a (insert b U)).image q ↔ x=q a ∨ x=q b ∨ x∈U.image q := by
  simp [Finset.image_insert]

/-- Restrict every wire to the finite test signatures. If forward equality,
    a constant, or deadness eliminates any gate the new gate budget is strictly
    smaller. Equality of budgets forces the entire image of the old root set. -/
theorem cone_image {α : Type} {out : Wire α} {k : Nat} {S : Finset (Wire α)}
    (h : Cone out k S) (q : Wire α → Sig) (goal : q out=target)
    (hom : ∀ d a b, q (op d a b) = bin d (q a) (q b)) :
    ∃ m T, m≤k ∧ Live m 0 T ∧ T ⊆ S.image q ∧ (m=k → T=S.image q) := by
  classical
  induction h with
  | stop =>
    refine ⟨0,{target},by omega,Live.stop,?_,?_⟩ <;> simp [goal]
  | @gate k U d a b fresh tail ih =>
    let z := op d a b
    let M := (insert a (insert b U)).image q
    obtain ⟨m,T,le,ht,sub,full⟩ := ih
    have old (x) (hx : x∈T) : x=q z ∨ x∈U.image q := by
      have found := sub hx
      simpa only [Finset.image_insert,Finset.mem_insert] using found
    have inU (x) (hx : x∈U.image q) : x∈M := by simp [M,Finset.image_insert,hx]
    by_cases need : q z∈T ∧ q z∉M
    · let del := T.erase (q z)
      have inDel (x) (hx : x∈del) : x∈U.image q :=
        (old x (Finset.mem_erase.mp hx).2).resolve_left (Finset.mem_erase.mp hx).1
      have qa : q a∈M := by simp [M,Finset.image_insert]
      have qb : q b∈M := by simp [M,Finset.image_insert]
      have pr := live_proper ht _ need.1
      have classified := bin_rep (w:=[q a,q b]) d (Or.inl (by simp)) (Or.inl (by simp))
      rw [←hom] at classified
      change represented _ (q z) ∨ witness _ (q z) at classified
      rcases classified with trivial | ⟨d',x,y,hx,hy,px,py,xy,hz⟩
      · rcases trivial with known | bad
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at known
          apply False.elim
          apply need.2
          rcases known with eq | eq
          · rw [eq]; exact qa
          · rw [eq]; exact qb
        · exact (bad pr).elim
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hy
        have inputs : ({x,y} : Finset Sig) = {q a,q b} := by
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all [Finset.pair_comm]
        have xM : x∈M := by rcases hx with e | e <;> simp_all
        have yM : y∈M := by rcases hy with e | e <;> simp_all
        have nt : bin d' x y ∉ insert x (insert y del) := by
          rw [←hz]
          intro hh
          simp only [Finset.mem_insert] at hh
          rcases hh with hh | hh | hh
          · apply need.2
            rw [hh]
            exact xM
          · apply need.2
            rw [hh]
            exact yM
          · exact (Finset.mem_erase.mp hh).1 rfl
        have tail' : Live m 0 (insert (bin d' x y) del) := by
          simpa [del,←hz,Finset.insert_erase need.1] using ht
        refine ⟨m+1,_,by omega,Live.binary px py xy nt tail',?_,?_⟩
        · intro w hw
          rcases Finset.mem_insert.mp hw with rfl | inner
          · exact xM
          rcases Finset.mem_insert.mp inner with rfl | inner
          · exact yM
          · exact inU w (inDel w inner)
        · intro same
          have exactTail := full (by omega)
          have nz : q z∉U.image q := fun hu => need.2 (inU _ hu)
          have dq : del=U.image q := by
            ext w
            simp only [del,Finset.mem_erase,exactTail,Finset.image_insert,Finset.mem_insert]
            change (w≠q z ∧ (w=q z ∨ w∈U.image q)) ↔ w∈U.image q
            constructor
            · rintro ⟨ne,hh⟩
              exact hh.resolve_left ne
            · intro hw
              exact ⟨fun eq => nz (eq ▸ hw),Or.inr hw⟩
          rw [dq,Finset.image_insert,Finset.image_insert]
          have pq := congrArg (fun t : Finset Sig => t ∪ U.image q) inputs
          simpa [Finset.insert_union] using pq
    · refine ⟨m,T,by omega,ht,?_,by omega⟩
      intro w hw
      rcases old w hw with eq | hu
      · by_contra no
        subst w
        exact need ⟨hw,no⟩
      · exact inU w hu

end CoAO3143Restriction
