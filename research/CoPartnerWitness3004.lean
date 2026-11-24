import PEqualNP.CoUnsafePort3004

namespace CoUnsafePort3004
variable {V : Type} [DecidableEq V]

/-- Any independent witness that switches on a unique OR partner must hit
each of the three disjoint sets of alternate neighbors in the Heawood graph. -/
theorem alternate_neighbors {edge : V → V → Prop} (sym : Symmetric edge)
    (irr : ∀ v, ¬ edge v v) {x : V} {bank : Finset V → Bool}
    (mono : ∀ A B : Finset V,A ⊆ B → bank A=true → bank B=true)
    (stable : ∀ J : Finset V,x∉J → bank J=true → Independent edge J → Independent edge (insert x J))
    {I : Finset V} (absent : x∉I) (clean : Independent edge I) (high : bank I=true)
    {a b c : V} (adjA : edge x a) (adjB : edge x b) (adjC : edge x c)
    (ab : ∀ v∈I,edge a v → ¬ edge b v)
    (ac : ∀ v∈I,edge a v → ¬ edge c v)
    (bc : ∀ v∈I,edge b v → ¬ edge c v) : 3≤I.card := by
  have hits := unsafe_partner sym irr mono stable (Finset.Subset.refl I) absent clean high
  obtain ⟨u,hu,au⟩ := hits a adjA
  obtain ⟨v,hv,bv⟩ := hits b adjB
  obtain ⟨w,hw,cw⟩ := hits c adjC
  have uv : u≠v := fun h => ab u hu au (h ▸ bv)
  have uw : u≠w := fun h => ac u hu au (h ▸ cw)
  have vw : v≠w := fun h => bc v hv bv (h ▸ cw)
  have sub : ({u,v,w} : Finset V)⊆I := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl <;> assumption
  simpa [uv,uw,vw] using Finset.card_le_card sub
end CoUnsafePort3004
