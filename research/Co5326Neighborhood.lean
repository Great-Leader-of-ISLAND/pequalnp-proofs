import PEqualNP.Co5326Transversal

namespace Co5326Neighborhood
open Co5326Transversal
open scoped BigOperators
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def TriangleFree : Prop := ∀ a b c : V, G.Adj a b → G.Adj a c → ¬G.Adj b c

def overlap (S : Finset V) (c z : V) : Finset V :=
  S.filter fun x => G.Adj c x ∧ (x=z ∨ G.Adj z x)

theorem overlap_le_one (triangle : TriangleFree G) (square : FourFree G) (S : Finset V)
    {c z : V} (distinct : c≠z) : (overlap G S c z).card ≤ 1 := by
  by_cases adjacent : G.Adj c z
  · apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨_,pc,rfl | pz⟩ := Finset.mem_filter.mp hp
    · obtain ⟨_,qc,rfl | qz⟩ := Finset.mem_filter.mp hq
      · rfl
      · exact (triangle c _ q adjacent qc qz).elim
    · exact (triangle c z p adjacent pc pz).elim
  · apply le_trans _ (square c z distinct S)
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hS,hc,rfl | hz⟩ := Finset.mem_filter.mp hx
    · exact (adjacent hc).elim
    · exact Finset.mem_filter.mpr ⟨hS,hc,hz⟩

theorem few_outside (triangle : TriangleFree G) (square : FourFree G) (S Z : Finset V)
    (cover : ∀ x∈S, ∃ z∈Z, x=z ∨ G.Adj z x) {c : V} (outside : c∉Z) :
    (S.filter (G.Adj c)).card ≤ Z.card := by
  have sub : S.filter (G.Adj c) ⊆ Z.biUnion (overlap G S c) := by
    intro x hx
    obtain ⟨hs,hc⟩ := Finset.mem_filter.mp hx
    obtain ⟨z,hz,edge⟩ := cover x hs
    exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_filter.mpr ⟨hs,hc,edge⟩⟩
  calc
    _ ≤ (Z.biUnion (overlap G S c)).card := Finset.card_le_card sub
    _ ≤ ∑ z∈Z,(overlap G S c z).card := Finset.card_biUnion_le
    _ ≤ ∑ _z∈Z,1 := Finset.sum_le_sum (fun z hz => overlap_le_one G triangle square S
      (fun e => outside (e.symm ▸ hz)))
    _ = _ := by simp

theorem rich_centers (triangle : TriangleFree G) (square : FourFree G) (S Z centers : Finset V)
    (t : Nat) (hz : Z.card ≤ t) (cover : ∀ x∈S, ∃ z∈Z, x=z ∨ G.Adj z x) :
    (centers.filter fun c => t < (S.filter (G.Adj c)).card).card ≤ t := by
  apply le_trans _ hz
  apply Finset.card_le_card
  intro c hc
  have rich := (Finset.mem_filter.mp hc).2
  by_contra outside
  have u := (few_outside G triangle square S Z cover outside).trans hz
  omega

#print axioms rich_centers
end Co5326Neighborhood
