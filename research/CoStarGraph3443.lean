import Mathlib
import PEqualNP.Defs

namespace CoStarGraph3443
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

variable {n : Nat} (c : Fin n)

theorem no_four : NoFourCycle (SimpleGraph.starGraph c) := by
  intro a b different
  calc
    _ ≤ ({c} : Finset (Fin n)).card := by
      apply Finset.card_le_card
      intro v hv
      obtain ⟨av,bv⟩ := (Finset.mem_filter.mp hv).2
      have A := (SimpleGraph.starGraph_adj.mp av).2
      have B := (SimpleGraph.starGraph_adj.mp bv).2
      apply Finset.mem_singleton.mpr
      by_contra h
      exact different ((A.resolve_right h).trans (B.resolve_right h).symm)
    _ = 1 := Finset.card_singleton c

theorem truth (x : Fin n → Bool) :
    graphFun (SimpleGraph.starGraph c) ∅ x =
      (x c && decide (∃ v : Fin n, v ≠ c ∧ x v = true)) := by
  have edge : (∃ a b : Fin n, (SimpleGraph.starGraph c).Adj a b ∧ x a = true ∧ x b = true) ↔
      x c = true ∧ ∃ v : Fin n, v ≠ c ∧ x v = true := by
    constructor
    · rintro ⟨a,b,ab,xa,xb⟩
      obtain ⟨ne,atCentre⟩ := SimpleGraph.starGraph_adj.mp ab
      rcases atCentre with rfl|rfl
      · exact ⟨xa,b,Ne.symm ne,xb⟩
      · exact ⟨xb,a,ne,xa⟩
    · rintro ⟨xc,v,hv,xv⟩
      exact ⟨c,v,SimpleGraph.starGraph_center_adj (Ne.symm hv),xc,xv⟩
  unfold graphFun
  simp only [edge]
  cases h : x c <;> simp [h]

theorem rest_card (leaf : Fin n) (away : leaf ≠ c) :
    ((SimpleGraph.starGraph c).edgeFinset \ {s(c,leaf)}).card + 2 = n := by
  have mem : s(c,leaf) ∈ (SimpleGraph.starGraph c).edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.starGraph_center_adj (Ne.symm away))
  have tree := (SimpleGraph.isTree_starGraph c).card_edgeFinset
  simp only [Fintype.card_fin] at tree
  rw [Finset.sdiff_singleton_eq_erase,Finset.card_erase_of_mem mem]
  have pos := Finset.card_pos.mpr ⟨_,mem⟩
  omega

theorem minimum_cover (leaf v : Fin n) (outside : v ≠ c) (other : v ≠ leaf) :
    IsMinCover ((SimpleGraph.starGraph c).deleteEdges {s(c,leaf)}) {c} := by
  have edge : ((SimpleGraph.starGraph c).deleteEdges {s(c,leaf)}).Adj c v := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨SimpleGraph.starGraph_center_adj (Ne.symm outside),?_⟩
    simpa [Sym2.eq_iff,other,outside] 
  constructor
  · intro a b ab
    exact (SimpleGraph.starGraph_adj.mp (SimpleGraph.deleteEdges_adj.mp ab).1).2.imp
      (fun e => by simp [e]) (fun e => by simp [e])
  · intro T covers
    have hit := covers edge
    have nonempty : T.Nonempty := hit.elim (fun h => ⟨c,h⟩) (fun h => ⟨v,h⟩)
    simpa using Finset.card_pos.mpr nonempty

end CoStarGraph3443
