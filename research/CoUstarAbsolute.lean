import PEqualNP.CoUstarWitness
import PEqualNP.Outside.L_meta_1733
import PEqualNP.Outside.L_meta_1388

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_1766

namespace CoUstarWitness

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- All nonisolated vertices belong to the dependency component of the output.
The checked component-coloring lemma bounds the size of this component. -/
private lemma active_inputs (hL : IsLeastAO G C) :
    ∃ A : Finset (Fin n), A.card ≤ C.size+1 ∧ ∀ u v, G.Adj u v → u ∈ A ∧ v ∈ A := by
  classical
  obtain ⟨f,hcount,hwire⟩ :=
    PEqualNP.Outside.L_meta_1388.WireComponents.coloring (n := n) C
      (fun g hg => Nat.le_of_eq (hL.1.2.2 g hg))
  obtain ⟨k,hk⟩ := hwire C.output
  let A := (Finset.univ : Finset (Fin n)).filter (fun u => f u = k)
  have hm (u : Fin n) : u ∈ A ↔ f u = k := by simp [A]
  let B := (Finset.univ : Finset (Fin n)) \ A
  have hsub : Finset.univ.image f ⊆ insert k (B.image f) := by
    intro z hz
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hz
    by_cases h : f u = k
    · simp [h]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,mt (hm u).mp h⟩,rfl⟩
  have hc : (Finset.univ.image f).card ≤ B.card + 1 :=
    (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right Finset.card_image_le 1))
  have hsum : B.card+A.card = n := by
    simpa [B] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have mem (u v : Fin n) (huv : G.Adj u v) : u ∈ A := by
    by_contra hu
    have hf := mt (hm u).mpr hu
    have eq := hk (pairInput u v) (pairInput v v) (by
      intro p hp
      have hne : p ≠ u := fun h => hf (h ▸ hp)
      simp [pairInput,hne])
    have out (x : Fin n → Bool) :
        (C.wires (List.ofFn x)).getD C.output false = graphFun G ∅ x := congrFun hL.2.1 x
    rw [out,out] at eq
    have hv := (graphFun_pair G v v).mp (eq ▸ (graphFun_pair G u v).mpr huv)
    exact G.irrefl hv
  exact ⟨A,by omega,fun u v huv => ⟨mem u v huv,mem v u huv.symm⟩⟩

/-- The original girth and circuit model imply an absolute linear bound if all
junk gates share one independent witness with at most h vertices. -/
theorem absolute (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (hL : IsLeastAO G C) (hT : TopForm G C) (h : ℕ)
    (W : Finset (Fin n)) (hcard : W.card ≤ h)
    (hI : ∀ a ∈ W, ∀ b ∈ W, ¬G.Adj a b)
    (hW : ∀ g ∈ junk G C, gateVal n C g (row W) = true) :
    (Ustar G C).card ≤ h * (C.size+1) := by
  obtain ⟨A,ha,hm⟩ := active_inputs hL
  have tri (a b c : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) : False := by
    have ab := G.ne_of_adj hab
    have bc := G.ne_of_adj hbc
    have ac := G.ne_of_adj hac
    have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
        (SimpleGraph.Walk.cons hac.symm SimpleGraph.Walk.nil))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      constructor
      · simp [SimpleGraph.Walk.cons_isPath_iff, ab,bc,ac,Ne.symm ab,Ne.symm bc,Ne.symm ac]
      · simp [Sym2.eq_iff, ab,bc,ac,Ne.symm ab,Ne.symm bc,Ne.symm ac]
    have bad := hg a _ hcyc
    simp at bad
  calc
    _ ≤ W.card * A.card := common_witness hL hT (PEqualNP.Outside.L_meta_1733.Glue.no4 n G hg)
      tri A W hm hI hW
    _ ≤ h * (C.size+1) := Nat.mul_le_mul hcard ha

end CoUstarWitness
