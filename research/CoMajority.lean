import PEqualNP.CoUstarFraction
import PEqualNP.Outside.L_meta_1733
import PEqualNP.Outside.L_meta_1388

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_1766

namespace CoMajority

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

open scoped BigOperators
open Classical in
theorem majority_absolute {m h : ℕ}
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (W : Fin m → Finset (Fin n))
    (small : ∀ i, (W i).card ≤ h)
    (hI : ∀ i, ∀ a ∈ W i, ∀ b ∈ W i, ¬G.Adj a b)
    (freq : ∀ g ∈ junk G C,
       m/2 < (Finset.univ.filter (fun i => gateVal n C g (CoUstarFraction.row (W i)) = true)).card) :
    (Ustar G C).card ≤ 2 * h * (C.size+1) := by
  classical
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
  let active (g : ℕ) := Finset.univ.filter (fun i => gateVal n C g (CoUstarFraction.row (W i)) = true)
  let d := m/2+1
  have hf (g : ℕ) (hg : g ∈ junk G C) : d ≤ (active g).card := freq g hg
  have together (g : ℕ) (hg : g ∈ junk G C) (j : ℕ) (hj : j ∈ junk G C) :
      ∃ i, gateVal n C g (CoUstarFraction.row (W i)) = true ∧ gateVal n C j (CoUstarFraction.row (W i)) = true := by
    have c := Finset.card_union_add_card_inter (active g) (active j)
    have u : ((active g) ∪ (active j)).card ≤ m := by
      simpa using Finset.card_le_card (Finset.subset_univ ((active g) ∪ (active j)))
    have a := hf g hg
    have b := hf j hj
    have hne : ((active g) ∩ (active j)).Nonempty := by
      apply Finset.card_pos.mp
      dsimp [d] at a b
      omega
    obtain ⟨i,hi⟩ := hne
    rcases Finset.mem_inter.mp hi with ⟨ig,ij⟩
    exact ⟨i,(Finset.mem_filter.mp ig).2,(Finset.mem_filter.mp ij).2⟩
  have lower := CoUstarFraction.fractional hL hT (PEqualNP.Outside.L_meta_1733.Glue.no4 n G hg)
    tri A hm W hI hf together
  have md : m ≤ 2*d := by dsimp [d]; omega
  refine Nat.le_of_mul_le_mul_right ?_ (show 0 < d by dsimp [d]; omega)
  calc
    _ ≤ ∑ i, (W i).card * A.card := lower
    _ ≤ ∑ _i : Fin m, h * (C.size+1) := Finset.sum_le_sum (fun i _ => Nat.mul_le_mul (small i) ha)
    _ = m * (h * (C.size+1)) := by simp
    _ ≤ (2*d) * (h * (C.size+1)) := Nat.mul_le_mul_right _ md
    _ = _ := by ring
end CoMajority
