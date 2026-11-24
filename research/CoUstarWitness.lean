import PEqualNP.Outside.L_meta_1766

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1766

namespace CoUstarWitness

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def row (S : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ S)

private lemma row_edge {S : Finset (Fin n)} (h : graphFun G ∅ (row S) = true) :
    ∃ p q, G.Adj p q ∧ p ∈ S ∧ q ∈ S := by
  simpa [graphFun, row] using h

private lemma both {a : ℕ} (hAO : IsAO2 n C) (ha : a ∈ tops G C)
    (x : Fin n → Bool) (b : Fin 2)
    (hb : val C (List.ofFn x) (opnd C a b) = true)
    (hc : val C (List.ofFn x) (opnd C a (1-b)) = true) :
    graphFun G ∅ x = true := by
  have ht : a < C.gates.length ∧ (gateAt C a).op = .and ∧ BelowF G C a := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
  obtain ⟨p,q,hpq⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ht.1))
  have hzero : val C (List.ofFn x) (opnd C a 0) = true := by
    fin_cases b
    · exact hb
    · simpa only [sub_one2] using hc
  have hone : val C (List.ofFn x) (opnd C a 1) = true := by
    fin_cases b
    · simpa only [sub_zero2] using hc
    · exact hb
  apply ht.2.2 x
  apply (val_and (n := n) (x := List.ofFn x) (by simp) ht.1 ht.2.1).mpr
  intro i hi
  refine ⟨hAO.2.1 a ht.1 i hi, ?_⟩
  rw [hpq] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · simpa [opnd,hpq] using hzero
  · simpa [opnd,hpq] using hone

private lemma neighbor_from_insert (W : Finset (Fin n))
    (hI : ∀ a ∈ W, ∀ b ∈ W, ¬G.Adj a b) (u : Fin n)
    (h : graphFun G ∅ (row (insert u W)) = true) : ∃ w ∈ W, G.Adj w u := by
  obtain ⟨a,b,hab,ha,hb⟩ := row_edge h
  simp only [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact (G.loopless.irrefl _ hab).elim
  · exact ⟨_, hb, hab.symm⟩
  · exact ⟨_, ha, hab⟩
  · exact (hI _ ha _ hb hab).elim

/-- Every uncovered edge touches a neighbor of the common independent witness.
Only the witness and its single-vertex extensions are tested. -/
theorem localization (hL : IsLeastAO G C) (hT : TopForm G C)
    (W : Finset (Fin n)) (hI : ∀ a ∈ W, ∀ b ∈ W, ¬G.Adj a b)
    (hW : ∀ g ∈ junk G C, ∀ S : Finset (Fin n), W ⊆ S →
      gateVal n C g (row S) = true)
    (e : Sym2 (Fin n)) (he : e ∈ Ustar G C) :
    ∃ u v, e = s(u,v) ∧ G.Adj u v ∧ ∃ w ∈ W, G.Adj w u := by
  have via {a : ℕ} {b : Fin 2} {g : ℕ} (hg : g ∈ junk G C)
      (hr : OrReaches n C (opnd C a b) g) (S : Finset (Fin n)) (hs : W ⊆ S) :
      val C (List.ofFn (row S)) (opnd C a b) = true :=
    orStep_up (n := n) (by simp) (orReaches_reach g _ hr).1 (hW g hg S hs)
  rcases PEqualNP.Outside.L_meta_1766 n G C hL hT e he with
    ⟨u,v,rfl,a,ha,b,g,hg,hu,hr,_⟩ | ⟨u,v,rfl,a,ha,g,hg,j,hj,_,hr,hs,_,_⟩
  · have hAdj : G.Adj u v := by
      exact (Finset.mem_sdiff.mp he).1
    have hv := via hg hr (insert u W) (Finset.subset_insert u W)
    have hraw := reach_var_val (row (insert u W)) _ u (mem_orIn_reach u hu)
      (by simp [row])
    exact ⟨u,v,rfl,hAdj,neighbor_from_insert W hI u (both hL.1 ha _ b hraw hv)⟩
  · have hg0 := via hg hr W (Finset.Subset.refl W)
    have hg1 := via hj hs W (Finset.Subset.refl W)
    have hg1' : val C (List.ofFn (row W)) (opnd C a (1-(0 : Fin 2))) = true := by
      simpa only [sub_zero2] using hg1
    obtain ⟨p,q,hpq,hp,hq⟩ := row_edge (both hL.1 ha _ 0 hg0 hg1')
    exact (hI p hp q hq hpq).elim

private noncomputable def common (G : SimpleGraph (Fin n)) (w z : Fin n) : Fin n :=
  if h : ∃ u, G.Adj w u ∧ G.Adj z u then h.choose else w

private lemma common_eq (h4 : NoFourCycle G) {w z u : Fin n} (hwz : w ≠ z)
    (hw : G.Adj w u) (hz : G.Adj z u) : common G w z = u := by
  classical
  have h : ∃ t, G.Adj w t ∧ G.Adj z t := ⟨u,hw,hz⟩
  rw [common, dif_pos h]
  apply Finset.card_le_one.mp (h4 w z hwz)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.choose_spec⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hz⟩

/-- A fixed center charges directly incident edges to their near endpoints.
The other edges charge to their far endpoints by uniqueness of common neighbors;
triangle-freeness makes the two classes of charges disjoint. -/
theorem neighborhood_count (h4 : NoFourCycle G)
    (hTri : ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj a c)
    (A W : Finset (Fin n)) (E : Finset (Sym2 (Fin n)))
    (hE : ∀ e ∈ E, ∃ u ∈ A, ∃ v ∈ A, e = s(u,v) ∧ G.Adj u v ∧ ∃ w ∈ W, G.Adj w u) :
    E.card ≤ W.card * A.card := by
  classical
  let f (w z : Fin n) : Sym2 (Fin n) :=
    if G.Adj w z then s(w,z) else s(common G w z,z)
  have hsub : E ⊆ W.biUnion (fun w => A.image (f w)) := by
    intro e he
    obtain ⟨u,hu,v,hv,rfl,huv,w,hw,hwu⟩ := hE e he
    apply Finset.mem_biUnion.mpr
    refine ⟨w,hw,?_⟩
    by_cases hwv : w = v
    · subst v
      apply Finset.mem_image.mpr
      exact ⟨u,hu,by simp only [f,if_pos hwu]; exact Sym2.eq_swap⟩
    · apply Finset.mem_image.mpr
      refine ⟨v,hv,?_⟩
      simp only [f, if_neg (hTri w u v hwu huv), common_eq h4 hwv hwu huv.symm]
  calc
    E.card ≤ (W.biUnion (fun w => A.image (f w))).card := Finset.card_le_card hsub
    _ ≤ ∑ w ∈ W, (A.image (f w)).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ W, A.card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ = W.card * A.card := by simp

/-- The size of a common independent witness controls uncovered edges uniformly in
the number, fanout and nesting of the junk ANDs. A may omit all isolated vertices. -/
theorem bound (hL : IsLeastAO G C) (hT : TopForm G C) (h4 : NoFourCycle G)
    (hTri : ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj a c)
    (A W : Finset (Fin n)) (hA : ∀ u v, G.Adj u v → u ∈ A ∧ v ∈ A)
    (hI : ∀ a ∈ W, ∀ b ∈ W, ¬G.Adj a b)
    (hW : ∀ g ∈ junk G C, ∀ S : Finset (Fin n), W ⊆ S →
      gateVal n C g (row S) = true) :
    (Ustar G C).card ≤ W.card * A.card := by
  apply neighborhood_count h4 hTri A W
  intro e he
  obtain ⟨u,v,heq,huv,h⟩ := localization hL hT W hI hW e he
  exact ⟨u,(hA u v huv).1,v,(hA u v huv).2,heq,huv,h⟩

end CoUstarWitness
