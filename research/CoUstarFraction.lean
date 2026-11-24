import PEqualNP.CoUstarWitness
import PEqualNP.Outside.L_meta_1766
import PEqualNP.Outside.L_meta_1572

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1766

namespace CoUstarFraction

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
    · change val C (List.ofFn x) (opnd C a (1-(1 : Fin 2))) = true at hc
      simpa only [sub_one2] using hc
  have hone : val C (List.ofFn x) (opnd C a 1) = true := by
    fin_cases b
    · change val C (List.ofFn x) (opnd C a (1-(0 : Fin 2))) = true at hc
      simpa only [sub_zero2] using hc
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

def near (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (e : Sym2 (Fin n)) : Prop :=
  ∃ u v, e = s(u,v) ∧ G.Adj u v ∧ ∃ w ∈ W, G.Adj w u

theorem edge_rows {m : ℕ} (hL : IsLeastAO G C) (hT : TopForm G C)
    (W : Fin m → Finset (Fin n))
    (hI : ∀ i, ∀ a ∈ W i, ∀ b ∈ W i, ¬G.Adj a b)
    (bothOn : ∀ g ∈ junk G C, ∀ j ∈ junk G C, ∃ i,
      gateVal n C g (row (W i)) = true ∧ gateVal n C j (row (W i)) = true)
    (e : Sym2 (Fin n)) (he : e ∈ Ustar G C) :
    ∃ g ∈ junk G C, ∀ i, gateVal n C g (row (W i)) = true → near G (W i) e := by
  have via {a : ℕ} {b : Fin 2} {g : ℕ} (hr : OrReaches n C (opnd C a b) g)
      (S : Finset (Fin n)) (hon : gateVal n C g (row S) = true) :
      val C (List.ofFn (row S)) (opnd C a b) = true :=
    orStep_up (n := n) (by simp) (orReaches_reach g _ hr).1 hon
  rcases PEqualNP.Outside.L_meta_1766 n G C hL hT e he with
    ⟨u,v,rfl,a,ha,b,g,hg,hu,hr,_⟩ | ⟨u,v,rfl,a,ha,g,hg,j,hj,_,hr,hs,_,_⟩
  · refine ⟨g,hg,?_⟩
    intro i on
    have adj : G.Adj u v := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using (Finset.mem_sdiff.mp he).1
    have on' : gateVal n C g (row (insert u (W i))) = true := by
      apply PEqualNP.Outside.L_meta_1572_aux.wires_mono C (x := row (W i)) (w := n+g)
      · intro q hq
        exact ⟨hL.1.1 q hq, Nat.le_of_eq (hL.1.2.2 q hq)⟩
      · intro p hp
        simpa [row] using (Finset.mem_insert_of_mem (show p ∈ W i from by simpa [row] using hp) : p ∈ insert u (W i))
      · exact on
    have hraw := reach_var_val (row (insert u (W i))) _ u (mem_orIn_reach u hu) (by simp [row])
    exact ⟨u,v,rfl,adj,neighbor_from_insert (W i) (hI i) u (both hL.1 ha _ b hraw (via hr _ on'))⟩
  · obtain ⟨i,og,oj⟩ := bothOn g hg j hj
    have h1 : val C (List.ofFn (row (W i))) (opnd C a (1-(0 : Fin 2))) = true := by
      simpa only [sub_zero2] using via hs _ oj
    obtain ⟨p,q,adj,hp,hq⟩ := row_edge (both hL.1 ha _ 0 (via hr _ og) h1)
    exact (hI i p hp q hq adj).elim

noncomputable section
open scoped BigOperators
open Classical in
theorem fractional {m d : ℕ} (hL : IsLeastAO G C) (hT : TopForm G C)
    (h4 : NoFourCycle G) (hTri : ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj a c)
    (A : Finset (Fin n)) (hA : ∀ a b, G.Adj a b → a ∈ A ∧ b ∈ A)
    (W : Fin m → Finset (Fin n))
    (hI : ∀ i, ∀ a ∈ W i, ∀ b ∈ W i, ¬G.Adj a b)
    (freq : ∀ g ∈ junk G C, d ≤ (Finset.univ.filter (fun i => gateVal n C g (row (W i)) = true)).card)
    (bothOn : ∀ g ∈ junk G C, ∀ j ∈ junk G C, ∃ i,
      gateVal n C g (row (W i)) = true ∧ gateVal n C j (row (W i)) = true) :
    (Ustar G C).card * d ≤ ∑ i, (W i).card * A.card := by
  classical
  let U := Ustar G C
  have lower (e) (he : e ∈ U) : d ≤ (Finset.univ.filter (fun i => near G (W i) e)).card := by
    obtain ⟨g,hg,h⟩ := edge_rows hL hT W hI bothOn e he
    exact (freq g hg).trans (Finset.card_le_card (fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,h i (Finset.mem_filter.mp hi).2⟩))
  have upper (i : Fin m) : (U.filter (near G (W i))).card ≤ (W i).card * A.card := by
    apply CoUstarWitness.neighborhood_count h4 hTri
    intro e he
    obtain ⟨u,v,eq,adj,w,hw,hwu⟩ := (Finset.mem_filter.mp he).2
    exact ⟨u,(hA _ _ adj).1,v,(hA _ _ adj).2,eq,adj,w,hw,hwu⟩
  calc
    U.card * d = ∑ _e ∈ U, d := by simp
    _ ≤ ∑ e ∈ U, (Finset.univ.filter (fun i => near G (W i) e)).card :=
      Finset.sum_le_sum lower
    _ = ∑ i, (U.filter (near G (W i))).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => upper i)
end
end CoUstarFraction
