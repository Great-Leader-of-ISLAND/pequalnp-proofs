import CoGeneric2147

namespace CoGeneric2147

set_option maxRecDepth 100000
set_option maxHeartbeats 0

instance arcDec2147 (B : V → Finset V) (S : Finset V) : Decidable (arc B S) := by
  unfold arc
  infer_instance

def nonFlat2147 (B : V → Finset V) (S : Finset V) : Prop := ∀ i, ¬ S ⊆ B i

instance nonFlatDec2147 (B : V → Finset V) (S : Finset V) : Decidable (nonFlat2147 B S) := by
  unfold nonFlat2147
  infer_instance

private theorem allFivePoint : ∀ S ∈ (Finset.univ : Finset V).powersetCard 5,
    ¬arc line S := by decide +kernel
private theorem allFiveLine : ∀ T ∈ (Finset.univ : Finset V).powersetCard 5,
    ¬arc pencil T := by decide +kernel

private def pointInfo2147 (k : ℕ) := ∀ S ∈ (Finset.univ : Finset V).powersetCard k,
    arc line S → nonFlat2147 line S ∧ nonFlat2147 pencil (missing S)
private def lineInfo2147 (k : ℕ) := ∀ T ∈ (Finset.univ : Finset V).powersetCard k,
    arc pencil T → nonFlat2147 pencil T ∧ nonFlat2147 line (dualMissing T)

private theorem threePoint : pointInfo2147 3 := by unfold pointInfo2147; decide +kernel
private theorem fourPoint : pointInfo2147 4 := by unfold pointInfo2147; decide +kernel
private theorem threeLine : lineInfo2147 3 := by unfold lineInfo2147; decide +kernel
private theorem fourLine : lineInfo2147 4 := by unfold lineInfo2147; decide +kernel

private theorem lineCard2147 : ∀ i : V, (line i).card=4 := by decide +kernel
/-- These tables involve at most 78 pairs. -/
private theorem smallMissing : ∀ k : Fin 3,
    ∀ T ∈ (Finset.univ : Finset V).powersetCard k.val, 5 ≤ (dualMissing T).card := by
  decide +kernel
private theorem pairExtension : ∀ R ∈ (Finset.univ : Finset V).powersetCard 2,
    ∃ i : V, R ⊆ line i ∧ ∀ z : V, z ∉ line i → arc line (insert z R) := by
  decide +kernel

theorem arc_down2147 {B : V → Finset V} {S U : Finset V} (h : S ⊆ U) (ha : arc B U) :
    arc B S := fun i j hj hsub => ha i j hj (fun x hx => h (hsub hx))

private theorem card_class2147 {B : V → Finset V} {S : Finset V}
    (five : ∀ R ∈ (Finset.univ : Finset V).powersetCard 5, ¬arc B R)
    (ha : arc B S) (hsize : 3 ≤ S.card) : S.card = 3 ∨ S.card = 4 := by
  by_contra! h
  have h5 : 5 ≤ S.card := by omega
  obtain ⟨R, hR, hcard⟩ := Finset.exists_subset_card_eq h5
  exact five R (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ R,hcard⟩) (arc_down2147 hR ha)

theorem largePoint2147 {S : Finset V} (ha : arc line S) (hsize : 3 ≤ S.card) :
    nonFlat2147 line S ∧ nonFlat2147 pencil (missing S) := by
  rcases card_class2147 allFivePoint ha hsize with h|h
  · exact threePoint S (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S,h⟩) ha
  · exact fourPoint S (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S,h⟩) ha

theorem largeLine2147 {T : Finset V} (ha : arc pencil T) (hsize : 3 ≤ T.card) :
    nonFlat2147 pencil T ∧ nonFlat2147 line (dualMissing T) := by
  rcases card_class2147 allFiveLine ha hsize with h|h
  · exact threeLine T (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T,h⟩) ha
  · exact fourLine T (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T,h⟩) ha

theorem smallTriangle2147 {S T : Finset V} (ind : ∀ x∈S, ∀ t∈T, ¬inc x t)
    (hs : S.card ≤ 2) (ht : T.card ≤ 2) :
    ∃ R : Finset V, S ⊆ R ∧ R ⊆ dualMissing T ∧ R.card=3 ∧ arc line R := by
  classical
  let W := dualMissing T
  have hw : 5 ≤ W.card := smallMissing ⟨T.card,by omega⟩ T
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T,rfl⟩)
  have hsw : S ⊆ W := fun x hx => (dual_membership _ _).mpr (ind x hx)
  have hd : 2-S.card ≤ (W \ S).card := by
    rw [Finset.card_sdiff_of_subset hsw]
    omega
  obtain ⟨D,hD,hcard⟩ := Finset.exists_subset_card_eq hd
  have dis : Disjoint S D := Finset.disjoint_left.mpr
    (fun x hx hxd => (Finset.mem_sdiff.mp (hD hxd)).2 hx)
  let A := S ∪ D
  have hA : A.card=2 := by
    change (S ∪ D).card=2
    rw [Finset.card_union_of_disjoint dis,hcard]
    omega
  have hAW : A ⊆ W := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hsw hx
    · exact (Finset.mem_sdiff.mp (hD hx)).1
  obtain ⟨i,hai,hnew⟩ := pairExtension A
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ A,hA⟩)
  obtain ⟨z,hz,hzi⟩ : ∃ z∈W, z∉line i := by
    by_contra! h
    have hle := Finset.card_le_card (show W ⊆ line i from h)
    rw [lineCard2147 i] at hle
    omega
  have hza : z∉A := fun h => hzi (hai h)
  refine ⟨insert z A,?_,?_,?_,hnew z hzi⟩
  · intro x hx
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl|h
    · exact hz
    · exact hAW h
  · rw [Finset.card_insert_of_notMem hza,hA]

def genericExtension2147 (S T : Finset V) : Prop :=
  ∃ U, S⊆U ∧ T⊆missing U ∧
      (∀ x∉U, ∃ l∈missing U, inc x l) ∧
      (¬∃ t, ∀ x∈U, inc x t) ∧ (¬∃ x, ∀ t∈missing U, inc x t)

private theorem nonLine2147 {S : Finset V} (h : nonFlat2147 line S) :
    ¬∃ t, ∀ x∈S, inc x t := by
  rintro ⟨t,ht⟩
  exact h t (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht x hx⟩)

private theorem nonPencil2147 {T : Finset V} (h : nonFlat2147 pencil T) :
    ¬∃ x, ∀ t∈T, inc x t := by
  rintro ⟨x,hx⟩
  exact h x (fun t ht => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx t ht⟩)

private theorem weakenGeneric2147 {S R T : Finset V} (h : S ⊆ R)
    (g : genericExtension2147 R T) : genericExtension2147 S T := by
  obtain ⟨U,hu,ht,hmax,hp,hl⟩ := g
  exact ⟨U,fun x hx => hu (h hx),ht,hmax,hp,hl⟩

theorem generic_iff_arcs (S T : Finset V) (ind : ∀ x∈S, ∀ t∈T, ¬inc x t) :
    genericExtension2147 S T ↔ arc line S ∧ arc pencil T := by
  constructor
  · rintro ⟨U,hs,ht,_,h1,h2⟩
    have hac := closed_arcs (S:=U) (T:=missing U)
      (fun x hx t ht' => (missing_membership _ _).mp ht' x hx) h1 h2
    exact ⟨arc_down2147 hs hac.1, arc_down2147 ht hac.2⟩
  · rintro ⟨ha,hb⟩
    by_cases hS : 3 ≤ S.card
    · obtain ⟨h1,h2⟩ := largePoint2147 ha hS
      exact closure ind (nonLine2147 h1) (nonPencil2147 h2)
    by_cases hT : 3 ≤ T.card
    · let R := dualMissing T
      have sep : ∀ x∈R, ∀ t∈T, ¬inc x t :=
        fun x hx => (dual_membership _ _).mp hx
      have sb : S ⊆ R := fun x hx => (dual_membership _ _).mpr (ind x hx)
      obtain ⟨h1,h2⟩ := largeLine2147 hb hT
      apply weakenGeneric2147 sb
      apply closure sep (nonLine2147 h2)
      rintro ⟨x,hx⟩
      apply nonPencil2147 h1
      refine ⟨x,fun t ht => hx t ((missing_membership R t).mpr (fun y hy => sep y hy t ht))⟩
    obtain ⟨R,hsr,hrt,h3,har⟩ := smallTriangle2147 ind (by omega) (by omega)
    obtain ⟨h1,h2⟩ := largePoint2147 har (by omega)
    exact weakenGeneric2147 hsr (closure
      (fun x hx => (dual_membership _ x).mp (hrt hx)) (nonLine2147 h1) (nonPencil2147 h2))

theorem excluded_iff_triple2147 {S T : Finset V} (ind : ∀ x∈S, ∀ t∈T, ¬inc x t) :
    ¬genericExtension2147 S T ↔
      (∃ i j, j∈line i ∧ (line i).erase j ⊆ S) ∨
      (∃ i j, j∈pencil i ∧ (pencil i).erase j ⊆ T) := by
  classical
  rw [generic_iff_arcs S T ind]
  constructor
  · intro h
    by_contra none
    apply h
    exact ⟨fun i j hj hs => none (Or.inl ⟨i,j,hj,hs⟩),
           fun i j hj hs => none (Or.inr ⟨i,j,hj,hs⟩)⟩
  · rintro (⟨i,j,hj,hs⟩|⟨i,j,hj,hs⟩) h
    · exact h.1 i j hj hs
    · exact h.2 i j hj hs

/-- The point/line coordinate tags keep dual exceptions separate. -/
def triples2147 (B : V → Finset V) : Finset (Finset V) :=
  Finset.univ.biUnion (fun i => (B i).image (fun j => (B i).erase j))

def minimalSupports2147 : Finset (Finset V × Finset V) :=
  (triples2147 line).image (fun R => (R,∅)) ∪ (triples2147 pencil).image (fun R => (∅,R))

theorem supportCount2147 : (triples2147 line).card=52 ∧ (triples2147 pencil).card=52 ∧
    minimalSupports2147.card=104 ∧ ∀ b∈minimalSupports2147, b.1.card+b.2.card=3 := by
  decide +kernel

private theorem memTriple2147 {B : V → Finset V} {R : Finset V} :
    R ∈ triples2147 B ↔ ∃ i j, j∈B i ∧ (B i).erase j=R := by
  simp [triples2147]

theorem exactSupport2147 {S T : Finset V} (ind : ∀ x∈S, ∀ t∈T, ¬inc x t) :
    ¬genericExtension2147 S T ↔
    ∃ b ∈ minimalSupports2147, b.1 ⊆ S ∧ b.2 ⊆ T := by
  rw [excluded_iff_triple2147 ind]
  constructor
  · rintro (⟨i,j,hj,hsub⟩|⟨i,j,hj,hsub⟩)
    · refine ⟨((line i).erase j,∅),Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨_,memTriple2147.mpr ⟨i,j,hj,rfl⟩,rfl⟩),hsub,Finset.empty_subset _⟩
    · refine ⟨(∅,(pencil i).erase j),Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨_,memTriple2147.mpr ⟨i,j,hj,rfl⟩,rfl⟩),Finset.empty_subset _,hsub⟩
  · rintro ⟨b,hb,hs,ht⟩
    rcases Finset.mem_union.mp hb with h | h
    · obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨i,j,hj,rfl⟩ := memTriple2147.mp hR
      exact Or.inl ⟨i,j,hj,hs⟩
    · obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨i,j,hj,rfl⟩ := memTriple2147.mp hR
      exact Or.inr ⟨i,j,hj,ht⟩

#print axioms CoGeneric2147.generic_iff_arcs
#print axioms CoGeneric2147.excluded_iff_triple2147

end CoGeneric2147
