import Mathlib

namespace PEqualNP.Research.PivotProjection

/-- The active input points contain both endpoints of an edge. -/
def hasEdge {V : Type*} (G : SimpleGraph V) (X : Finset V) : Prop :=
  ∃ a ∈ X, ∃ b ∈ X, G.Adj a b

/-- Given the active subset P of two side variables, any independent side
pattern extends to an independent input where v is sensitive. The set N can
be any three or more neighbors with the stated common-neighbor property. -/
theorem sensitive_projection {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v p q : V) (N P : Finset V)
    (hpv : p ≠ v) (hqv : q ≠ v) (hN : 3 ≤ N.card) (hnear : ∀ w ∈ N, G.Adj v w)
    (hcommon : ∀ z : V, z ≠ v → (N.filter (G.Adj z)).card ≤ 1)
    (hP : P ⊆ {p,q}) (hind : ¬ hasEdge G P) :
    ∃ X : Finset V, v ∉ X ∧ X ∩ {p,q} = P ∧ ¬ hasEdge G X ∧ hasEdge G (insert v X) := by
  classical
  let bad (z : V) : Finset V := if z ∈ P then N.filter (G.Adj z) else {z}
  have small (z : V) (hz : z ≠ v) : (bad z).card ≤ 1 := by
    by_cases hzP : z ∈ P
    · simpa only [bad, if_pos hzP] using hcommon z hz
    · simp [bad, hzP]
  obtain ⟨w, hw, hout⟩ : ∃ w ∈ N, w ∉ bad p ∪ bad q := by
    by_contra! h
    have hc := Finset.card_le_card (show N ⊆ bad p ∪ bad q from h)
    have hu := Finset.card_union_le (bad p) (bad q)
    have hp := small p hpv
    have hq := small q hqv
    omega
  have avoids (z : V) (hz : z ∈ ({p,q} : Finset V)) : w ∉ bad z := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact fun h => hout (Finset.mem_union_left _ h)
    · exact fun h => hout (Finset.mem_union_right _ h)
  have sep (z : V) (hz : z ∈ P) : ¬ G.Adj z w := by
    intro ha
    apply avoids z (hP hz)
    simpa only [bad, if_pos hz, Finset.mem_filter] using And.intro hw ha
  have vw : G.Adj v w := hnear w hw
  have hwv : v ≠ w := by
    intro he
    simpa [he] using vw
  have hvP : v ∉ P := by
    intro hv
    have hs := hP hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    exact hs.elim (fun e => hpv e.symm) (fun e => hqv e.symm)
  refine ⟨insert w P, ?_, ?_, ?_, ?_⟩
  · simpa [hwv] using hvP
  · ext z
    constructor
    · intro hz
      obtain ⟨hzX, hzS⟩ := Finset.mem_inter.mp hz
      rcases Finset.mem_insert.mp hzX with he | hin
      · subst z
        by_contra hno
        apply avoids w hzS
        simp [bad, hno]
      · exact hin
    · intro hz
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hz, hP hz⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases Finset.mem_insert.mp ha with hwa | ha
    · subst a
      rcases Finset.mem_insert.mp hb with hwb | hb
      · simpa [hwb] using hab
      · exact sep b hb hab.symm
    · rcases Finset.mem_insert.mp hb with hwb | hb
      · subst b
        exact sep a ha hab
      · exact hind ⟨a,ha,b,hb,hab⟩
  · exact ⟨v, Finset.mem_insert_self _ _, w,
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), vw⟩

/-- If masking a pair of side literals always hides v at the circuit output,
the mask must set two adjacent side variables to true. -/
theorem masking_requires_edge {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v p q : V) (N P : Finset V)
    (hpv : p ≠ v) (hqv : q ≠ v) (hN : 3 ≤ N.card) (hnear : ∀ w ∈ N, G.Adj v w)
    (hcommon : ∀ z : V, z ≠ v → (N.filter (G.Adj z)).card ≤ 1)
    (hP : P ⊆ {p,q})
    (hmask : ∀ X : Finset V, v ∉ X → X ∩ {p,q} = P →
      (hasEdge G X ↔ hasEdge G (insert v X))) : p ∈ P ∧ q ∈ P ∧ G.Adj p q := by
  classical
  have hed : hasEdge G P := by
    by_contra hno
    obtain ⟨X,hv,hpat,hzero,hone⟩ := sensitive_projection G v p q N P hpv hqv hN hnear hcommon hP hno
    exact hzero ((hmask X hv hpat).mpr hone)
  obtain ⟨a,ha,b,hb,hab⟩ := hed
  have hsa := hP ha
  have hsb := hP hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsa hsb
  rcases hsa with e1 | e1 <;> rcases hsb with e2 | e2
  · exact False.elim (by simpa [e1,e2] using hab)
  · exact ⟨by simpa [e1] using ha, by simpa [e2] using hb, by simpa [e1,e2] using hab⟩
  · exact ⟨by simpa [e2] using hb, by simpa [e1] using ha, by simpa [e1,e2] using hab.symm⟩
  · exact False.elim (by simpa [e1,e2] using hab)

end PEqualNP.Research.PivotProjection
