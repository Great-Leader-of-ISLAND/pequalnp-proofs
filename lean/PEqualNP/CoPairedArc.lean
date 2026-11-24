import Mathlib

namespace PEqualNP.Research.PairedArc

/-- A meeting block spends a distinct point of the arc on the row. -/
theorem thin_of_arc {n m k : ℕ} (S : Fin m → Finset (Fin n)) (A : Finset (Fin n))
    (B : Fin k → Finset (Fin n)) (hsub : ∀ i, B i ⊆ A)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hcap : ∀ i, (S i ∩ A).card ≤ 2) :
    ∀ i, (Finset.univ.filter (fun j : Fin k => (B j ∩ S i).Nonempty)).card ≤ 2 := by
  classical
  intro i
  let T := Finset.univ.filter (fun j : Fin k => (B j ∩ S i).Nonempty)
  have obtainPoint : ∀ j : ↥T, ∃ p, p ∈ B j.val ∩ S i :=
    fun j => (Finset.mem_filter.mp j.property).2
  choose point hp using obtainPoint
  let f : ↥T → ↥(S i ∩ A) := fun j => ⟨point j, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp (hp j)).2, hsub _ (Finset.mem_inter.mp (hp j)).1⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have he : point a = point b := congrArg Subtype.val hab
    have ha := (Finset.mem_inter.mp (hp a)).1
    have hb := (Finset.mem_inter.mp (hp b)).1
    rw [← he] at hb
    exact Finset.disjoint_left.mp (hdisj _ _ hne) ha hb
  have hn : T.card ≤ (S i ∩ A).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  exact hn.trans (hcap i)

/-- Partition an arbitrary fourteen-point arc into seven genuinely disjoint pairs. -/
theorem seven_pairs_of_arc14 {n m : ℕ} (S : Fin m → Finset (Fin n)) (A : Finset (Fin n))
    (hA : A.card = 14) (hcap : ∀ i, (S i ∩ A).card ≤ 2) :
    ∃ B : Fin 7 → Finset (Fin n), (∀ i, (B i).card = 2) ∧ (∀ i, B i ⊆ A) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      ∀ i, (Finset.univ.filter (fun j : Fin 7 => (B j ∩ S i).Nonempty)).card ≤ 2 := by
  classical
  let e : ↥A ≃ Fin 14 := Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hA)
  let point (j : Fin 14) : Fin n := (e.symm j).val
  have inj : Function.Injective point := fun _ _ h => e.symm.injective (Subtype.ext h)
  let lo (i : Fin 7) : Fin 14 := ⟨i.val, by have := i.isLt; omega⟩
  let hi (i : Fin 7) : Fin 14 := ⟨i.val + 7, by have := i.isLt; omega⟩
  let B (i : Fin 7) : Finset (Fin n) := {point (lo i), point (hi i)}
  have distinct : ∀ i, point (lo i) ≠ point (hi i) := by
    intro i h
    have hv := congrArg Fin.val (inj h)
    change i.val = i.val+7 at hv
    omega
  have card : ∀ i, (B i).card=2 := by
    intro i
    simp [B, distinct i]
  have sub : ∀ i, B i ⊆ A := by
    intro i x hx
    change x ∈ ({point (lo i), point (hi i)} : Finset (Fin n)) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (e.symm (lo i)).property
    · exact (e.symm (hi i)).property
  have disj : ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hxi hxj
    rcases hxi with ha | ha <;> rcases hxj with hb | hb
    all_goals
      have he := congrArg Fin.val (inj (ha.symm.trans hb))
      simp only [lo, hi] at he
      have hI := i.isLt
      have hJ := j.isLt
      exact hij (Fin.ext (by omega))
  exact ⟨B, card, sub, disj, thin_of_arc S A B sub disj hcap⟩

end PEqualNP.Research.PairedArc
