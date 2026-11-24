import Mathlib

namespace PEqualNP.Research.CoSharedWitness

variable {V : Type*} [DecidableEq V]

private def Small (k : ℕ) (p : Finset V → Prop) : Prop :=
  ∀ x, p x → ∃ y, y ⊆ x ∧ y.card ≤ k ∧ p y

private theorem join_two {i j : ℕ} {p q : Finset V → Prop}
    (mp : Monotone p) (mq : Monotone q) (sp : Small i p) (sq : Small j q) :
    Small (i + j) (fun s => p s ∧ q s) := by
  intro x h
  obtain ⟨a, ha, ca, pa⟩ := sp x h.1
  obtain ⟨b, hb, cb, qb⟩ := sq x h.2
  refine ⟨a ∪ b, Finset.union_subset ha hb, ?_, mp Finset.subset_union_left pa,
    mq Finset.subset_union_right qb⟩
  exact (Finset.card_union_le a b).trans (Nat.add_le_add ca cb)

-- A clean prefix with one shared exceptional signal appears on each independent
-- row as an OR of singleton tests and optionally that same signal. The local
-- parts may also be constants, covering omitted AND pins.
theorem second_dirty_has_small_witness
    (left right shared : Finset V → Prop) (useL useR : Prop)
    (ml : Monotone left) (mr : Monotone right) (md : Monotone shared)
    (sl : ∀ x, left x → ∃ y, y ⊆ x ∧ y.card ≤ 1 ∧ left y)
    (sr : ∀ x, right x → ∃ y, y ⊆ x ∧ y.card ≤ 1 ∧ right y)
    (sd : ∀ x, shared x → ∃ y, y ⊆ x ∧ y.card ≤ 2 ∧ shared y)
    (x : Finset V) (hl : left x ∨ useL ∧ shared x) (hr : right x ∨ useR ∧ shared x) :
    ∃ y, y ⊆ x ∧ y.card ≤ 3 ∧
      (left y ∨ useL ∧ shared y) ∧ (right y ∨ useR ∧ shared y) := by
  rcases hl with l | ⟨ul,d⟩ <;> rcases hr with r | ⟨ur,e⟩
  · obtain ⟨y,h,c,a,b⟩ := join_two (i:=1) (j:=1) ml mr sl sr x ⟨l,r⟩
    exact ⟨y,h,by omega,Or.inl a,Or.inl b⟩
  · obtain ⟨y,h,c,a,b⟩ := join_two (i:=1) (j:=2) ml md sl sd x ⟨l,e⟩
    exact ⟨y,h,c,Or.inl a,Or.inr ⟨ur,b⟩⟩
  · obtain ⟨y,h,c,a,b⟩ := join_two (i:=2) (j:=1) md mr sd sr x ⟨d,r⟩
    exact ⟨y,h,c,Or.inr ⟨ul,a⟩,Or.inl b⟩
  · obtain ⟨y,h,c,a⟩ := sd x d
    exact ⟨y,h,by omega,Or.inr ⟨ul,a⟩,Or.inr ⟨ur,a⟩⟩

end PEqualNP.Research.CoSharedWitness
