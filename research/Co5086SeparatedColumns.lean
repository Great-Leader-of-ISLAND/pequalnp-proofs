import Mathlib

namespace Co5086SeparatedColumns

variable {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def Legal (p l : Fin N) (S : Finset (Fin N)) : Fin N ⊕ Fin N → Prop
  | .inl u => u = p ∧ ∃ t ∈ S, I p t
  | .inr u => u = l ∧ l ∉ S

/-- At most q other lines cannot cover any whole line of q+1 points. -/
theorem uncovered (degree : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (joinLine : ∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l)
    (T : Finset (Fin N)) (hT : T.card ≤ q) (l : Fin N) (absent : l ∉ T) :
    ∃ p, I p l ∧ ¬ ∃ t ∈ T, I p t := by
  classical
  by_contra no
  have covered (p : {p : Fin N // I p l}) : ∃ t ∈ T, I p.val t :=
    Classical.byContradiction (fun miss => no ⟨p.val,p.property,miss⟩)
  choose f hf using covered
  let witness : {p : Fin N // I p l} → ↥T := fun p => ⟨f p,(hf p).1⟩
  have injective : Function.Injective witness := by
    intro p r he
    have eq : f p = f r := congrArg Subtype.val he
    apply Subtype.ext
    by_contra ne
    have e : l = f p := (joinLine p.val r.val ne).unique
      ⟨p.property,r.property⟩ ⟨(hf p).2, eq.symm ▸ (hf r).2⟩
    exact absent (e.symm ▸ (hf p).1)
  have count := Fintype.card_le_of_injective witness injective
  rw [degree,Fintype.card_coe] at count
  omega

/-- Two requests returning a common label on every flag must have equal
line sets. Only the bound for the second input is needed for inclusion. -/
theorem compatible_subset (degree : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (joinLine : ∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l)
    (S T : Finset (Fin N)) (hT : T.card ≤ q)
    (both : ∀ p l, I p l → ∃ label, Legal I p l S label ∧ Legal I p l T label) :
    S ⊆ T := by
  intro l hs
  by_contra hnot
  obtain ⟨p,hp,miss⟩ := uncovered I degree joinLine T hT l hnot
  obtain ⟨u,hsound,tsound⟩ := both p l hp
  cases u with
  | inl v => exact miss tsound.2
  | inr v => exact hsound.2 hs

abbrev Small (N q : ℕ) := {S : Finset (Fin N) // S.card ≤ q}

/-- A column-first protocol's entry into its all-row suffix is injective on
all size-at-most-q requests, even if suffixes could otherwise be shared. -/
theorem entry_injective {J : Type*} (degree : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (joinLine : ∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l)
    (entry : Small N q → J) (answer : J → Fin N → Fin N → Fin N ⊕ Fin N)
    (sound : ∀ S p l, I p l → Legal I p l S.val (answer (entry S) p l)) :
    Function.Injective entry := by
  intro S T same
  apply Subtype.ext
  apply le_antisymm
  · apply compatible_subset I degree joinLine _ _ T.property
    intro p l hp
    exact ⟨_,sound S p l hp,same.symm ▸ sound T p l hp⟩
  · apply compatible_subset I degree joinLine _ _ S.property
    intro p l hp
    exact ⟨_,sound T p l hp,same ▸ sound S p l hp⟩

def pencil (r m : Fin N) : Finset (Fin N) :=
  (Finset.univ.filter fun l => I r l).erase m

theorem mem_pencil (r m t : Fin N) : t ∈ pencil I r m ↔ t ≠ m ∧ I r t := by
  simp [pencil]

/-- The whole restriction to pencil columns, including pairs of disjoint flags. -/
theorem point_on_pencil (joinLine : ∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l)
    (r m : Fin N) (rm : I r m) (other : ∃ t, t ≠ m ∧ I r t) (p : Fin N) :
    (∃ t ∈ pencil I r m, I p t) ↔ p = r ∨ ¬I p m := by
  constructor
  · rintro ⟨t,ht,pt⟩
    obtain ⟨tm,rt⟩ := (mem_pencil I r m t).mp ht
    by_cases pr : p = r
    · exact Or.inl pr
    · right
      intro pm
      exact tm ((joinLine p r pr).unique ⟨pt,rt⟩ ⟨pm,rm⟩)
  · rintro (rfl | pm)
    · obtain ⟨t,tm,rt⟩ := other
      exact ⟨t,(mem_pencil I _ _ _).mpr ⟨tm,rt⟩,rt⟩
    · have pr : p ≠ r := fun e => pm (e.symm ▸ rm)
      obtain ⟨t,⟨pt,rt⟩,_⟩ := joinLine p r pr
      have tm : t ≠ m := fun e => pm (e ▸ pt)
      exact ⟨t,(mem_pencil I _ _ _).mpr ⟨tm,rt⟩,pt⟩

theorem line_on_pencil (r m l : Fin N) : l ∉ pencil I r m ↔ l = m ∨ ¬I r l := by
  rw [mem_pencil]
  by_cases h : l = m <;> simp [h]

end Co5086SeparatedColumns
