import Mathlib
namespace CoSmallSides2567
abbrev V := Fin 13

def incident (p l : V) : Prop := (p.val+l.val)%13∈([0,1,3,9]:List Nat)
instance (p l : V) : Decidable (incident p l) := by unfold incident; infer_instance

def missing (S : Finset V) : Finset V := Finset.univ.filter (fun l => ∀ p∈S, ¬incident p l)

theorem symmetry (p l : V) : incident p l ↔ incident l p := by
  simp only [incident,Nat.add_comm p.val l.val]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem four : ∀ S∈(Finset.univ : Finset V).powersetCard 4, (missing S).card ≤ 3 := by decide +kernel

theorem small_side {S T : Finset V} (ind : ∀ p∈S, ∀ l∈T, ¬incident p l) : S.card≤3 ∨ T.card≤3 := by
  by_cases small : S.card≤3
  · exact Or.inl small
  right
  have enough : 4≤S.card := by omega
  obtain ⟨A,asub,acard⟩ := Finset.exists_subset_card_eq enough
  have sub : T⊆missing A := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => ind p (asub hp) l hl⟩
  exact (Finset.card_le_card sub).trans (four A (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ A,acard⟩))

/-- For monotone outputs, the two small-side test families force the exact
    incidence function on the entire 26-variable cube. -/
theorem tests_exact (F : Finset V → Finset V → Prop)
    (mono : ∀ {S T S' T'}, S⊆S' → T⊆T' → F S T → F S' T')
    (hits : ∀ p l, incident p l → F {p} {l})
    (negative : ∀ S, S.card≤3 → ¬F S (missing S) ∧ ¬F (missing S) S)
    (S T : Finset V) : F S T ↔ ∃ p∈S, ∃ l∈T, incident p l := by
  constructor
  · intro accepted
    by_contra no
    have ind (p) (hp : p∈S) (l) (hl : l∈T) : ¬incident p l :=
      fun edge => no ⟨p,hp,l,hl,edge⟩
    rcases small_side ind with left|right
    · apply (negative S left).1
      exact mono (fun _ h => h) (fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => ind p hp l hl⟩) accepted
    · apply (negative T right).2
      exact mono (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl h => ind p hp l hl ((symmetry l p).mp h)⟩)
        (fun _ h => h) accepted
  · rintro ⟨p,hp,l,hl,edge⟩
    exact mono (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl) (hits p l edge)

#print axioms CoSmallSides2567.tests_exact
end CoSmallSides2567
