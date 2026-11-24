import PEqualNP.CoMinorCatalog4938

namespace CoFormulaMinor4938

def levels (n : Nat) : List Fam :=
  if n=1 then cat1 else if n=2 then cat2 else if n=3 then cat3 else cat4

theorem bounded_four (s : Shape) (small : s.leaves≤4) : bound s (levels s.leaves) := by
  induction s with
  | atom i => exact atom_bound i
  | fork op l r ih jh =>
    have hl := nonempty l
    have hr := nonempty r
    change l.leaves+r.leaves≤4 at small
    have A := ih (by omega)
    have B := jh (by omega)
    change bound (.fork op l r) (levels (l.leaves+r.leaves))
    have casesSize : (l.leaves=1 ∧ r.leaves=1) ∨ (l.leaves=1 ∧ r.leaves=2) ∨
        (l.leaves=1 ∧ r.leaves=3) ∨ (l.leaves=2 ∧ r.leaves=1) ∨
        (l.leaves=2 ∧ r.leaves=2) ∨ (l.leaves=3 ∧ r.leaves=1) := by omega
    rcases casesSize with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩ <;>
      rw [a] at A <;> rw [b] at B <;> rw [a,b]
    · exact compose link11 A B op
    · exact compose link12 A B op
    · exact compose link13 A B op
    · exact compose link21 A B op
    · exact compose link22 A B op
    · exact compose link31 A B op

theorem wedge_five (s : Shape) (reaches : ∀ x∈required,x∈s.value) : 5≤s.leaves := by
  by_contra! tooSmall
  have h := bounded_four s (by omega)
  obtain ⟨T,ht,covers⟩ := h
  have whole : T∈cat1++cat2++cat3++cat4 := by
    simp only [levels] at ht
    split at ht
    · simp [ht]
    · split at ht
      · simp [ht]
      · split at ht <;> simp [ht]
  have noCover := List.all_eq_true.mp cat_bad T whole
  have yes : subsetB required T=true :=
    List.all_eq_true.mpr (fun x hx => List.contains_iff_mem.mpr (covers x (reaches x hx)))
  simp [yes] at noCover

#print axioms wedge_five
end CoFormulaMinor4938
