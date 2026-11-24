import PEqualNP.CoDiagonalDensity
import PEqualNP.CoDiagonalWedges

namespace PEqualNP.Research.CoDiagonalSmall

theorem small_incidence_bound (N : ℕ) (hn : N ≤ 241) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (sq : ∀ p q a b, p ≠ q → a ≠ b → ¬ (I p a ∧ I p b ∧ I q a ∧ I q b))
    (T : Finset (Fin N × Fin N)) (sub : ∀ e ∈ T, I e.1 e.2) : T.card ≤ 16*N := by
  classical
  let U : Finset (Fin N) := Finset.univ
  let lim (p : Fin N) := U.filter (I p)
  have inU (p : Fin N) (_ : p ∈ U) : lim p ⊆ U := Finset.filter_subset _ _
  have free (p : Fin N) (_ : p ∈ U) (q : Fin N) (_ : q ∈ U) (pq : p ≠ q)
      (a : Fin N) (pa : a ∈ lim p) (b : Fin N) (pb : b ∈ lim p) (ab : a ≠ b)
      (qa : a ∈ lim q) (qb : b ∈ lim q) : False :=
    sq p q a b pq ab ⟨(Finset.mem_filter.mp pa).2, (Finset.mem_filter.mp pb).2,
      (Finset.mem_filter.mp qa).2, (Finset.mem_filter.mp qb).2⟩
  have h := CoDiagonalWedges.side_count U U lim inU free
  have un : U.card = N := by simp [U]
  have mom : (∑ p ∈ U, (lim p).card * ((lim p).card-1)) ≤ (N-1)*U.card := by
    simpa only [un, Nat.mul_comm N (N-1)] using h
  have sparse : (∑ p ∈ U, (lim p).card) ≤ 16*N := by
    by_contra hn'
    have large : 16*U.card < (∑ p ∈ U, (lim p).card) := by omega
    have bad := CoDiagonalDensity.side_lower_bound U (fun p => (lim p).card) 16 N
      (by decide) mom large
    omega
  have inject : T.card ≤ (U.sigma lim).card := by
    apply Finset.card_le_card_of_injOn (fun e : Fin N × Fin N => (⟨e.1,e.2⟩ : Σ _ : Fin N, Fin N))
    · intro e he
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub e he⟩⟩
    · intro e he f hf same
      cases e with
      | mk a b =>
        cases f with
        | mk c d =>
          cases same
          rfl
  rw [Finset.card_sigma] at inject
  exact inject.trans sparse

end PEqualNP.Research.CoDiagonalSmall
