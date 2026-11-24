import Mathlib
namespace CoSmallSides2567
abbrev V := Fin 13

def incident (p l : V) : Prop := (p.val+l.val)%13∈([0,1,3,9]:List Nat)
instance (p l : V) : Decidable (incident p l) := by unfold incident; infer_instance

def missing (S : Finset V) : Finset V := Finset.univ.filter (fun l => ∀ p∈S, ¬incident p l)

theorem symmetry (p l : V) : incident p l ↔ incident l p := by
  simp only [incident,Nat.add_comm p.val l.val]

private def pencil (p : V) : Finset V := Finset.univ.filter (incident p)

private theorem card_pencil : ∀ p : V, (pencil p).card=4 := by decide +kernel
private theorem pair_pencil : ∀ p q : V, p≠q → (pencil p ∩ pencil q).card=1 := by decide +kernel

private theorem four_pencils (p q r s : V) (pq : p≠q) (pr : p≠r) (ps : p≠s)
    (qr : q≠r) (qs : q≠s) (rs : r≠s) :
    10 ≤ (((pencil p ∪ pencil q) ∪ pencil r) ∪ pencil s).card := by
  let P := pencil p
  let Q := pencil q
  let R := pencil r
  let T := pencil s
  have h1 := Finset.card_union_add_card_inter P Q
  have h2 := Finset.card_union_add_card_inter (P∪Q) R
  have h3 := Finset.card_union_add_card_inter ((P∪Q)∪R) T
  have rbound : ((P∪Q)∩R).card≤2 := by
    rw [Finset.union_inter_distrib_right]
    exact (Finset.card_union_le _ _).trans (by rw [pair_pencil p r pr,pair_pencil q r qr])
  have sbound : (((P∪Q)∪R)∩T).card≤3 := by
    rw [Finset.union_inter_distrib_right,Finset.union_inter_distrib_right]
    have u := Finset.card_union_le (P∩T) (Q∩T)
    have v := Finset.card_union_le ((P∩T)∪(Q∩T)) (R∩T)
    have x := pair_pencil p s ps
    have y := pair_pencil q s qs
    have z := pair_pencil r s rs
    change (P∩T).card=1 at x
    change (Q∩T).card=1 at y
    change (R∩T).card=1 at z
    omega
  change 10 ≤ (((P∪Q)∪R)∪T).card
  have pc : P.card=4 := card_pencil p
  have qc : Q.card=4 := card_pencil q
  have rc : R.card=4 := card_pencil r
  have tc : T.card=4 := card_pencil s
  have pcq : (P∩Q).card=1 := pair_pencil p q pq
  omega

private theorem four (S : Finset V) (hS : S∈(Finset.univ : Finset V).powersetCard 4) :
    (missing S).card≤3 := by
  classical
  have sc := (Finset.mem_powersetCard.mp hS).2
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0<S.card by omega)
  have erased := Finset.card_erase_add_one hp
  obtain ⟨q,r,s,qr,qs,rs,eq⟩ := Finset.card_eq_three.mp (show (S.erase p).card=3 by omega)
  have miss : p∉({q,r,s} : Finset V) := eq ▸ Finset.notMem_erase p S
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at miss
  have orig : S=insert p {q,r,s} := by rw [←eq,Finset.insert_erase hp]
  let U := ((pencil p∪pencil q)∪pencil r)∪pencil s
  have large : 10≤U.card := four_pencils _ _ _ _ miss.1 miss.2.1 miss.2.2 qr qs rs
  have dis : Disjoint (missing S) U := by
    apply Finset.disjoint_left.mpr
    intro l hl hU
    have avoids := (Finset.mem_filter.mp hl).2
    change l∈((pencil p∪pencil q)∪pencil r)∪pencil s at hU
    simp only [Finset.mem_union,pencil,Finset.mem_filter,Finset.mem_univ,true_and] at hU
    rcases hU with ((e|e)|e)|e
    · exact avoids p (by simp [orig]) e
    · exact avoids q (by simp [orig]) e
    · exact avoids r (by simp [orig]) e
    · exact avoids s (by simp [orig]) e
  have bound := Finset.card_le_univ (missing S ∪ U)
  rw [Finset.card_union_of_disjoint dis] at bound
  change (missing S).card+U.card≤13 at bound
  omega

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
