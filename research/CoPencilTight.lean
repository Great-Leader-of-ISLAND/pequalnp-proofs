import Mathlib

namespace PhaseTwo.Pencil

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def hit (I : α → β → Prop) (P : Finset α) (L : Finset β) : Prop :=
  ∃ u ∈ P, ∃ l ∈ L, I u l

theorem forget_or (I : α → β → Prop) (p : α)
    (H : Finset α → Finset β → Prop) (K : Prop → Finset α → Finset β → Prop)
    (factor : ∀ (b : Bool) P L, p ∉ P →
      (hit I (if b then insert p P else P) L ↔ K (b = true ∨ H P L) P L))
    {P L} (absent : p ∉ P) (on : H P L) :
    hit I (insert p P) L ↔ hit I P L := by
  have t := factor true P L absent
  have f := factor false P L absent
  simp [on] at t f
  exact t.trans f.symm

theorem blockers (I : α → β → Prop) (p : α) (H : Finset α → Finset β → Prop)
    (up : ∀ P L L', L ⊆ L' → H P L → H P L')
    (forget : ∀ P L, p ∉ P → H P L → (hit I (insert p P) L ↔ hit I P L))
    {P L} (absent : p ∉ P) (on : H P L) (independent : ¬hit I P L) :
    ∀ l, I p l → ∃ u ∈ P, I u l := by
  intro l hp
  have more := up P L (insert l L) (Finset.subset_insert _ _) on
  have pos : hit I (insert p P) (insert l L) :=
    ⟨p, Finset.mem_insert_self _ _, l, Finset.mem_insert_self _ _, hp⟩
  obtain ⟨u, hu, j, hj, inc⟩ := (forget P _ absent more).mp pos
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact ⟨u, hu, inc⟩
  · exact (independent ⟨u,hu,j,hj,inc⟩).elim

theorem pencil_cost [Fintype β] (I : α → β → Prop) [DecidableRel I] (p : α)
    (linear : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)
    (P : Finset α) (absent : p ∉ P)
    (block : ∀ l, I p l → ∃ u ∈ P, I u l) :
    Fintype.card {l : β // I p l} ≤ P.card := by
  classical
  choose f hf using fun x : {l : β // I p l} => block x.val x.property
  let witness : {l : β // I p l} → ↥P := fun x => ⟨f x, (hf x).1⟩
  have inj : Function.Injective witness := by
    intro l j he
    have eq : f l = f j := congrArg Subtype.val he
    have ne : p ≠ f l := fun e => absent (e.symm ▸ (hf l).1)
    obtain ⟨_,_,unique⟩ := linear p (f l) ne
    apply Subtype.ext
    exact (unique _ ⟨l.property,(hf l).2⟩).trans
      (unique _ ⟨j.property, eq.symm ▸ (hf j).2⟩).symm
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective witness inj

theorem whole_line_masks_every_point (I : α → β → Prop) (B : Finset α)
    (blocking : ∀ l, ∃ u ∈ B, I u l) {P : Finset α} (hB : B ⊆ P)
    (extra : Finset α) (L : Finset β) :
    hit I (P ∪ extra) L ↔ hit I P L := by
  constructor
  · rintro ⟨_,_,l,hl,_⟩
    obtain ⟨u,hu,h⟩ := blocking l
    exact ⟨u,hB hu,l,hl,h⟩
  · rintro ⟨u,hu,l,hl,h⟩
    exact ⟨u,Finset.mem_union_left _ hu,l,hl,h⟩

/-- With exactly one witness per line, no secant of the witnessing set contains p. -/
theorem equality_excludes_secants [Fintype β] (I : α → β → Prop) [DecidableRel I] (p : α)
    (linear : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)
    (P : Finset α) (absent : p ∉ P) (tight : Fintype.card {l : β // I p l} = P.card)
    (block : ∀ l, I p l → ∃ u ∈ P, I u l) {u v : α} (hu : u ∈ P) (hv : v ∈ P)
    (uv : u ≠ v) {s : β} (ps : I p s) (us : I u s) (vs : I v s) : False := by
  classical
  have pu : p ≠ u := fun e => absent (e.symm ▸ hu)
  obtain ⟨_, _, unique⟩ := linear p u pu
  have smaller : ∀ l, I p l → ∃ a ∈ P.erase u, I a l := by
    intro l pl
    obtain ⟨a, ha, al⟩ := block l pl
    by_cases au : a = u
    · subst a
      have sl : s = l := (unique _ ⟨ps, us⟩).trans (unique _ ⟨pl, al⟩).symm
      exact ⟨v, Finset.mem_erase.mpr ⟨uv.symm, hv⟩, sl ▸ vs⟩
    · exact ⟨a, Finset.mem_erase.mpr ⟨au, ha⟩, al⟩
  have le := pencil_cost I p linear (P.erase u) (fun h => absent (Finset.mem_of_mem_erase h)) smaller
  rw [tight] at le
  exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hu)) le

end PhaseTwo.Pencil
