import PEqualNP.CoFalseCode
namespace PEqualNP.Research.PlanePacking
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_1778

theorem exterior {q N} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card=q+1)
    (uniq : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (T : Finset (Fin N)) (small : T.card≤q) (l : Fin N) (notin : l∉T) :
    ∃ p, I p l ∧ ∀ k∈T, ¬I p k := by
  classical
  by_contra! closed
  have hit (p : {p // I p l}) : ∃ k : T, I p.val k.val := by
    obtain ⟨k,hk,on⟩ := closed p.val p.property
    exact ⟨⟨k,hk⟩,on⟩
  choose f hf using hit
  have inj : Function.Injective f := by
    intro p r eq
    by_contra ne
    have dist : p.val ≠ r.val := fun h => ne (Subtype.ext h)
    obtain ⟨j,hj,only⟩ := uniq _ _ dist
    have h₁ := only l ⟨p.property,r.property⟩
    have h₂ := only (f p).val ⟨hf p,by simpa only [eq] using hf r⟩
    exact notin ((h₂.trans h₁.symm) ▸ (f p).property)
  have count := Fintype.card_le_of_injective f inj
  rw [Fintype.card_subtype,lines] at count
  have cardT : Fintype.card T = T.card := Fintype.card_coe _
  omega

def vec {N : Nat} (I : Fin N→Fin N→Prop) [DecidableRel I] (T : Finset (Fin N)) :
    Fin (N+N) → Bool :=
  Fin.addCases (fun p => decide (∀ k∈T, ¬I p k)) (fun l => decide (l∈T))

theorem packing {q N} (I : Fin N→Fin N→Prop) [DecidableRel I] (C : Circuit) (mono : Monotone2 C)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card=q+1)
    (uniq : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (pos : ∀ p l, I p l → circuitFun (N+N) C (fun k => decide (k=Fin.castAdd N p ∨ k=Fin.natAdd N l))=true)
    (neg : ∀ x : Fin (N+N)→Bool, (Finset.univ.filter (fun l => x (Fin.natAdd N l)=true)).card≤q →
      (¬∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → circuitFun (N+N) C x=false) :
    Fintype.card {T : Finset (Fin N) // T.card≤q} ≤ 2 ^ FalseCode.countA C.gates := by
  classical
  apply FalseCode.packing C mono (fun T : {s : Finset (Fin N) // s.card≤q} => vec I T.val)
  · intro T
    apply neg
    · have setEq : (Finset.univ.filter (fun l : Fin N => vec I T.val (Fin.natAdd N l)=true))=T.val := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, vec, Fin.addCases_right, decide_eq_true_eq]
      rw [setEq]
      exact T.property
    · rintro ⟨p,l,on,hp,hl⟩
      simp only [vec, Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at hp hl
      exact hp l hl on
  · intro S T ne
    have key (A B : Finset (Fin N)) (small : A.card≤q) (l : Fin N) (hn : l∉A) (hl : l∈B) :
        circuitFun (N+N) C (fun i => vec I A i || vec I B i)=true := by
      obtain ⟨p,on,off⟩ := exterior I lines uniq A small l hn
      apply cf_mono (N+N) C mono _ _ _ (pos p l on)
      intro i hi
      simp only [decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · simp only [vec, Fin.addCases_left, Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl off
      · simp only [vec, Fin.addCases_right, Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inr hl
    by_cases h : S.val ⊆ T.val
    · have notsub : ¬T.val ⊆ S.val := fun other => ne (Subtype.ext (Finset.Subset.antisymm h other))
      obtain ⟨l,hl,hn⟩ := Finset.not_subset.mp notsub
      exact key S.val T.val S.property l hn hl
    · obtain ⟨l,hl,hn⟩ := Finset.not_subset.mp h
      simpa only [Bool.or_comm] using key T.val S.val T.property l hn hl
end PEqualNP.Research.PlanePacking
