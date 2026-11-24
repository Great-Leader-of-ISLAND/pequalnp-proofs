import PEqualNP.Co5339Core

namespace Co5339Fiber

noncomputable section
open Classical

/-- The posted high-degree-core assertion entails a lower bound even for circuits with arbitrary clean-edge sets. -/
theorem converse
    (posted : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             have x14 : Set (Fin x2 × Fin x2) := {x14 : Fin x2 × Fin x2 | x3 x14.1 x14.2 ∧ ∃ x15 < x9, x11 (x12 + x15) ⊆ x11 x10 ∧ (x13 x14.1, x13 x14.2) ∈ x11 (x12 + x15) ∧ ∃ (x16 : ℕ) (x17 : ℕ), Max.max x16 x17 < x12 + x15 ∧ x11 (x12 + x15) = x11 x16 ∩ x11 x17 ∧ ∃ (x18 : Set (Fin x2 → Bool)) (x19 : Set (Fin x2 → Bool)), x11 x16 = x18 ×ˢ Set.univ ∧ x11 x17 = Set.univ ×ˢ x19};             x10 < x12 + x9 → (∀ (x16 : Fin x2), x11 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x11 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) → (∀ x17 < x9, ∃ (x19 : ℕ) (x20 : ℕ), Max.max x19 x20 < x12 + x17 ∧ x11 (x12 + x17) ∈ [x11 x19 ∪ x11 x20, x11 x19, ∅, x11 x19 ∩ x11 x20]) → (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x13 x18, x13 x19) ∈ x11 x10) → (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x11 x10) → x14.ncard ≤ (4 : ℕ) * x9 → ∀ (x21 : Finset (Fin x2 × Fin x2)), (∀ (x22 : Fin x2 × Fin x2), x22 ∈ x21 ↔ x3 x22.1 x22.2 ∧ x22 ∉ x14) → ∀ (x23 x24 : Finset (Fin x2)), x23.Nonempty → x24.Nonempty → (∀ x27 ∈ x23, (12 : ℕ) * x1 / (25 : ℕ) < {x29 ∈ x24 | (x27, x29) ∈ x21}.card) → (∀ x28 ∈ x24, (12 : ℕ) * x1 / (25 : ℕ) < {x30 ∈ x23 | (x30, x28) ∈ x21}.card) → x2 * x1 ≤ (100 : ℕ) * x9)
    {q N s o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (large : 100<q) (plane : N=q^2+q+1) (deg : ∀l,Fintype.card {p // I p l}=q+1)
    (joined : ∀p r,p≠r → ∃!l,I p l ∧ I r l)
    (W : ℕ → Set (Input N)) (output : o<N+N+s) (base : Bases W)
    (gates : ∀i<s,LegalAt W (N+N+i)) (pos : positive I (W o)) (neg : correctNegative I q (W o)) :
    N*q≤100*(s+N+q) := by
  classical
  have fits : q<N := by nlinarith
  let Ws := padded q W
  let os := slot N q o
  let ss := q+N+s
  let E : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2
  have valid := pad_gate fits base gates
  have hbase := @pad_base N q W base
  have bound : os<N+N+ss := by
    have z := @slot_lt N q o s (by omega) output
    dsimp [os,ss]; omega
  obtain ⟨hp,hn⟩ := padded_sparse_spec I fits base (by omega) pos neg
  have none : clean I Ws os ss=∅ := no_clean I fits base gates (by omega) hn
  have few : (clean I Ws os ss).ncard≤4*ss := by simp [none]
  have edges : ∀e,e∈E ↔ I e.1 e.2 ∧ e∉clean I Ws os ss := by simp [E,none]
  have nonempty : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  have pdeg : ∀p∈(Finset.univ : Finset (Fin N)),12*q/25 < (Finset.univ.filter fun l => (p,l)∈E).card := by
    intro p _
    have eq : (Finset.univ.filter fun l => (p,l)∈E)=(Finset.univ.filter fun l => I p l) := by ext l; simp [E]
    rw [eq,point_count I (by omega) plane deg joined]
    omega
  have ldeg : ∀l∈(Finset.univ : Finset (Fin N)),12*q/25 < (Finset.univ.filter fun p => (p,l)∈E).card := by
    intro l _
    have eq : (Finset.univ.filter fun p => (p,l)∈E).card = q+1 := by
      simpa [E,Fintype.card_subtype] using deg l
    rw [eq]; omega
  have res := posted q N I large plane deg joined ss os Ws bound hbase valid hp hn few E edges
    Finset.univ Finset.univ nonempty nonempty pdeg ldeg
  dsimp only [ss] at res
  omega

end
end Co5339Fiber
