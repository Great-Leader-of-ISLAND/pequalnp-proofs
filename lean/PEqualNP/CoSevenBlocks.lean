import Mathlib
import PEqualNP.Outside.L_meta_1461

namespace PEqualNP.Outside.CoSevenBlocks

open PEqualNP.CircuitLowerBounds

/-- The Paley tournament on the seven block labels. -/
private def beats (a b : Fin 7) : Prop :=
  (b.val + 7 - a.val) % 7 = 1 ∨ (b.val + 7 - a.val) % 7 = 2 ∨
    (b.val + 7 - a.val) % 7 = 4

private instance beatsDec (a b : Fin 7) : Decidable (beats a b) := by
  unfold beats
  infer_instance

private theorem beats_asymm : ∀ a b : Fin 7, beats a b → ¬ beats b a := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem common_predecessor : ∀ t : Finset (Fin 7), t.card ≤ 2 →
    ∃ a : Fin 7, ∀ b ∈ t, beats a b := by decide +kernel

/-- Seven trigger sets, of which any row meets at most two, suffice for the
one-inverter lower bound. The trigger sets need not consist of singletons. -/
theorem seven_blocks {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (B : Fin 7 → Finset (Fin n)) (hq : 1 ≤ q) (hm : 1 ≤ m)
    (hsize : ∀ i : Fin m, (S i).card = q+1)
    (hlinear : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hcover : ∀ v : Fin n, ∃ i : Fin m, v ∈ S i)
    (hthin : ∀ i : Fin m,
      (Finset.univ.filter (fun k : Fin 7 => (B k ∩ S i).Nonempty)).card ≤ 2)
    (gates : List Gate) (out : Fin m → ℕ) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hj : (gates.get j).op = GateOp.not)
    (huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i=j)
    (hcalc : ∀ (i : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gates, out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true))
    (htrigger : ∀ (k : Fin 7) (U : Finset (Fin n)), B k ⊆ U →
      Circuit.eval ⟨gates, n+(j : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∈ U))) = false) :
    m*q + (Finset.univ.filter (fun i : Fin gates.length =>
      j < i ∧ n+(j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  classical
  let touched (i : Fin m) := Finset.univ.filter (fun k : Fin 7 => (B k ∩ S i).Nonempty)
  have hchoose : ∀ i : Fin m, ∃ a : Fin 7, ∀ b ∈ touched i, beats a b :=
    fun i => common_predecessor (touched i) (hthin i)
  choose f hf using hchoose
  have miss : ∀ i, Disjoint (B (f i)) (S i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro p hp hline
    have hh : f i ∈ touched i := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, p, Finset.mem_inter.mpr ⟨hp, hline⟩⟩
    exact beats_asymm _ _ (hf i _ hh) (hf i _ hh)
  let R (i : Fin m) (p : Fin n) := insert p (B (f i))
  have hlocal : ∀ (i : Fin m) (p : Fin n), p ∈ S i → R i p ∩ S i = {p} := by
    intro i p hp
    ext z
    constructor
    · intro hz
      obtain ⟨hzr, hzs⟩ := Finset.mem_inter.mp hz
      rcases Finset.mem_insert.mp hzr with he | hb
      · exact Finset.mem_singleton.mpr he
      · exact (Finset.disjoint_left.mp (miss i) hb hzs).elim
    · intro hz
      obtain rfl := Finset.mem_singleton.mp hz
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hp⟩
  have arrow : ∀ (i l : Fin m), (∃ p ∈ S i \ S l, (R i p ∩ S l).Nonempty) →
      beats (f l) (f i) := by
    rintro i l ⟨p, hp, z, hz⟩
    obtain ⟨hzr, hzl⟩ := Finset.mem_inter.mp hz
    have hb : z ∈ B (f i) := by
      rcases Finset.mem_insert.mp hzr with he | hb
      · subst z
        exact ((Finset.mem_sdiff.mp hp).2 hzl).elim
      · exact hb
    apply hf l (f i)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, Finset.mem_inter.mpr ⟨hb, hzl⟩⟩
  apply PEqualNP.Outside.L_meta_1461 q n m S R hq hm hsize hlinear hcover hlocal
    (fun i l _ h => beats_asymm _ _ (arrow i l h.1) (arrow l i h.2)) gates out j hg hj huniq hcalc
  · intro i
    have hs : B (f i) ⊆ Finset.univ \ S i := by
      intro p hp
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp (miss i) hp⟩
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and] using htrigger (f i) _ hs
  · intro i p _
    exact htrigger (f i) (R i p) (fun _ h => Finset.mem_insert_of_mem h)

end PEqualNP.Outside.CoSevenBlocks
