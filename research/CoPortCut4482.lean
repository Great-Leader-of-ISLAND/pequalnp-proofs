import PEqualNP.CoPortBank4482

namespace CoPortCut4482
open CoPortBank4482 CoPortTrace4482 PEqualNP.CircuitLowerBounds

variable {W X : Type} [DecidableEq W]

theorem avoid {join : Bool → W → W → W} {stop : Finset W → Prop} {c : W}
    (dead : ∀ d a b, a=c ∨ b=c → join d a b=a ∨ join d a b=b)
    (atEnd : ∀ S, stop S → c∉S) {k S} (p : Path join stop k S) : c∉S := by
  induction p with
  | final S h => exact atEnd S h
  | @step k U d a b ne fresh tail ih =>
    intro hc
    rcases Finset.mem_insert.mp hc with same|rest
    · rcases dead d a b (Or.inl same.symm) with ea|eb
      · exact fresh (ea.symm ▸ Finset.mem_insert_self _ _)
      · exact fresh (eb.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    · rcases Finset.mem_insert.mp rest with same|old
      · rcases dead d a b (Or.inr same.symm) with ea|eb
        · exact fresh (ea.symm ▸ Finset.mem_insert_self _ _)
        · exact fresh (eb.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      · exact ih (Finset.mem_insert_of_mem old)

def cleanCut (M : Model W X) (label : X → Bool) (limit : Nat) (S : Finset W) : Prop :=
  S.card≤limit ∧ Distinguishes M.val label S ∧ M.zero∉S ∧ M.one∉S

theorem observation {M : Model W X} (label : X → Bool) (limit : Nat)
    {n : Nat} {root last : Finset W} (history : Bank M.join root n last)
    (idem : ∀ d a, M.join d a a=a) (word : Nat → W) (O : Finset Nat)
    (cap : O.card≤limit) (sound : ∀ i∈O, word i∈last)
    (detect : ∀ x y, label x ≠ label y → ∃ i∈O, M.val (word i) x ≠ M.val (word i) y) :
    ∃ j ≤ n, ∃ A ⊆ root, Path M.join (cleanCut M label limit) j A := by
  let S := (O.image word).filter fun w => w≠M.zero ∧ w≠M.one
  have sub : S⊆last := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hw).1
    exact sound i hi
  have card : S.card≤limit := (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans cap)
  have dist : Distinguishes M.val label S := by
    intro x y ne
    obtain ⟨i,hi,d⟩ := detect x y ne
    have h0 : word i ≠ M.zero := by
      intro e
      exact d (by rw [e,M.atZero,M.atZero])
    have h1 : word i ≠ M.one := by
      intro e
      exact d (by rw [e,M.atOne,M.atOne])
    exact ⟨word i,Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hi,h0,h1⟩,d⟩
  have stop : cleanCut M label limit S :=
    ⟨card,dist,fun h => (Finset.mem_filter.mp h).2.1 rfl,fun h => (Finset.mem_filter.mp h).2.2 rfl⟩
  simpa only [Nat.add_zero] using pull idem history sub (Path.final S stop)

end CoPortCut4482
