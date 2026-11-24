import PEqualNP.Outside.L_meta_1672

namespace PEqualNP.Research.TwoCofactor
open PEqualNP.Outside.L_meta_1672.Main1672

/-- A 13-gate continuation cannot simultaneously use two initial signals
that vanish on deletion of a degree-three vertex, if every remaining initial
signal is an original projection on this restricted input. -/
theorem lower {k t : Nat} {S : Finset Sig} (i : Fin 9)
    (hi : ¬ (i.val = 4 ∨ i.val = 6 ∨ i.val = 7))
    (l : Live k t S) (x y : Sig) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y)
    (xz : (homProject i).fn x = zero) (yz : (homProject i).fn y = zero)
    (sub : ∀ a ∈ S, ∃ b ∈ raw, (homProject i).fn a = (homProject i).fn b) : 14 ≤ k := by
  obtain ⟨q,hq,hh⟩ := feasible_two_consts l (homProject i) x y hx hy hne
    (fun hp => hp.2.1 xz) (fun hp => hp.2.1 yz)
  have img : S.image (homProject i).fn ⊆ raw.toFinset.image (homProject i).fn := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b,hb,eq⟩ := sub a ha
    exact eq ▸ Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hb)
  by_contra h
  exact root_project_deg3 i hi (feasible_mono (feasible_subset hh img) (by omega))

/-- For the assigned first AND on 0 and 3 and second OR on 0 and j, setting
input 0 to false collapses both new signals to original input signals. -/
theorem anchor (j : Fin 9) {k t : Nat} {S : Finset Sig} (l : Live k t S)
    (hx : raw0 ∈ S) (ha : bin false raw0 raw3 ∈ S)
    (hs : ∀ a ∈ S, a ∈ raw ++ [bin false raw0 raw3,bin true raw0 (raw.getD j.val zero)]) : 14 ≤ k := by
  let H := homProject 0
  have hz : H.fn raw0 = zero := project_raw_zero 0
  have hx3 : Valid raw3 := raw_valid _ (by simp [raw])
  have hj : raw.getD j.val zero ∈ raw := by
    rw [← raw_id]
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  have vj := raw_valid _ hj
  have eA : H.fn (bin false raw0 raw3) = zero := by
    rw [H.hbin,hz,bin_comm]; exact (bin_laws (H.valid raw3)).2.2.1
  have eO : H.fn (bin true raw0 (raw.getD j.val zero)) = H.fn (raw.getD j.val zero) := by
    rw [H.hbin,hz,bin_comm]; exact (bin_laws (H.valid (raw.getD j.val zero))).2.1
  apply lower 0 (by decide) l raw0 (bin false raw0 raw3) hx ha (by decide +kernel) hz eA
  intro z hm
  rcases List.mem_append.mp (hs z hm) with hr | extras
  · exact ⟨z,hr,rfl⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at extras
    rcases extras with rfl | rfl
    · exact ⟨raw0,by simp [raw],eA.trans hz.symm⟩
    · exact ⟨_,hj,eO⟩

end PEqualNP.Research.TwoCofactor
