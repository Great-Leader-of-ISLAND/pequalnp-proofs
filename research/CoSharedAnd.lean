import PEqualNP.CoTwoCofactor

namespace PEqualNP.Research.SharedAnd
open PEqualNP.Outside.L_meta_1672.Main1672

private lemma one_new {k t : Nat} {S : Finset Sig} (l : Live k t S) (hk : k ≤ 13)
    (z : Sig) (hz : represented raw z ∨ witness raw z)
    (sub : ∀ a ∈ S, a ∈ raw ++ [z]) : False := by
  obtain ⟨j,u,T,hj,hL,hT⟩ := pull_gate l hz sub
  have e := necessary hL hT
  subst T
  have hj14 : j ≤ 14 := by omega
  have sz := live_size hL
  rw [List.toFinset_card_of_nodup raw_nd] at sz
  have hlen : raw.length = 9 := rfl
  exact rootImpossible u (by omega) j hj14 raw.toFinset rootTag rootWires_rep
    (restrict_live hL (rootTag_ok hj14))

theorem two_constant_signals {k t : Nat} {S : Finset Sig} (i : Fin 9)
    (hi : ¬(i.val = 4 ∨ i.val = 6 ∨ i.val = 7)) (l : Live k t S)
    (a b : Sig) (ga : represented raw a ∨ witness raw a)
    (gb : represented raw b ∨ witness raw b)
    (za : ¬proper ((homProject i).fn a)) (zb : ¬proper ((homProject i).fn b))
    (hs : ∀ c ∈ S, c ∈ raw ++ [a,b]) : 14 ≤ k := by
  by_contra hn
  have hk : k ≤ 13 := by omega
  have pool (c : Sig) (hc : c ∈ S) : c ∈ raw ∨ c = a ∨ c = b := by simpa using hs c hc
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · by_cases ab : a = b
      · subst b
        exact one_new l hk a ga (fun c hc => by simpa using pool c hc)
      · obtain ⟨q,hq,m,hm,t',T,l',subset⟩ := feasible_two_consts l (homProject i) a b ha hb ab za zb
        apply root_project_deg3 i hi
        refine ⟨m,by omega,t',T,l',?_⟩
        intro v hv
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp (subset hv)
        rcases pool c hc with hr | rfl | rfl
        · exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hr)
        · exact (za (live_proper l' _ hv)).elim
        · exact (zb (live_proper l' _ hv)).elim
    · apply one_new l hk a ga
      intro c hc
      rcases pool c hc with hr | rfl | rfl
      · exact List.mem_append_left _ hr
      · simp
      · exact (hb hc).elim
  · apply one_new l hk b gb
    intro c hc
    rcases pool c hc with hr | rfl | rfl
    · exact List.mem_append_left _ hr
    · exact (ha hc).elim
    · simp

theorem and_pair {k t : Nat} {S : Finset Sig} (i : Fin 9)
    (hi : ¬(i.val = 4 ∨ i.val = 6 ∨ i.val = 7)) (l : Live k t S)
    (a b : Sig) (ha : a ∈ raw) (hb : b ∈ raw)
    (hs : ∀ c ∈ S, c ∈ raw ++ [bin false (raw.getD i.val zero) a,bin false (raw.getD i.val zero) b]) :
    14 ≤ k := by
  have hr : raw.getD i.val zero ∈ raw := by
    rw [← raw_id]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have gate (d : Sig) (hd : d ∈ raw) := bin_rep false (raw_valid _ hr) (raw_valid _ hd)
    (Or.inl hr : represented raw _) (Or.inl hd : represented raw _)
  have collapse (d : Sig) : (homProject i).fn (bin false (raw.getD i.val zero) d) = zero := by
    rw [(homProject i).hbin, project_raw_zero, bin_comm]
    exact (bin_laws ((homProject i).valid d)).2.2.1
  exact two_constant_signals i hi l _ _ (gate a ha) (gate b hb)
    (fun hp => hp.2.1 (collapse _)) (fun hp => hp.2.1 (collapse _)) hs

theorem and_then_invert {k t : Nat} {S : Finset Sig} (i : Fin 9)
    (hi : ¬(i.val = 4 ∨ i.val = 6 ∨ i.val = 7)) (l : Live k t S)
    (a : Sig) (ha : a ∈ raw)
    (hs : ∀ c ∈ S, c ∈ raw ++ [bin false (raw.getD i.val zero) a,neg (raw.getD i.val zero)]) :
    14 ≤ k := by
  let x := raw.getD i.val zero
  have hr : x ∈ raw := by
    change raw.getD i.val zero ∈ raw
    rw [← raw_id]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have gz : (homProject i).fn x = zero := project_raw_zero i
  have meet := bin_rep false (raw_valid _ hr) (raw_valid _ ha)
    (Or.inl hr : represented raw _) (Or.inl ha : represented raw _)
  apply two_constant_signals i hi l _ _ meet (neg_rep raw (raw_valid _ hr) hr) _ _ hs
  · intro hp
    apply hp.2.1
    rw [(homProject i).hbin, gz, bin_comm]
    exact (bin_laws ((homProject i).valid a)).2.2.1
  · intro hp
    apply hp.2.2
    rw [(homProject i).hneg (raw_valid _ hr),gz]
    exact neg_laws.1

end PEqualNP.Research.SharedAnd
