import PEqualNP.Outside.L_meta_1672

namespace PEqualNP.Research.RedundantOr
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1672.Main1672

/-- If the second gate only repeats an available signal, or is constant on
the paired rows, every realization of the Petersen function still needs 14
gates after that second gate. The first gate is completely arbitrary. -/
theorem lower (g q : Gate) (D : Circuit)
    (fan : FanInTwo (Circuit.mk (g :: q :: D.gates) D.output))
    (computes : ∀ x : Fin 9 → Bool,
      (Circuit.mk (g :: q :: D.gates) D.output).eval (List.ofFn x) = edgeF x)
    (redundant : represented (raw ++ [gv raw g]) (gv (raw ++ [gv raw g]) q)) :
    14 ≤ D.size := by
  let w := raw ++ [gv raw g]
  let z := gv w q
  have vw : ∀ a ∈ w, Valid a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact raw_valid a ha
    · obtain rfl := List.mem_singleton.mp ha
      exact gv_valid raw_valid _
  have vz : ∀ a ∈ w ++ [z], Valid a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact vw a ha
    · obtain rfl := List.mem_singleton.mp ha
      exact gv_valid vw _
  have endTarget : target ∈ execute D.gates (w ++ [z]) :=
    circuit_target ⟨g :: q :: D.gates, D.output⟩ fan computes
  obtain ⟨k,t,S,hk,hl,hs⟩ := extract D.gates (w ++ [z]) vz
    (fun a ha => fan a (by change a ∈ g :: q :: D.gates; simp [ha])) endTarget
  have hs' : ∀ a ∈ S, a ∈ w := by
    intro a ha
    rcases List.mem_append.mp (hs a ha) with hw | hz
    · exact hw
    · obtain rfl := List.mem_singleton.mp hz
      exact redundant.resolve_right (fun hn => hn (live_proper hl _ ha))
  obtain ⟨j,u,T,hj,hL,hT⟩ := pull_gate hl
    (gate_rep raw_valid g (fan g (by change g ∈ g :: q :: D.gates; simp))) hs'
  have e := necessary hL hT
  subst T
  by_contra h
  change ¬ 14 ≤ D.gates.length at h
  have hj14 : j ≤ 14 := by omega
  have sz := live_size hL
  rw [List.toFinset_card_of_nodup raw_nd] at sz
  have hlen : raw.length = 9 := rfl
  exact rootImpossible u (by omega) j hj14 raw.toFinset rootTag rootWires_rep
    (restrict_live hL (rootTag_ok hj14))

end PEqualNP.Research.RedundantOr
