import PEqualNP.Co4358TinyModel

namespace CoNum4358.Tiny
open CoAO3143

private noncomputable def preimageWire (z : AugWire) : W := by
  classical
  exact if h : ∃ w : W, lift w=z then h.choose else default

private theorem preimage_lift (w : W) : preimageWire (lift w)=w := by
  classical
  unfold preimageWire
  rw [dif_pos (show ∃ v : W,lift v=lift w from ⟨w,rfl⟩)]
  apply lift_inj
  exact Classical.choose_spec _

private theorem lift_preimage {z : AugWire} (hz : ∃ w : W,lift w=z) :
    lift (preimageWire z)=z := by
  obtain ⟨w,rfl⟩ := hz
  rw [preimage_lift]

private theorem original_fringe {S : Finset AugWire}
    (rep : ∀ z∈S,∃ w : W,lift w=z) :
    (S.image preimageWire).image (fun w => wide w.1) = S.image Prod.fst := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro z hz
  exact congrArg Prod.fst (lift_preimage (rep z hz))

private theorem small_good {k S} (fact : Local k S)
    (rep : ∀ z∈S,∃ w : W,lift w=z) : Good k (S.image preimageWire) := by
  constructor
  · rw [original_fringe rep]
    exact fact.live
  · intro s
    obtain ⟨z,hz,flag⟩ := fact.caps s
    refine ⟨preimageWire z,Finset.mem_image_of_mem _ hz,?_⟩
    have bits : (preimageWire z).2 = z.2 := congrArg Prod.snd (lift_preimage (rep z hz))
    rwa [bits]

private theorem trace_of_shadow {k q S} (run : Shadow k q S) :
    (∀ z∈S,∃ w : W,lift w=z) → Trace k q (S.image preimageWire) := by
  classical
  induction run with
  | done q z orig sep₀ sep₃ =>
    intro rep
    obtain ⟨x,rfl⟩ := rep z (by simp)
    rw [Finset.image_singleton,preimage_lift]
    exact Trace.done q x (wide_inj (orig.trans target_value.symm)) sep₀ sep₃
  | @step k q U d a b apart bd clean unused noraw facts child ih =>
    intro rep
    obtain ⟨x,rfl⟩ := rep a (by simp)
    obtain ⟨y,rfl⟩ := rep b (by simp)
    have related := lift_make d x y
    have computed : wide (make d x y).1=(augGate d (lift x) (lift y)).1 :=
      congrArg Prod.fst related
    have next := ih (by
      intro z hz
      rcases Finset.mem_insert.mp hz with eq | mem
      · exact ⟨make d x y,related.trans eq.symm⟩
      · exact rep z (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem)))
    rw [Finset.image_insert,←related,preimage_lift,←charge_eq] at next
    have localSmall := small_good facts rep
    simp only [Finset.image_insert,preimage_lift] at localSmall ⊢
    apply Trace.step d x y (fun h => apart (congrArg lift h))
      (by simpa only [charge_eq] using bd) _ _ _ localSmall next
    · constructor
      · intro e
        exact clean.1 (computed.symm.trans ((congrArg wide e).trans zero_value))
      · intro e
        exact clean.2 (computed.symm.trans ((congrArg wide e).trans one_value))
    · intro bad
      obtain ⟨v,hv,he⟩ := Finset.mem_image.mp bad
      have inMap : v∈(insert (lift x) (insert (lift y) U)).image preimageWire := by
        simpa only [Finset.image_insert,preimage_lift] using hv
      obtain ⟨z,hz,eq⟩ := Finset.mem_image.mp inMap
      have e : wide (preimageWire z).1=z.1 := congrArg Prod.fst (lift_preimage (rep z hz))
      rw [eq,he] at e
      exact unused (Finset.mem_image.mpr ⟨z,hz,e.symm.trans computed⟩)
    · intro bad
      have mem : wide (make d x y).1∈bare.map wide := List.mem_map.mpr ⟨_,bad,rfl⟩
      rw [bare_ground,computed] at mem
      exact noraw mem

theorem shadow_to_tiny (run : Shadow 11 1 augRoots.toFinset) :
    Trace 11 1 roots.toFinset := by
  classical
  have eq : augRoots.toFinset=roots.toFinset.image lift := by
    rw [←ground]
    ext z
    simp
  have rep (z) (hz : z∈augRoots.toFinset) : ∃ w : W,lift w=z := by
    rw [eq] at hz
    obtain ⟨w,_,e⟩ := Finset.mem_image.mp hz
    exact ⟨w,e⟩
  have back : augRoots.toFinset.image preimageWire=roots.toFinset := by
    rw [eq,Finset.image_image]
    ext w
    simp [Function.comp_def,preimage_lift]
  simpa only [back] using trace_of_shadow run rep

end CoNum4358.Tiny
