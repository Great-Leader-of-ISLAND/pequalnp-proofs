import PEqualNP.CoPortTrace4482

namespace CoPortTrace4482
variable {W V : Type} [DecidableEq W] [DecidableEq V]

theorem transport {join : Bool → W → W → W} {join' : Bool → V → V → V}
    {stop : Finset W → Prop} {stop' : Finset V → Prop} (f : W → V)
    (inj : Function.Injective f) (op : ∀ d a b,f (join d a b)=join' d (f a) (f b))
    (terminal : ∀ S,stop S → stop' (S.image f))
    {k S} (p : Path join stop k S) : Path join' stop' k (S.image f) := by
  induction p with
  | final S h => exact Path.final _ (terminal S h)
  | @step k U d a b ne fresh tail ih =>
    have strict : join' d (f a) (f b) ∉ (insert a (insert b U)).image f := by
      intro h
      obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp h
      exact fresh (inj (eq.trans (op d a b).symm) ▸ hw)
    simp only [Finset.image_insert,op] at ih strict ⊢
    exact Path.step d (f a) (f b) (fun e => ne (inj e)) strict ih

end CoPortTrace4482
