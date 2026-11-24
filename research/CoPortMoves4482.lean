import PEqualNP.CoPortTrace4482
namespace CoPortTrace4482
variable {W : Type} [DecidableEq W]
variable {join : Bool → W → W → W} {stop : Finset W → Prop}

theorem width {cap : Nat} (terminal : ∀ S,stop S → S.card ≤ cap)
    {k S} (p : Path join stop k S) : S.card ≤ cap+k := by
  induction p with
  | final S h => simpa using terminal S h
  | @step k U d a b ne fresh tail ih =>
    have out : join d a b ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem out] at ih
    have t := Finset.card_insert_le a (insert b U)
    have u := Finset.card_insert_le b U
    omega

def discard (S : Finset W) (v : W) (yes : Bool) := if yes then S.erase v else S

theorem rest_shape (U : Finset W) (a b : W) :
    ∃ da db : Bool, discard (discard (insert a (insert b U)) a da) b db = U := by
  refine ⟨decide (a∉U),decide (b∉U),?_⟩
  ext t
  by_cases ha : a∈U <;> by_cases hb : b∈U <;> by_cases ta : t=a <;> by_cases tb : t=b <;>
    simp_all [discard]

theorem transition {k : Nat} {S : Finset W} (path : Path join stop (k+1) S) :
    ∃ d a b da db, a∈S ∧ b∈S ∧ a≠b ∧ join d a b∉S ∧
      Path join stop k (insert (join d a b) (discard (discard S a da) b db)) := by
  cases path with
  | @step _ U d a b ne fresh tail =>
    obtain ⟨da,db,eq⟩ := rest_shape U a b
    exact ⟨d,a,b,da,db,Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      ne,fresh,by rw [eq];exact tail⟩

end CoPortTrace4482
