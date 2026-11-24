import PEqualNP.CoAO3143Physical
import PEqualNP.CoPetersen2598Prior

namespace CoAO3143Restriction.Physical
/-- The coordinate table is an isomorphism onto the eight-vertex restriction
    of the public nine-vertex Petersen snapshot with vertex 7 removed. -/
def ordinaryMap : Fin 8→Nat := ![2,1,0,5,3,6,4,8]
def ordinaryCube (r : Prior1667.Row) (i : Fin 8) : Bool :=
  Prior1667.bit r (Prior1667.inputs.getD (ordinaryMap i) Prior1667.zero)

private theorem buildReach {α : Type} {initial ws : List (Wire α)} {n : Nat} (run : Build initial n ws)
    (f : Prior1667.Row → α) (raw : List (Wire Prior1667.Row))
    (src : ∀ w∈initial, Prior1667.Available raw (cut f w)) :
    ∃ zs, Prior1667.Reach raw n zs ∧ ∀ w∈ws,Prior1667.Available zs (cut f w) := by
  induction run with
  | start => exact ⟨raw,Prior1667.Reach.start,src⟩
  | @gate n ws pre d a b ha hb ih =>
    obtain ⟨xs,build,holds⟩ := ih
    have newBuild := Prior1667.Reach.two d build (holds a ha) (holds b hb)
    refine ⟨_,newBuild,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | old
    · left
      have eq : cut f (op d a b)=Prior1667.combine d (cut f a) (cut f b) := by cases d <;> rfl
      rw [eq]
      exact List.mem_cons_self
    · rcases holds w old with h | constant
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr constant

set_option maxRecDepth 8192 in
theorem ordinary_price : OrdinaryPrice := by
  intro n ws build hit
  have mapped : ∀ i : Fin 8, Prior1667.inputs.getD (ordinaryMap i) Prior1667.zero ∈
      Prior1667.vars 383 := by decide +kernel
  have source : ∀ w∈positiveRoots,
      Prior1667.Available ((Prior1667.vars 383).map Prior1667.observe) (cut ordinaryCube w) := by
    intro w hw
    rcases List.mem_append.mp hw with idx | c
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp idx
      exact Or.inl (List.mem_map_of_mem (mapped i))
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at c
      rcases c with rfl | rfl
      · exact Or.inr ⟨true,rfl⟩
      · exact Or.inr ⟨false,rfl⟩
  have exactGoal : cut ordinaryCube CoAO3143.f8=Prior1667.observe (Prior1667.graphGoal 383) := by
    funext r
    exact (show ∀ i : Prior1667.Row, CoAO3143.f8 (ordinaryCube i)=
      Prior1667.observe (Prior1667.graphGoal 383) i by decide +kernel) r
  obtain ⟨bank,real,word⟩ := buildReach build ordinaryCube _ source
  have yes := word _ hit
  rw [exactGoal] at yes
  exact Prior1667.low383 n bank real yes

end CoAO3143Restriction.Physical
