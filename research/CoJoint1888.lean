import PEqualNP.CoReaders1888
namespace CoJoint1888
open CoRaw1888 CoEndpoint1888 CoThetaFreeCore CoThetaNine CoReaders1888

private def rows (k : Kind) (sw : Bool) : Row×Row := match k with
  | .conj | .disj => (9,12)
  | .leftOnly => if sw then (9,13) else (20,21)
  | .rightOnly => if sw then (20,21) else (9,13)

private theorem separable (k : Kind) (sw : Bool) :
    let a := raw (rows k sw).1
    let b := raw (rows k sw).2
    CoRaw1888.seed a=CoRaw1888.seed b ∧ target a≠target b ∧ (∀i : Vertex,i≠0 → i≠2 → a i=b i) ∧
    pairCode k sw (a 0) (a 2)=pairCode k sw (b 0) (b 2) := by cases k <;> cases sw <;> decide +kernel

/-- The two indispensable single readers in a fifteen-binary computation must
    be different gates, even when the supplied disjunction is available. -/
theorem no_joint (L : SignedLower) {gs : List (TraceGate Full)} (ok : sufficient roots target gs)
    (small : gs.length≤15) {g : TraceGate Full} (hg : g∈gs) (h0 : reads g (coord 0)) : ¬reads g (coord 2) := by
  intro h2
  have separate : coord 0≠coord 2 := fun e => Bool.false_ne_true (congrFun e (raw 1)).symm
  obtain ⟨sw,desc⟩ := joint_reader_code (coord 0) (coord 2) separate g h0 h2
  let a := raw (rows g.kind sw).1
  let b := raw (rows g.kind sw).2
  obtain ⟨same,away,other,mask⟩ := separable g.kind sw
  have source : agreeOutside (fun w => w=coord 0 ∨ w=coord 2) a b roots := by
    intro w hw skip
    rcases List.mem_cons.mp hw with rfl|hr
    · rfl
    rcases List.mem_cons.mp hr with rfl|hr
    · exact same
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact other i (fun eq => skip (Or.inl (congrArg coord eq))) (fun eq => skip (Or.inr (congrArg coord eq)))
  have clear : ¬(target=coord 0 ∨ target=coord 2) := by
    rintro (e|e) <;> exact Bool.false_ne_true (congrFun e (raw 24)).symm
  obtain ⟨t,ht,tr,mark⟩ := reader_witness (fun w => w=coord 0 ∨ w=coord 2) a b ok.1 source ok.2 clear away
  have eqn : t=g := by
    rcases tr with (r|r)|(r|r)
    · exact unique_reader L ok small false ht hg (Or.inl r) h0
    · exact unique_reader L ok small true ht hg (Or.inl r) h2
    · exact unique_reader L ok small false ht hg (Or.inr r) h0
    · exact unique_reader L ok small true ht hg (Or.inr r) h2
  apply mark
  rw [eqn,desc,desc]
  exact mask

#print axioms CoJoint1888.no_joint
end CoJoint1888
