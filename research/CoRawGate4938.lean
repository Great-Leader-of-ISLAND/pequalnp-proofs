import PEqualNP.CoPrivateCut4938
namespace CoRawGate4938
open CoPrivateCut4938
def blocks : List Nat := [19809470288449884039386497024, 636303902639415047930643513346, 24760020338009232787604767748, 635064752492564383787952148481, 22285348005814882957193651202, 636303902639412796122239895554, 19811876331849064126229779460, 638782198210763404098018512900, 9445891517853681583112, 633826812453279003514126770177, 178264585209397512914590499968, 635064751311971637171707707392, 22285350367290860567078896642, 633828020199661045860121217026, 24763683717267117550071714820, 633830442775826231883435376644, 59430802773922165318750315528, 643738491835107791233093763080, 19884496902087392002557674512, 321139511712058582286352]
def base (i j : Fin 10) (op : Bool) : Nat :=
  let k := 20*i.val+2*j.val+(if op then 1 else 0)
  ((blocks.getD (k/10) 0) >>> (10*(k%10))) % 1024
def merged (op a b : Bool) := if op then a || b else a && b

def check (i j : Fin 10) (op : Bool) : Prop :=
  let a := base i j op
  let b := a ||| 2^i.val
  graph a=false ∧ graph b=true ∧ (a &&& (1023-2^i.val))=(b &&& (1023-2^i.val)) ∧
  merged op (a.testBit i.val) (a.testBit j.val) = merged op (b.testBit i.val) (b.testBit j.val)
instance (i j : Fin 10) (op : Bool) : Decidable (check i j op) := by unfold check; infer_instance
theorem evidence : ∀ (i j : Fin 10) (op : Bool),i ≠ j → check i j op := by decide +kernel

theorem pin_reused (i j : Fin 10) (different : i ≠ j) (op : Bool) :
    ¬ ∃ rest : Nat → Bool → Bool,∀ x : Nat, graph x =
      rest (x &&& (1023-2^i.val)) (merged op (x.testBit i.val) (x.testBit j.val)) := by
  obtain ⟨low,high,raw,port⟩ := evidence i j op different
  rintro ⟨tail,works⟩
  have a := works (base i j op)
  have b := works (base i j op ||| 2^i.val)
  rw [low,raw,port] at a
  rw [high] at b
  rw [←b] at a
  contradiction
#print axioms pin_reused
end CoRawGate4938
