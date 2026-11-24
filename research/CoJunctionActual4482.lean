import PEqualNP.CoJunctionFixedModel4482
import PEqualNP.CoJunctionStream4482
namespace CoJunctionActual4482
open CoPortRoots4482 CoPortFrontier4482 CoJunctionLogical4482
open CoJunctionFixed4482 CoJunctionTree4482 CoJunctionWire4482
open CoJunctionStream4482

def picture (g : G) (w : W) : List Wire → W
  | [] => 0
  | a::xs => if value a=w then value (rename g a) else picture g w xs

theorem picture_correct (g : G) (w : W) (xs : List Wire) (hw : w∈values xs) :
    picture g w xs = reorder (rowEquiv g) w := by
  induction xs with
  | nil => simp [values] at hw
  | cons a xs ih =>
    change w∈value a::values xs at hw
    by_cases eq : value a=w
    · rw [picture,if_pos eq]
      exact (full_rename g a).trans (congrArg (reorder (rowEquiv g)) eq)
    · rw [picture,if_neg eq]
      exact ih ((List.mem_cons.mp hw).resolve_left (fun h => eq h.symm))

def recordAt (h : Graph) (seeded : Bool) (depth : Nat) (i : Fin h.size) :=
  CoJunctionFixedModel4482.table h seeded depth i.val

def arcsAt (h : Graph) [NeZero h.size] (seeded : Bool) (i : Fin h.size) : List (Fin h.size×G) :=
  (references h i.val).map fun (ref,g) => (Fin.ofNat h.size ref,CoJunctionFixedModel4482.graphView seeded g)

/-- Entire internal-row predicate including the *actual* destination
budgets and *actual* decoded target banks. No external 512-bit input,
target or transporter tables are supplied to this checker. -/
def internal (h : Graph) [NeZero h.size] (seeded : Bool) (depth : Nat) (i : Fin h.size) : Bool :=
  let row := recordAt h seeded depth i
  let xs := CoJunctionFixedModel4482.build h seeded depth i.val
  let frame := (stateWords row).toFinset.card
  stream (recordAt h seeded depth) row (fun g w => picture g w xs)
    (runs row frame (CoJunctionUnique4482.privateRows row.bank)) (arcsAt h seeded i)

theorem internal_sound {h : Graph} [NeZero h.size] {seeded : Bool} {depth : Nat} {i : Fin h.size}
    (accepted : internal h seeded depth i=true) :
    Routed (recordAt h seeded depth) (recordAt h seeded depth i) := by
  let xs := CoJunctionFixedModel4482.build h seeded depth i.val
  have views (g : G) (w : W) (hw : w∈stateWords (recordAt h seeded depth i)) :
      picture g w xs = reorder (rowEquiv g) w := by
    apply picture_correct
    change w∈words (CoJunctionFixedModel4482.data xs) at hw
    rwa [CoJunctionFixedModel4482.data_values] at hw
  exact stream_sound views rfl (fun _ _ => rfl) accepted

#print axioms internal_sound
end CoJunctionActual4482
