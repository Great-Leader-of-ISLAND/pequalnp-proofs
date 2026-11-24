import PEqualNP.CoRecipe4482
import PEqualNP.CoPortCheckMove4482
namespace CoRecipeOrbit4482
open CoPortRoots4482 CoPortFrontier4482

/-- Each recipe produces ordinary values and all graph-transformed values from
the same input/gate code. The view does not evaluate a 512-entry row shuffle. -/
structure Orbit where
  base : CoRecipe4482.Entry
  view : G → W
  correct : ∀ g, view g = reorder (rowEquiv g) base.full

def rawWord (i : Fin 9) : Orbit where
  base := CoRecipe4482.input i
  view := fun g => raw (coordinate g i)
  correct := fun g => (raw_reordered g i).symm

def gateWord (d : Bool) (a b : Orbit) : Orbit where
  base := CoRecipe4482.gate d a.base b.base
  view := fun g => join d (a.view g) (b.view g)
  correct := by
    intro g
    change join d (a.view g) (b.view g) = reorder (rowEquiv g) (join d a.base.full b.base.full)
    rw [a.correct g,b.correct g,reorder_join]

def payload (a : Orbit) : Entry := (a.base.full,a.base.projected)
def record (xs : List Orbit) := xs.map payload

theorem real (xs : List Orbit) : authentic (record xs) := by
  intro e he
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
  exact a.base.correct

theorem increasing (xs : List Orbit) {w : W} (m : w∈words (record xs)) :
    CoPortEdgeRows4482.Ordered w := by
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp m
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
  exact a.base.ordered

/-- Lookup by full value is used in the transparent scanner. Backreferences
are also free to retrieve the same view by position. Both representations
keep the costly finite permutation only in the generic proof. -/
def lookup (g : G) (w : W) : List Orbit → W
  | [] => 0
  | a::xs => if a.base.full=w then a.view g else lookup g w xs

theorem lookup_correct (g : G) (w : W) (xs : List Orbit) (m : w∈words (record xs)) :
    lookup g w xs = reorder (rowEquiv g) w := by
  induction xs with
  | nil => simp [words,record] at m
  | cons a xs ih =>
    change w ∈ a.base.full :: words (record xs) at m
    by_cases eq : a.base.full=w
    · rw [lookup,if_pos eq,a.correct g,eq]
    · simp only [lookup,if_neg eq]
      exact ih ((List.mem_cons.mp m).resolve_left (fun h => eq h.symm))

/-- Raw tags and topological references use the same portable field format
as CoRecipe4482.fromFields. Out-of-range gate references are rejected. -/
def fromFields : Nat → List Nat → Array Orbit → Option (Array Orbit × List Nat)
  | 0,fields,entries => some (entries,fields)
  | _+1,[],_ => none
  | n+1,t::fields,entries =>
    if h : t<9 then fromFields n fields (entries.push (rawWord ⟨t,h⟩)) else
      match fields with
      | [] => none
      | b::tail =>
        match entries[(t-9)/2]?,entries[b]? with
        | some a,some b =>
          fromFields n tail (entries.push (gateWord (decide ((t-9)%2=1)) a b))
        | _,_ => none

#print axioms gateWord
#print axioms lookup_correct
end CoRecipeOrbit4482
