import PEqualNP.CoPortEdgeRows4482

namespace CoRecipe4482
open CoPortRoots4482 CoPortEdgeRows4482 CoBitBlock4482

/-- A fully computed word together with its mathematical endpoint projection.
The proof fields allow one shared DAG to reconstruct both data columns. -/
structure Entry where
  full : W
  projected : Mark
  correct : projected=mark full
  ordered : Ordered full

def input (i : Fin 9) : Entry :=
  ⟨raw i,basis i,(basis_matches i).symm,raw_order i⟩

def gate (d : Bool) (a b : Entry) : Entry where
  full := join d a.full b.full
  projected :=
    if d then (a.projected.1 ||| b.projected.1,a.projected.2 ||| b.projected.2)
    else (a.projected.1 &&& b.projected.1,a.projected.2 &&& b.projected.2)
  correct := by rw [mark_gate,←a.correct,←b.correct]
  ordered := join_ordered d a.ordered b.ordered

/-- Input tags 0..8 contain no second field. For gate tags 9+2*a+d the
second field is b. Malformed references and missing fields reject decoding. -/
def fromFields : Nat → List Nat → Array Entry → Option (Array Entry × List Nat)
  | 0,fields,entries => some (entries,fields)
  | _+1,[],_ => none
  | n+1,t::fields,entries =>
    if h : t<9 then fromFields n fields (entries.push (input ⟨t,h⟩))
    else match fields with
    | [] => none
    | b::tail =>
      match entries[(t-9)/2]?,entries[b]? with
      | some a,some b =>
        fromFields n tail (entries.push (gate (decide ((t-9)%2=1)) a b))
      | _,_ => none

theorem entry_projection {n fields entries encoded tail}
    (_built : fromFields n fields entries=some (encoded,tail))
    {a : Entry} (_member : a∈encoded) : a.projected=mark a.full ∧ Ordered a.full :=
  ⟨a.correct,a.ordered⟩

#print axioms gate
#print axioms entry_projection
end CoRecipe4482
