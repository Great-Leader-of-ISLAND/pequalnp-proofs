import PEqualNP.CoRedundantOr
import PEqualNP.CoPetersenPrefix

namespace PEqualNP.Research.OriginalOr
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1672.Main1672

def first : Gate := ⟨.and,[0,1]⟩
def second (pins : List (Fin 11)) : Gate := ⟨.or,pins.map Fin.val⟩
def afterFirst := raw ++ [gv raw first]

def skip (pins : List (Fin 11)) : Bool :=
  let z := gv afterFirst (second pins)
  decide (z ∈ afterFirst ∨ z = zero ∨ z = one)

def lists : List (List (Fin 11)) :=
  [] :: ((List.finRange 11).map (fun i => [i]) ++ (List.finRange 11).flatMap
    (fun i => (List.finRange 11).map (fun j => [i,j])))

set_option maxRecDepth 8000 in
theorem count : (lists.filter skip).length = 47 := by decide +kernel

theorem bound (pins : List (Fin 11)) (hp : pins.length ≤ 2) (hskip : skip pins = true)
    (D : Circuit) (fan : FanInTwo D)
    (he : ∀ x : Fin 9 → Bool,
      let w := List.ofFn x ++ [x 0 && x 1]
      D.eval (w ++ [GateOp.or.eval (pins.map (fun i => w.getD i.val false))]) = edgeF x) :
    14 ≤ D.size := by
  let C := Circuit.mk (first :: second pins :: D.gates) D.output
  have legal : FanInTwo C := by
    intro g hg
    change g ∈ first :: second pins :: D.gates at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [first]
    rcases List.mem_cons.mp hg with rfl | hg
    · simpa [second] using hp
    · exact fan _ hg
  have firstVal (x : Fin 9 → Bool) : (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 1) := by
    change ((Circuit.mk (first :: second pins :: D.gates) D.output).wires _).getD 9 false = _
    rw [PetersenPrefix.firstValue]
    simp [first,GateOp.eval,List.getD_eq_getElem?_getD]
  have functions (x : Fin 9 → Bool) : C.eval (List.ofFn x) = edgeF x := by
    have h := PetersenPrefix.semanticTail first (second pins :: D.gates) D.output x (x 0 && x 1) (firstVal x)
    refine h.trans ?_
    simpa only [Circuit.eval,Circuit.wires,List.foldl_cons,second,List.map_map,Function.comp_def] using he x
  apply RedundantOr.lower first (second pins) D legal functions
  have test : gv afterFirst (second pins) ∈ afterFirst ∨ gv afterFirst (second pins) = zero ∨
      gv afterFirst (second pins) = one := of_decide_eq_true hskip
  rcases test with r | z | o
  · exact Or.inl r
  · exact Or.inr (fun h => h.2.1 z)
  · exact Or.inr (fun h => h.2.2 o)

end PEqualNP.Research.OriginalOr
