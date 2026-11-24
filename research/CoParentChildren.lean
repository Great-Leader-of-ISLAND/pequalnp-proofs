import PEqualNP.CoPetersenPrefix
import PEqualNP.Outside.L_meta_1667

namespace PEqualNP.Research.ParentChildren
open CircuitLowerBounds MetaComplexity
open PEqualNP.Outside.L_meta_1667 (edge)

def w (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 1]

theorem child (op : GateOp) (pins : List Nat)
    (legalOp : op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) (short : pins.length ≤ 2)
    (D : Circuit) (fan : FanInTwo D) (small : D.size ≤ 13) :
    ∃ x : Fin 9 → Bool, D.eval (w x ++ [op.eval (pins.map fun j => (w x).getD j false)]) ≠ edge x := by
  by_contra! realizes
  let a : Gate := ⟨.and,[0,1]⟩
  let b : Gate := ⟨op,pins⟩
  let C : Circuit := ⟨a :: b :: D.gates, D.output⟩
  have legal : FanInTwo C := by
    intro g hg
    change g ∈ a :: b :: D.gates at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [a]
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨legalOp,short⟩
    exact fan g hg
  have first (x : Fin 9 → Bool) : (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 1) := by
    change (Circuit.wires ⟨a :: b :: D.gates,D.output⟩ _).getD 9 false = _
    rw [PetersenPrefix.firstValue]
    simp [a,GateOp.eval,List.getD_eq_getElem?_getD]
  have heval (x : Fin 9 → Bool) : C.eval (List.ofFn x) = edge x := by
    exact (PetersenPrefix.semanticTail a (b :: D.gates) D.output x _ (first x)).trans (realizes x)
  have h := PEqualNP.Outside.L_meta_1667 C legal first (funext heval)
  have size : C.size = D.size + 2 := by simp [C,Circuit.size]
  omega

end PEqualNP.Research.ParentChildren
