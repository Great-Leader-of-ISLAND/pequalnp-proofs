import PEqualNP.CoSwapInputs
import PEqualNP.CoPetersenPrefix
import PEqualNP.Outside.L_meta_1672

namespace PEqualNP.Research.SecondAnd

open CircuitLowerBounds MetaComplexity
open PrefixSwap

def gate (a b : ℕ) : Gate := ⟨GateOp.and,[a,b]⟩

def withHeads (D : Circuit) : Circuit :=
  let S := flip 9 10 D
  ⟨gate 4 6 :: gate 0 1 :: S.gates, S.output⟩

theorem lastTwo (x : List Bool) (u v : Bool) (i : ℕ) :
    (x ++ [v,u]).getD (index x.length (x.length+1) i) false = (x ++ [u,v]).getD i false := by
  have h (a b : Bool) : x ++ [a,b] = (x ++ [a]) ++ [b] := by simp
  rw [h v u, h u v, read_snoc, read_snoc, read_snoc, read_snoc]
  by_cases h0 : i = x.length
  · subst i
    simp [index]
  · by_cases h1 : i = x.length + 1
    · subst i
      simp [index]
    · simp [index,h0,h1]

theorem bound (D : Circuit) (hfan : FanInTwo D)
    (hfun : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 && x 1,x 4 && x 6]) =
      PEqualNP.Outside.L_meta_1672.Main1672.edgeF x) : 14 ≤ D.size := by
  let C := withHeads D
  have legal : FanInTwo C := by
    intro g hg
    change g ∈ gate 4 6 :: gate 0 1 :: (flip 9 10 D).gates at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [gate]
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [gate]
    exact fan_flip _ _ _ hfan g hg
  have head : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 && x 6) := by
    intro x
    rw [show C = ⟨gate 4 6 :: gate 0 1 :: (flip 9 10 D).gates,(flip 9 10 D).output⟩ from rfl]
    rw [PetersenPrefix.firstValue]
    simp [gate,GateOp.eval,List.getD_eq_getElem?_getD]
  have realizes (x : Fin 9 → Bool) : C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_1672.Main1672.edgeF x := by
    have h1 := PetersenPrefix.semanticTail (gate 4 6) (gate 0 1 :: (flip 9 10 D).gates)
      (flip 9 10 D).output x (x 4 && x 6) (head x)
    refine h1.trans ?_
    have hprefix : step (List.ofFn x ++ [x 4 && x 6]) (gate 0 1) =
        List.ofFn x ++ [x 4 && x 6,x 0 && x 1] := by
      simp [step,gate,GateOp.eval,List.getD_eq_getElem?_getD,List.append_assoc]
    change (((flip 9 10 D).gates).foldl step (step _ (gate 0 1))).getD (flip 9 10 D).output false = _
    rw [hprefix]
    refine Eq.trans ?_ (hfun x)
    apply swapEval (w := List.ofFn x ++ [x 0 && x 1,x 4 && x 6])
    · simp
    · simp
    · simp
    · intro i
      simpa using lastTwo (List.ofFn x) (x 0 && x 1) (x 4 && x 6) i
  have lower := PEqualNP.Outside.L_meta_1672 C legal head (funext realizes)
  have sz : C.size = D.size + 2 := by simp [C,withHeads,flip,Circuit.size]
  omega

end PEqualNP.Research.SecondAnd
