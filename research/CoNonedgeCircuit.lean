import PEqualNP.CoNonedgeMono
import PEqualNP.CoPetersenPrefix
import PEqualNP.Outside.L_meta_1572

namespace PEqualNP.Research.NonedgeCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1672.Main1672
open PEqualNP.Outside.L_meta_1572_aux

private theorem snocList (x : Fin 9 → Bool) (b : Bool) :
    List.ofFn (Fin.snoc x b : Fin 10 → Bool) = List.ofFn x ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem tail_mono (D : Circuit) (ao : AO D) (x y : Fin 9 → Bool) (a b : Bool)
    (le : ∀ i, x i = true → y i = true) (ab : a = true → b = true) :
    NonedgeMono.tailF D x a = true → NonedgeMono.tailF D y b = true := by
  have h : ∀ i, (Fin.snoc x a : Fin 10 → Bool) i = true → (Fin.snoc y b : Fin 10 → Bool) i = true := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using ab
    · simpa using le j
  have g := wires_mono D ao (Fin.snoc x a) (Fin.snoc y b) h D.output
  change D.eval (List.ofFn (Fin.snoc x a : Fin 10 → Bool)) = true →
    D.eval (List.ofFn (Fin.snoc y b : Fin 10 → Bool)) = true at g
  simpa [NonedgeMono.tailF,snocList] using g

theorem monotone_tail (D : Circuit) (fan : FanInTwo D) (ao : AO D)
    (realizes : ∀ x, NonedgeMono.tailF D x (NonedgeMono.head x) = edgeF x) : 15 ≤ D.size := by
  apply NonedgeMono.lower D fan
  apply NonedgeMono.erase_head D _ _ realizes
  · intro x y xy
    exact tail_mono D ao x y false false xy id
  · intro x
    exact tail_mono D ao x x false (NonedgeMono.head x) (fun _ => id) (by simp)

theorem full (C : Circuit) (fan : FanInTwo C) (ao : AO C)
    (head : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = NonedgeMono.head x)
    (out : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) : 16 ≤ C.size := by
  obtain ⟨gs,o⟩ := C
  cases gs with
  | nil =>
    have bad := head (fun _ => true)
    rw [PetersenPrefix.emptyHead] at bad
    contradiction
  | cons g tail =>
    let D : Circuit := ⟨tail,o⟩
    have hd : FanInTwo D := fun a ha => fan a (List.mem_cons_of_mem g ha)
    have hm : AO D := fun a ha => ao a (List.mem_cons_of_mem g ha)
    have h := monotone_tail D hd hm (fun x =>
      (PetersenPrefix.semanticTail g tail o x _ (head x)).symm.trans (out x))
    change 15 ≤ tail.length at h
    change 16 ≤ tail.length+1
    omega
end PEqualNP.Research.NonedgeCircuit
