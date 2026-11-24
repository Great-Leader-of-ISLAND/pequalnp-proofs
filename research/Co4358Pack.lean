import PEqualNP.CoPhysical4358
import PEqualNP.Co4358Order

namespace CoNum4358
open PEqualNP.MetaComplexity CoThetaNine

structure Paired (C D : PhysCircuit) (s t : Nat) where
  slots : List Marked
  original : slots.map (fun p => p.1.phys)=C.gates
  lifted : slots.map (fun p => p.1.lifted p.2)=D.gates
  permitted : ∀ p∈slots,Allowed s t p

theorem extract (lower : SignedLower) (C D : PhysCircuit) (s t : Nat)
    (fan : FanInTwo C) (size : C.size=11) (computes : circuitFun 7 C=target)
    (links : List.Forall₂ (Shape s t) C.gates D.gates) :
    Nonempty (Paired C D s t) := by
  have correct (x : Fin 7 → Bool) : C.eval (List.ofFn x)=target x := congrFun computes x
  obtain ⟨slots,raw,up,allow⟩ := decode_paired (all_binary lower C fan size correct) links
  exact ⟨⟨slots,raw,up,allow⟩⟩

theorem Paired.len {C D s t} (p : Paired C D s t) : p.slots.length=C.size := by
  simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using congrArg List.length p.original

theorem Paired.rawRows {C D s t} (p : Paired C D s t) (xs : List Bool) :
    C.wires xs=ordinary (p.slots.map Prod.fst) xs := by
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires
  rw [←p.original]
  exact ordinary_rows p.slots xs

theorem Paired.upRows {C D s t} (p : Paired C D s t) (xs : List Bool) :
    D.wires (true::xs)=true::raised p.slots xs := by
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires
  rw [←p.lifted]
  exact raised_rows p.slots xs

theorem Paired.readers {C D s t} (p : Paired C D s t) :
    (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length =
      ((p.slots.map Prod.fst).filter Gate.reads2).length := by
  rw [←p.original]
  exact reader_count _

theorem Paired.shifted {C D s t} (p : Paired C D s t) (xs : List Bool) (o : Nat) :
    (D.wires (true::xs)).getD (o+1) false=(raised p.slots xs).getD o false := by
  rw [p.upRows]
  simp [List.getD_eq_getElem?_getD]

namespace Transfer

def liftRow : Fin 6 → Nat := ![1,8,96,66,18,52]
def atRow (r : Nat) (j : Fin 7) : Bool := r.testBit j.val
def sixBit (f : Fin 6 → Bool) : BitVec 6 :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem raised_result (ps : List Marked) (o : Nat)
    (correct : ∀ x : Fin 7 → Bool,(raised ps (List.ofFn x)).getD o false =
      (target x || x 0 || x 3)) :
    sixBit (fun i => (raised ps (List.ofFn (atRow (liftRow i)))).getD o false)=3 := by
  have eq : (fun i => (raised ps (List.ofFn (atRow (liftRow i)))).getD o false) =
      (fun i => let x := atRow (liftRow i); target x || x 0 || x 3) := by
    funext i
    exact correct (atRow (liftRow i))
  rw [eq]
  decide +kernel

theorem from_shifted {C D s t} (p : Paired C D s t)
    (h : ∀ x : Fin 7 → Bool,(D.wires (true::List.ofFn x)).getD (C.output+1) false =
      (target x || x 0 || x 3)) :
    sixBit (fun i =>
      (raised (p.slots.map Marked.ordered) (List.ofFn (atRow (liftRow i)))).getD C.output false)=3 := by
  apply raised_result
  intro x
  rw [ordered_raised,←p.shifted]
  exact h x

end Transfer
end CoNum4358
