import PEqualNP.CoEscape3825

namespace CoRootless3825
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoNonredundant3825 CoNearReaders3825 CoLocalGate3825

def graph (x : Fin 9 → Bool) : Bool := decide (∃ u v : Fin 9,
  ([(34 : ℕ),68,136,272,1,128,256,0,32].getD u.val 0).testBit v.val=true ∧
    x u=true ∧ x v=true)

def edgePair (a b : Fin 9) (i : Fin 9) := decide (i=a ∨ i=b)

theorem sample : graph (edgePair 0 1)=true ∧ graph (edgePair 2 3)=true ∧
    graph (fun _ => false)=false := by decide +kernel

theorem away (v : Fin 9) : ∃ x : Fin 9→Bool,x v=false ∧ graph x=true := by
  by_cases h : v=0 ∨ v=1
  · refine ⟨edgePair 2 3,?_,sample.2.1⟩
    rcases h with rfl|rfl <;> decide
  · exact ⟨edgePair 0 1,by simp [edgePair,h],sample.1⟩

private theorem raw (C : Circuit) (v : Fin 9) (x : Fin 9 → Bool) : wire 9 C v.val x=x v := by
  let step (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false=w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g rest ih =>
      rw [List.foldl_cons,ih]
      · simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
      · simp [step]; omega
  change (C.gates.foldl step (List.ofFn x)).getD v.val false=x v
  rw [keep _ _ _ (by simpa using v.isLt)]
  simp [List.getD_eq_getElem?_getD]

theorem clean_escape {C : Circuit} (min : IsMinimalCircuit 9 C)
    (correct : circuitFun 9 C=graph) (back : NestedCover.ReadsBack 9 C)
    (arity : ∀ i < C.gates.length,(atPos C i).op=.not → (atPos C i).inputs.length=1)
    (v : Fin 9) : escapes C v := by
  classical
  have eq (x) : wire 9 C C.output x=graph x := congrFun correct x
  have nc : nonconstant 9 C := by
    intro b constant
    have a := (eq _).symm.trans (constant (edgePair 0 1))
    have z := (eq _).symm.trans (constant (fun _ => false))
    rw [sample.1] at a
    rw [sample.2.2] at z
    exact Bool.false_ne_true (z.trans a.symm)
  apply CoEscape3825.escape min nc back arity v
  intro j hj root
  obtain ⟨dj,spec⟩ := Finset.mem_filter.mp hj
  obtain ⟨pos,pin⟩ := Finset.mem_filter.mp dj
  have actual : j < C.gates.length := Finset.mem_range.mp pos
  rcases spec with A|N
  · obtain ⟨x,off,on⟩ := away v
    have hit := (eq x).trans on
    rw [root,evaluate C back j actual x,A] at hit
    have every := List.all_eq_true.mp hit
    have rawon : wire 9 C v.val x=true := every _ (List.mem_map.mpr ⟨v.val,pin,rfl⟩)
    rw [raw,off] at rawon
    exact Bool.false_ne_true rawon
  · have one := arity j actual N
    have pins : (atPos C j).inputs=[v.val] := by
      cases h : (atPos C j).inputs with
      | nil => simp [h] at pin
      | cons a tail =>
        cases tail with
        | nil => simp_all
        | cons b t => simp [h] at one
    have hit := (eq _).trans sample.2.2
    rw [root,evaluate C back j actual _,N,pins] at hit
    simp [GateOp.eval,raw] at hit

theorem exactly_three {C : Circuit} (min : IsMinimalCircuit 9 C)
    (correct : circuitFun 9 C=graph) (back : NestedCover.ReadsBack 9 C)
    (arity : ∀ i < C.gates.length,(atPos C i).op=.not → (atPos C i).inputs.length=1)
    (v : Fin 9) (price : physical C v) (size : (direct C v).card=3) : special C v=∅ :=
  three C v price (clean_escape min correct back arity v) size

theorem exactly_two {C : Circuit} (min : IsMinimalCircuit 9 C)
    (correct : circuitFun 9 C=graph) (back : NestedCover.ReadsBack 9 C)
    (arity : ∀ i < C.gates.length,(atPos C i).op=.not → (atPos C i).inputs.length=1)
    (v : Fin 9) (price : physical C v) (size : (direct C v).card=2)
    (has : (special C v).Nonempty) :
    ∃ i,extra C v={i} ∧ ∀ j∈special C v,j < i ∧ 9+j∈(atPos C i).inputs :=
  two C v price (clean_escape min correct back arity v) size has

#print axioms exactly_three
#print axioms exactly_two
end CoRootless3825
