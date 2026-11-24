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
  fin_cases v <;> rfl

theorem not_raw {C : Circuit} (correct : circuitFun 9 C=graph) (v : Fin 9) : C.output≠v.val := by
  intro h
  let y : Fin 9→Bool := fun i => decide (i=v)
  have off : ∀ j : Fin 9,graph (fun i => decide (i=j))=false := by decide +kernel
  have eq : wire 9 C C.output y=graph y := congrFun correct y
  rw [h,raw] at eq
  have no : y v=false := eq.trans (off v)
  simp [y] at no

theorem correct_nonconstant {C : Circuit} (correct : circuitFun 9 C=graph) : nonconstant 9 C := by
  have eq (x) : wire 9 C C.output x=graph x := congrFun correct x
  intro b constant
  have a := (eq _).symm.trans (constant (edgePair 0 1))
  have z := (eq _).symm.trans (constant (fun _ => false))
  rw [sample.1] at a
  rw [sample.2.2] at z
  exact Bool.false_ne_true (z.trans a.symm)

theorem clean_escape {C : Circuit} (min : IsMinimalCircuit 9 C)
    (correct : circuitFun 9 C=graph) (back : NestedCover.ReadsBack 9 C)
    (arity : ∀ i < C.gates.length,(atPos C i).op=.not → (atPos C i).inputs.length=1)
    (v : Fin 9) : escapes C v := by
  classical
  have eq (x) : wire 9 C C.output x=graph x := congrFun correct x
  have nc := correct_nonconstant correct
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

theorem all_three_or {C : Circuit} (min : IsMinimalCircuit 9 C)
    (correct : circuitFun 9 C=graph) (back : NestedCover.ReadsBack 9 C)
    (arity : ∀ i < C.gates.length,(atPos C i).op=.not → (atPos C i).inputs.length=1)
    (v : Fin 9) (price : physical C v) (size : (direct C v).card=3) :
    ∀ j∈direct C v,(atPos C j).op=.or := by
  classical
  have none := exactly_three min correct back arity v price size
  intro j hj
  have pos : j < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have eq : atPos C j=C.gates[j] := by simp [atPos,NestedCover.gateAt,List.getD_eq_getElem?_getD,pos]
  have allowed := (min.1 (atPos C j) (by rw [eq]; exact List.getElem_mem pos)).1
  have excluded : ¬((atPos C j).op=.and ∨ (atPos C j).op=.not) := by
    intro op
    have mem : j∈special C v := Finset.mem_filter.mpr ⟨hj,op⟩
    rw [none] at mem
    simpa using mem
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at allowed
  rcases allowed with a|o|n
  · exact (excluded (.inl a)).elim
  · exact o
  · exact (excluded (.inr n)).elim

theorem sole_physical_consumer {C : Circuit} (min : IsMinimalCircuit 9 C)
    (correct : circuitFun 9 C=graph) (back : NestedCover.ReadsBack 9 C)
    (arity : ∀ i < C.gates.length,(atPos C i).op=.not → (atPos C i).inputs.length=1)
    (v : Fin 9) (price : physical C v) (size : (direct C v).card=2)
    (has : (special C v).Nonempty) :
    ∃ k,extra C v={k} ∧ ∀ j∈special C v,∀ l < C.size,(9+j∈(atPos C l).inputs ↔ l=k) := by
  classical
  obtain ⟨k,hk,uses⟩ := exactly_two min correct back arity v price size has
  refine ⟨k,hk,?_⟩
  intro j hj l hl
  constructor
  · intro hit
    have order := back l hl (9+j) hit
    have lt : j < l := by omega
    obtain ⟨d,op⟩ := Finset.mem_filter.mp hj
    have vp := (Finset.mem_filter.mp d).2
    have nc := correct_nonconstant correct
    have miss : v.val∉(atPos C l).inputs :=
      fun common => no_common min nc back arity v lt hl vp op ⟨common,hit⟩
    have en : l∈extra C v := Finset.mem_sdiff.mpr ⟨
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hl,Or.inr ⟨j,lt,vp,op,hit⟩⟩,
      fun mem => miss (Finset.mem_filter.mp mem).2⟩
    rw [hk] at en
    exact Finset.mem_singleton.mp en
  · rintro rfl
    exact (uses j hj).2

#print axioms all_three_or
#print axioms sole_physical_consumer
end CoRootless3825
