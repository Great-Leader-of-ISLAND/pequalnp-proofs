import PEqualNP.CoPortRoots4482

namespace CoPortRoots4482
open CoPortBank4482 CoPortCut4482 CoPortTrace4482 PEqualNP.CircuitLowerBounds

def head : Gate := ⟨.or,[0,2]⟩
def circuit (gs : List Gate) : Circuit := ⟨head::gs,0⟩

private theorem init_values (r : R) :
    init.map (fun w => cell w r) = List.ofFn (row r)++[row r 0 || row r 2] := by
  simp [init,raws,seed,cell,row,List.map_ofFn,BitVec.getLsbD_or]

private theorem actual (gs : List Gate) (r : R)
    (valid : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    (history model init gs).map (fun w => cell w r) =
      (circuit gs).wires (List.ofFn (row r)) := by
  change (history model init gs).map (fun w => model.val w r) = _
  rw [correct model gs init r valid]
  change gs.foldl _ (init.map (fun w => cell w r)) = _
  rw [init_values]
  simp [circuit,head,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD]

theorem roots_of_collision_free (gs : List Gate)
    (valid : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (O : Finset Nat) (cap : O.card≤6)
    (nodupLabel : ¬∃ x y, graph x≠graph y ∧ ∀ i∈O,
      ((circuit gs).wires (List.ofFn x)).getD i false = ((circuit gs).wires (List.ofFn y)).getD i false) :
    ∃ k≤gs.length, Path join (cleanCut model label 6) k raws.toFinset ∨
      Path join (cleanCut model label 6) k init.toFinset := by
  classical
  have start : Covers roots init := fun _ h =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (List.mem_toFinset.mpr h))
  have z0 : model.zero∈roots := Finset.mem_insert_self _ _
  have z1 : model.one∈roots := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  obtain ⟨T,b,cov⟩ := bank model gs z0 z1 start (Bank.initial (join:=join) (root:=roots))
  let read := fun i => (history model init gs).getD i 0
  have represents (i) (r) :
      model.val (read i) r = ((circuit gs).wires (List.ofFn (row r))).getD i false := by
    rw [←actual gs r valid]
    exact (read_values model (history model init gs) r i).symm
  have sep (r s : R) (different : label r ≠ label s) :
      ∃ i∈O,model.val (read i) r ≠ model.val (read i) s := by
    by_contra! same
    apply nodupLabel
    exact ⟨row r,row s,different,fun i hi => by rw [←represents,←represents]; exact same i hi⟩
  have idem : ∀ d a,join d a a=a := by intro d a; cases d <;> simp [join]
  obtain ⟨j,hj,A,sub,path⟩ := observation label 6 b idem read O cap
    (fun i _ => read_mem model cov (b.keeps z0) i) sep
  refine ⟨j,by simpa using hj,?_⟩
  rcases only_roots sub path with rfl|rfl
  · exact Or.inl path
  · exact Or.inr path

#print axioms roots_of_collision_free
end CoPortRoots4482
