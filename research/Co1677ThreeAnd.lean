import PEqualNP.Co1675SliceBridge

namespace Co1677ThreeAnd
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoCommute1675
open Co1675ShardFour (graph)

def permuted (x : Fin 9 → Bool) : Fin 9 → Bool := ![x 2,x 1,x 0,x 5,x 7,x 3,x 6,x 4,x 8]
def address (i : Nat) : Nat := ([2,1,0,5,7,3,6,4,8,10,9] : List Nat).getD i i
def relabel (g : Gate) : Gate := ⟨g.op,g.inputs.map address⟩

theorem perm_graph (x : Fin 9 → Bool) : graph (permuted x)=graph x := by
  change (x 2 && x 1 || x 1 && x 0 || x 0 && x 5 || x 5 && x 7 || x 7 && x 2 ||
    x 2 && x 3 || x 1 && x 6 || x 0 && x 4 || x 5 && x 8 || x 3 && x 4 || x 6 && x 8 || x 8 && x 3)=_
  unfold graph
  ac_rfl

private theorem fixed (i : Nat) (hi : 11 ≤ i) : address i = i := by
  unfold address
  apply List.getD_eq_default
  exact hi
private theorem early (i : Nat) (hi : i<11) : address i<11 := by interval_cases i <;> decide

theorem later (gs : List Gate) (w v : List Bool) (wide : 11≤w.length) (len : v.length=w.length)
    (eq : ∀ i,v.getD (address i) false=w.getD i false) (i : Nat) :
    ((gs.map relabel).foldl step v).getD (address i) false=(gs.foldl step w).getD i false := by
  induction gs generalizing w v with
  | nil => exact eq i
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    have pins : (g.inputs.map address).map (fun k => v.getD k false)=g.inputs.map (fun k => w.getD k false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun k _ => eq k)
    apply ih (step w g) (step v (relabel g)) (by simp [step];omega) (by simp [step,len])
    intro k
    simp only [step,relabel,pins,read_snoc,len]
    by_cases e : k=w.length
    · subst k
      simp only [fixed w.length wide,if_pos rfl]
    · have h : address k≠w.length := by
        by_cases small : k<11
        · have := early k small;omega
        · rw [fixed k (Nat.le_of_not_gt small)]
          exact e
      simp only [if_neg e,if_neg h,eq]

private theorem start (x : Fin 9 → Bool) (f g : Bool) (i : Nat) :
    ((List.ofFn x++[g])++[f]).getD (address i) false =
    ((List.ofFn (permuted x)++[f])++[g]).getD i false := by
  by_cases hi : i<11
  · interval_cases i <;> rfl
  · have large : 11 ≤ i := Nat.le_of_not_gt hi
    have hx : ((List.ofFn x ++ [g]) ++ [f]).length ≤ i := by simpa using large
    have hy : ((List.ofFn (permuted x) ++ [f]) ++ [g]).length ≤ i := by simpa using large
    rw [fixed i large,List.getD_eq_default _ _ hx,List.getD_eq_default _ _ hy]

def oldPin : Fin 3 → Fin 9 := ![5,6,7]
def newPin : Fin 3 → Fin 9 := ![3,6,4]
def second (k : Fin 3) (x : Fin 9 → Bool) := x 2 && x (oldPin k)
def targetHead (k : Fin 3) (x : Fin 9 → Bool) := x 0 && x (newPin k)
def putFirst (k : Fin 3) : Gate := ⟨.and,[0,(newPin k).val]⟩
def putSecond : Gate := ⟨.or,[2,6]⟩

private theorem grounds (k : Fin 3) (x : Fin 9 → Bool) :
    let w := List.ofFn x
    (putFirst k).op.eval ((putFirst k).inputs.map fun i => w.getD i false)=targetHead k x ∧
    step (step w (putFirst k)) putSecond=(w++[second k (permuted x)])++[(permuted x 0 || permuted x 6)] := by
  have raw (j : Fin 9) : (List.ofFn x).getD j.val false = x j := by
    fin_cases j <;> rfl
  have first : (putFirst k).op.eval ((putFirst k).inputs.map fun i => (List.ofFn x).getD i false) =
      targetHead k x := by
    change GateOp.and.eval [(List.ofFn x).getD 0 false,(List.ofFn x).getD (newPin k).val false] = _
    simp [GateOp.eval,targetHead,show (List.ofFn x).getD 0 false = x 0 from raw 0,raw (newPin k)]
  have secondRead (b : Bool) : putSecond.op.eval
      (putSecond.inputs.map fun i => (List.ofFn x ++ [b]).getD i false) = (permuted x 0 || permuted x 6) := by
    change GateOp.or.eval [((List.ofFn x) ++ [b]).getD 2 false,((List.ofFn x) ++ [b]).getD 6 false] = (x 2 || x 6)
    rw [List.getD_append _ _ _ _ (by simp : 2 < (List.ofFn x).length),
        List.getD_append _ _ _ _ (by simp : 6 < (List.ofFn x).length)]
    simp [GateOp.eval,show (List.ofFn x).getD 2 false = x 2 from raw 2,
      show (List.ofFn x).getD 6 false = x 6 from raw 6]
  have swapped : second k (permuted x) = targetHead k x := by fin_cases k <;> rfl
  refine ⟨first,?_⟩
  simp only [step,first,secondRead,swapped]

theorem transfer (k : Fin 3) (bound : ∀ D : Circuit, FanInTwo D →
    (∀ x : Fin 9 → Bool,(D.wires (List.ofFn x)).getD 9 false=targetHead k x) →
    circuitFun 9 D=graph → 16≤D.size) (C : Circuit) (fan : FanInTwo C)
    (one : ∀ x : Fin 9 → Bool,(C.wires (List.ofFn x)).getD 9 false=(x 0 || x 6))
    (two : ∀ x : Fin 9 → Bool,(C.wires (List.ofFn x)).getD 10 false=second k x)
    (computes : circuitFun 9 C=graph) : 16≤C.size := by
  obtain ⟨gs,out⟩ := C
  have h := two (fun _ => true)
  have yes : second k (fun _ => true)=true := rfl
  rw [yes] at h
  cases gs with
  | nil =>
    change (List.ofFn (fun _ : Fin 9 => true)).getD 10 false=true at h
    rw [List.getD_eq_default _ _ (by simp)] at h
    cases h
  | cons a rest =>
    cases rest with
    | nil =>
      change ((List.ofFn (fun _ : Fin 9 => true))++[_]).getD 10 false=true at h
      rw [List.getD_eq_default _ _ (by simp)] at h
      cases h
    | cons b tail =>
      let D : Circuit := ⟨putFirst k::putSecond::tail.map relabel,address out⟩
      have good : FanInTwo D := by
        intro g hg
        change g∈putFirst k::putSecond::tail.map relabel at hg
        rcases List.mem_cons.mp hg with eq|hs
        · subst g;simp [putFirst]
        rcases List.mem_cons.mp hs with eq|hs
        · subst g;simp [putSecond]
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hs
        simpa [relabel] using fan z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
      have first (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false=targetHead k x :=
        (prefixReads (putFirst k) putSecond (tail.map relabel) (address out) x).1.trans (grounds k x).1
      have equal : circuitFun 9 D=graph := by
        funext x
        let y := permuted x
        have e := prefixReads a b tail out y
        have ha := e.1.symm.trans (one y)
        have hb := e.2.symm.trans (two y)
        have original : step (step (List.ofFn y) a) b=(List.ofFn y++[y 0 || y 6])++[second k y] := by
          dsimp only [step];rw [hb,ha]
        have eq := later tail ((List.ofFn y++[y 0 || y 6])++[second k y])
             ((List.ofFn x++[second k y])++[y 0 || y 6]) (by simp) (by simp)
             (start x (y 0 || y 6) (second k y)) out
        have same : circuitFun 9 D x=circuitFun 9 ⟨a::b::tail,out⟩ y := by
          change ((tail.map relabel).foldl step (step (step (List.ofFn x) (putFirst k)) putSecond)).getD (address out) false
            =(tail.foldl step (step (step (List.ofFn y) a) b)).getD out false
          rw [(grounds k x).2,original]
          exact eq
        exact same.trans ((congrFun computes y).trans (perm_graph x))
      simpa [D,Circuit.size] using bound D good first equal

#print axioms transfer
end Co1677ThreeAnd
