import PEqualNP.CoRootless3825

namespace CoJointPins3825
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoRootless3825

def step (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def outsideEq (a b : List Bool) := ∀ j : ℕ,j≠0 → j≠1 → a.getD j false=b.getD j false
def joint (g : Gate) : Prop :=
  (0∉g.inputs ∧ 1∉g.inputs) ∨ ((g.op=.and ∨ g.op=.or) ∧ (g.inputs=[0,1] ∨ g.inputs=[1,0]))

private theorem append_equal {a b : List Bool} {x y : Bool} (len : a.length=b.length)
    (old : outsideEq a b) (eq : x=y) : outsideEq (a++[x]) (b++[y]) := by
  intro i n0 n1
  by_cases lo : i < a.length
  · have lo' : i < b.length := len ▸ lo
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left lo,List.getElem?_append_left lo']
    exact old i n0 n1
  · rw [List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega),len,eq]

private theorem same_step {a b : List Bool} {g : Gate} (ok : joint g) (old : outsideEq a b)
    (a0 : a.getD 0 false=true) (a1 : a.getD 1 false=false)
    (b0 : b.getD 0 false=false) (b1 : b.getD 1 false=true) :
    g.op.eval (g.inputs.map fun i => a.getD i false)=g.op.eval (g.inputs.map fun i => b.getD i false) := by
  rcases ok with ⟨no0,no1⟩|⟨ops,pins⟩
  · apply congrArg g.op.eval
    apply List.map_congr_left
    intro i hi
    exact old i (fun e => no0 (e ▸ hi)) (fun e => no1 (e ▸ hi))
  · rcases ops with op|op <;> rcases pins with f|f <;>
      simp [op,f,GateOp.eval,a0,a1,b0,b1]

private theorem keeps {w : List Bool} (i : ℕ) (h : i < w.length) (g : Gate) :
    (step w g).getD i false=w.getD i false := by
  simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left h]

private theorem tail (gs : List Gate) {a b : List Bool} (len : a.length=b.length) (long : 1 < a.length)
    (old : outsideEq a b) (a0 : a.getD 0 false=true) (a1 : a.getD 1 false=false)
    (b0 : b.getD 0 false=false) (b1 : b.getD 1 false=true) (ok : ∀ g∈gs,joint g) :
    outsideEq (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil => exact old
  | cons g gs ih =>
    have v := same_step (ok g (by simp)) old a0 a1 b0 b1
    exact ih (a:=step a g) (b:=step b g) (by simp [step,len]) (by simp [step]; omega)
      (append_equal len old v) ((keeps 0 (by omega) g).trans a0) ((keeps 1 long g).trans a1)
      ((keeps 0 (by omega) g).trans b0) ((keeps 1 (by omega) g).trans b1)
      (fun h hh => ok h (by simp [hh]))

/-- Even many joint readers cannot distinguish the endpoints. The proof allows arbitrary
    unrelated gate operations (including NOT) and any output index. -/
theorem impossible {C : Circuit} (ok : ∀ g∈C.gates,joint g) : circuitFun 9 C≠graph := by
  intro correct
  let a := List.ofFn (edgePair 0 5)
  let b := List.ofFn (edgePair 1 5)
  have eq : outsideEq a b := by
    intro i n0 n1
    by_cases lo : i < 9
    · interval_cases i <;> first | contradiction | rfl | decide +revert
    · have A : a.length≤i := by change 9≤i; omega
      have B : b.length≤i := by change 9≤i; omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none A,List.getElem?_eq_none B]
  have same := tail C.gates (a:=a) (b:=b) rfl (by decide) eq rfl rfl rfl rfl ok
  have s : (C.wires a).getD C.output false=(C.wires b).getD C.output false :=
    same C.output (not_raw correct (0 : Fin 9)) (not_raw correct (1 : Fin 9))
  have pos : graph (edgePair 0 5)=true := by decide +kernel
  have neg : graph (edgePair 1 5)=false := by decide +kernel
  have pa : (C.wires a).getD C.output false=true := (congrFun correct _).trans pos
  have nb : (C.wires b).getD C.output false=false := (congrFun correct _).trans neg
  exact Bool.false_ne_true (nb.symm.trans (s.symm.trans pa))

#print axioms impossible
end CoJointPins3825
