import PEqualNP.Co1675SliceBridge

namespace Co1677ThirdReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoCommute1675
open Co1675ShardFour (graph)

def pins (g : Gate) : List Nat :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def sample (m : Nat) (i : Fin 9) := m.testBit i.val

theorem read_gate (g : Gate) (v w : List Bool)
    (absent : 6∉pins g) (same : ∀ i, i≠6 → v.getD i false=w.getD i false) :
    g.op.eval (g.inputs.map (fun i => v.getD i false)) =
    g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  obtain ⟨op,ks⟩ := g
  have allPins (abs : 6∉ks) : ks.map (fun i => v.getD i false)=ks.map (fun i => w.getD i false) := by
    exact List.map_congr_left fun i hi => same i (fun eq => abs (eq ▸ hi))
  cases op <;> try exact congrArg _ (allPins absent)
  cases ks with
  | nil => rfl
  | cons a as =>
    have ne : a≠6 := by simpa [pins,eq_comm] using absent
    simpa [GateOp.eval,List.getD_eq_getElem?_getD] using congrArg Bool.not (same a ne)

private theorem invisible (gs : List Gate) (v w : List Bool) (len : v.length=w.length)
    (same : ∀ i, i≠6 → v.getD i false=w.getD i false) (abs : ∀ g∈gs,6∉pins g) :
    ∀ i, i≠6 → (gs.foldl step v).getD i false=(gs.foldl step w).getD i false := by
  induction gs generalizing v w with
  | nil => exact same
  | cons g gs ih =>
    have bit := read_gate g v w (abs _ (by simp)) same
    apply ih (step v g) (step w g) (by simp [step,len]) _ (fun h hh => abs h (by simp [hh]))
    intro i ne
    simp only [step,read_snoc,len,bit,same i ne]

private theorem still (i : Nat) (ne : i≠6) :
    ((List.ofFn (sample 261)++[true])++[true]).getD i false =
    ((List.ofFn (sample 325)++[true])++[true]).getD i false := by
  by_cases small : i<11
  · interval_cases i <;> first | rfl | contradiction
  · rw [List.getD_eq_default _ _ (by simp;omega), List.getD_eq_default _ _ (by simp;omega)]

theorem exists_extra (a b : Gate) (tail : List Gate) (out : Nat)
    (first : ∀ x : Fin 9 → Bool,((Circuit.mk (a::b::tail) out).wires (List.ofFn x)).getD 9 false=(x 0 || x 6))
    (next : ∀ x : Fin 9 → Bool,((Circuit.mk (a::b::tail) out).wires (List.ofFn x)).getD 10 false=(x 2 || x 6))
    (computes : circuitFun 9 ⟨a::b::tail,out⟩=graph) : ∃ g∈tail,6∈pins g := by
  have notRaw : out≠6 := by
    intro eq
    subst out
    have e := congrFun computes (sample 64)
    change ((a::b::tail).foldl step (List.ofFn (sample 64))).getD 6 false=_ at e
    rw [read_kept _ _ _ (by simp)] at e
    exact Bool.noConfusion (show true=false from e)
  by_contra! abs
  have fixedHeads (m : Nat) (h : m=261 ∨ m=325) :
      step (step (List.ofFn (sample m)) a) b = (List.ofFn (sample m)++[true])++[true] := by
    have e := prefixReads a b tail out (sample m)
    have one := e.1.symm.trans (first (sample m))
    have two := e.2.symm.trans (next (sample m))
    dsimp only [step]
    rw [two,one]
    rcases h with rfl|rfl <;> rfl
  have indist := invisible tail _ _ (by simp) still abs out notRaw
  have equal : circuitFun 9 ⟨a::b::tail,out⟩ (sample 261) =
      circuitFun 9 ⟨a::b::tail,out⟩ (sample 325) := by
    change (tail.foldl step (step (step (List.ofFn (sample 261)) a) b)).getD out false =
        (tail.foldl step (step (step (List.ofFn (sample 325)) a) b)).getD out false
    rw [fixedHeads _ (Or.inl rfl),fixedHeads _ (Or.inr rfl)]
    exact indist
  rw [computes] at equal
  exact Bool.noConfusion (show false=true from equal)

#print axioms exists_extra
end Co1677ThirdReader
