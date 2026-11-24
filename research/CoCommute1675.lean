import Mathlib
import PEqualNP.Defs

/- A semantic two-head interchange for L-meta-1675, shard 4.
The general suffix transport is reused from our November 24 CoSwapInputs.lean.
`quotient` takes either accepted sibling lower bound as an argument. -/
namespace CoCommute1675
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def index (a b i : Nat) : Nat := if i = a then b else if i = b then a else i

def rewire (a b : Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map (index a b)⟩

def flip (a b : Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rewire a b), index a b C.output⟩

theorem size_flip (a b : Nat) (C : Circuit) : (flip a b C).size = C.size := by
  simp [flip, Circuit.size]

theorem fan_flip (a b : Nat) (C : Circuit) (hf : FanInTwo C) : FanInTwo (flip a b C) := by
  rintro g hg
  obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
  simpa [rewire] using hf h hh

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

theorem read_snoc (w : List Bool) (v : Bool) (i : Nat) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  by_cases same : i = w.length
  · subst i
    simp
  · rw [if_neg same]
    by_cases low : i < w.length
    · exact List.getD_append _ _ _ _ low
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem transported (a b : Nat) (gs : List Gate) (w v : List Bool)
    (ha : a < w.length) (hb : b < w.length) (hl : v.length = w.length)
    (hs : ∀ i, v.getD (index a b i) false = w.getD i false) :
    ∀ i, ((gs.map (rewire a b)).foldl step v).getD (index a b i) false =
      (gs.foldl step w).getD i false := by
  induction gs generalizing w v with
  | nil => exact hs
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hp : (g.inputs.map (index a b)).map (fun i => v.getD i false) =
        g.inputs.map (fun i => w.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => hs i)
    have hh : ∀ i, (step v (rewire a b g)).getD (index a b i) false = (step w g).getD i false := by
      intro i
      simp only [step, rewire, hp, read_snoc, hl]
      by_cases hi : i = w.length
      · subst i
        simp [index, show w.length ≠ a by omega, show w.length ≠ b by omega]
      · have h' : index a b i ≠ w.length := by
          unfold index
          split_ifs <;> omega
        rw [if_neg h', if_neg hi]
        exact hs i
    apply ih (step w g) (step v (rewire a b g)) (by simp [step]; omega) (by simp [step]; omega) (by simp [step, hl]) hh

theorem swapEval (a b : Nat) (C : Circuit) (w v : List Bool)
    (ha : a < w.length) (hb : b < w.length) (hl : v.length = w.length)
    (hs : ∀ i, v.getD (index a b i) false = w.getD i false) :
    (flip a b C).eval v = C.eval w :=
  transported a b C.gates w v ha hb hl hs C.output


def signal (b : Bool) (x : Fin 9 → Bool) : Bool :=
  if b then x 0 || x 1 else x 0 && x 2

def rawHead (b : Bool) : Gate := if b then ⟨.or,[0,1]⟩ else ⟨.and,[0,2]⟩
def or03 : Gate := ⟨.or,[0,3]⟩

theorem read_kept (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem prefixReads (a b : Gate) (gs : List Gate) (out : ℕ) (x : Fin 9 → Bool) :
    let w := List.ofFn x
    let u := a.op.eval (a.inputs.map fun i => w.getD i false)
    let v := b.op.eval (b.inputs.map fun i => (w ++ [u]).getD i false)
    let C : Circuit := ⟨a::b::gs,out⟩
    (C.wires w).getD 9 false = u ∧ (C.wires w).getD 10 false = v := by
  dsimp only
  change ((gs.foldl step (step (step (List.ofFn x) a) b)).getD 9 false = _) ∧
    ((gs.foldl step (step (step (List.ofFn x) a) b)).getD 10 false = _)
  rw [read_kept _ _ _ (by simp [step]), read_kept _ _ _ (by simp [step])]
  simp [step, read_snoc]

private theorem swapped (w : List Bool) (hw : w.length = 9) (u v : Bool) (i : ℕ) :
    ((w ++ [v]) ++ [u]).getD (index 9 10 i) false = ((w ++ [u]) ++ [v]).getD i false := by
  by_cases h : i=9
  · subst i; simp [index, read_snoc, hw]
  · by_cases h' : i=10
    · subst i; simp [index, read_snoc, hw]
    · rw [show index 9 10 i = i by simp [index, h, h']]
      simp only [read_snoc, List.length_append, List.length_singleton, hw,
        show 9 + 1 = 10 by rfl, if_neg h, if_neg h']

private theorem raw_get (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
  fin_cases i <;> rfl

private theorem canonical (b : Bool) (x : Fin 9 → Bool) :
    (rawHead b).op.eval ((rawHead b).inputs.map fun i => (List.ofFn x).getD i false) = signal b x ∧
    (step (step (List.ofFn x) (rawHead b)) or03) = ((List.ofFn x ++ [signal b x]) ++ [x 0 || x 3]) := by
  have r (i : Fin 9) := raw_get x i
  cases b <;> simp [rawHead, signal, or03, step, GateOp.eval, read_snoc,
    show (List.ofFn x).getD 0 false = x 0 from r 0,
    show (List.ofFn x).getD 1 false = x 1 from r 1,
    show (List.ofFn x).getD 2 false = x 2 from r 2,
    show (List.ofFn x).getD 3 false = x 3 from r 3]

def rearranged (b : Bool) (gs : List Gate) (out : ℕ) : Circuit :=
  ⟨rawHead b :: or03 :: gs.map (rewire 9 10), index 9 10 out⟩

private theorem head_small (b : Bool) :
    (rawHead b).op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      (rawHead b).inputs.length ≤ 2 := by cases b <;> simp [rawHead]

theorem quotient (b : Bool) (f : (Fin 9 → Bool) → Bool) (k : ℕ)
    (known : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = signal b x) →
      circuitFun 9 D = f → k ≤ D.size)
    (a c : Gate) (gs : List Gate) (out : ℕ)
    (fan : FanInTwo ⟨a::c::gs,out⟩)
    (head : ∀ x : Fin 9 → Bool, (Circuit.wires ⟨a::c::gs,out⟩ (List.ofFn x)).getD 9 false = (x 0 || x 3))
    (next : ∀ x : Fin 9 → Bool, (Circuit.wires ⟨a::c::gs,out⟩ (List.ofFn x)).getD 10 false = signal b x)
    (solves : circuitFun 9 ⟨a::c::gs,out⟩ = f) : k ≤ (Circuit.mk (a::c::gs) out).size := by
  let D := rearranged b gs out
  have fanD : FanInTwo D := by
    intro g hg
    change g ∈ rawHead b :: or03 :: gs.map (rewire 9 10) at hg
    simp only [List.mem_cons] at hg
    rcases hg with e | e | he
    · subst g; exact head_small b
    · subst g; simp [or03]
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
      simpa [rewire] using fan j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj))
  have headD : ∀ x, (D.wires (List.ofFn x)).getD 9 false = signal b x := by
    intro x
    exact (prefixReads (rawHead b) or03 (gs.map (rewire 9 10)) (index 9 10 out) x).1.trans (canonical b x).1
  have equal : circuitFun 9 D = f := by
    funext x
    have h := prefixReads a c gs out x
    have ha := h.1.symm.trans (head x)
    have hc := h.2.symm.trans (next x)
    have old : step (step (List.ofFn x) a) c = ((List.ofFn x ++ [x 0 || x 3]) ++ [signal b x]) := by
      dsimp only [step]; rw [hc, ha]
    have sim := transported 9 10 gs ((List.ofFn x ++ [x 0 || x 3]) ++ [signal b x])
        ((List.ofFn x ++ [signal b x]) ++ [x 0 || x 3]) (by simp) (by simp) (by simp)
        (swapped (List.ofFn x) (by simp) (x 0 || x 3) (signal b x)) out
    have same : circuitFun 9 D x = circuitFun 9 ⟨a::c::gs,out⟩ x := by
      change ((gs.map (rewire 9 10)).foldl step (step (step (List.ofFn x) (rawHead b)) or03)).getD
          (index 9 10 out) false = (gs.foldl step (step (step (List.ofFn x) a) c)).getD out false
      rw [(canonical b x).2, old]; exact sim
    exact same.trans (congrFun solves x)
  have bound := known D fanD headD equal
  simpa [D,rearranged,Circuit.size] using bound

end CoCommute1675
