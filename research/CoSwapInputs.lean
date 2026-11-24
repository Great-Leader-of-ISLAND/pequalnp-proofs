import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research.PrefixSwap
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
        g.inputs.map (fun i => w.getD i false) := by simp [List.map_map, Function.comp_def, hs]
    have hh : ∀ i, (step v (rewire a b g)).getD (index a b i) false = (step w g).getD i false := by
      intro i
      simp only [step, rewire, hp, read_snoc, hl]
      by_cases hi : i = w.length
      · subst i
        simp [index, show w.length ≠ a by omega, show w.length ≠ b by omega]
      · have h' : index a b i ≠ w.length := by
          unfold index
          split_ifs <;> omega
        simp [h', hi, hs]
    apply ih (step w g) (step v (rewire a b g)) (by simp [step]; omega) (by simp [step]; omega) (by simp [step, hl]) hh

theorem swapEval (a b : Nat) (C : Circuit) (w v : List Bool)
    (ha : a < w.length) (hb : b < w.length) (hl : v.length = w.length)
    (hs : ∀ i, v.getD (index a b i) false = w.getD i false) :
    (flip a b C).eval v = C.eval w :=
  transported a b C.gates w v ha hb hl hs C.output

end PEqualNP.Research.PrefixSwap
