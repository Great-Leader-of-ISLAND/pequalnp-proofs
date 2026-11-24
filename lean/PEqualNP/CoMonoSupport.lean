import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research.MonoSupport

open PEqualNP.CircuitLowerBounds

abbrev Family (n : ℕ) := List (List (Fin n))

def accepts {n : ℕ} (f : Family n) (x : Fin n → Bool) : Bool :=
  f.any fun t => t.all x

def subsumed {n : ℕ} (f h : Family n) : Bool :=
  f.all fun t => h.any fun u => u.all fun j => t.contains j

theorem subsumed_sound {n : ℕ} {f h : Family n} (ok : subsumed f h = true) (x : Fin n → Bool) :
    accepts f x = true → accepts h x = true := by
  simp only [subsumed, List.all_eq_true, List.any_eq_true, List.contains_iff_mem] at ok
  simp only [accepts, List.any_eq_true, List.all_eq_true]
  rintro ⟨t, ht, hpos⟩
  obtain ⟨u, hu, hsub⟩ := ok t ht
  exact ⟨u, hu, fun j hj => hpos j (hsub j hj)⟩

def meet {n : ℕ} (f h : Family n) : Family n :=
  f.flatMap fun t => h.map fun u => t ++ u

theorem meet_accepts {n : ℕ} (f h : Family n) (x : Fin n → Bool) :
    accepts (meet f h) x = (accepts f x && accepts h x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [accepts, meet, List.any_eq_true, List.mem_flatMap, List.mem_map,
    Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨w, ⟨t, ht, u, hu, rfl⟩, hw⟩
    exact ⟨⟨t, ht, fun j hj => hw j (List.mem_append_left _ hj)⟩,
      ⟨u, hu, fun j hj => hw j (List.mem_append_right _ hj)⟩⟩
  · rintro ⟨⟨t, ht, pt⟩, ⟨u, hu, pu⟩⟩
    refine ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, ?_⟩
    intro j hj
    exact (List.mem_append.mp hj).elim (pt j) (pu j)

def opAllowed : GateOp → Bool
  | .and | .or => true
  | _ => false

def raw {n : ℕ} (W : List (Family n)) (g : Gate) : Family n :=
  let fs := g.inputs.map fun i => W.getD i []
  match g.op with
  | .and => fs.foldr meet [[]]
  | .or => fs.flatten
  | _ => []

def values {n : ℕ} (W : List (Family n)) (x : Fin n → Bool) : List Bool :=
  W.map fun f => accepts f x

private theorem get_value {n : ℕ} (W : List (Family n)) (x : Fin n → Bool) (i : ℕ) :
    (values W x).getD i false = accepts (W.getD i []) x := by
  unfold values
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

private theorem all_accepts {n : ℕ} (fs : List (Family n)) (x : Fin n → Bool) :
    accepts (fs.foldr meet [[]]) x = (fs.map (fun f => accepts f x)).all id := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [meet_accepts, ih]

private theorem any_accepts {n : ℕ} (fs : List (Family n)) (x : Fin n → Bool) :
    accepts fs.flatten x = (fs.map (fun f => accepts f x)).any id := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change accepts (f ++ fs.flatten) x = (accepts f x || (fs.map (fun t => accepts t x)).any id)
    rw [← ih]
    simp only [accepts, List.any_append]

private theorem raw_sound {n : ℕ} (W : List (Family n)) (g : Gate) (x : Fin n → Bool)
    (ok : opAllowed g.op = true) :
    accepts (raw W g) x = g.op.eval (g.inputs.map fun i => (values W x).getD i false) := by
  rcases g with ⟨op, ps⟩
  cases op <;> simp_all only [opAllowed, GateOp.eval, raw, all_accepts, any_accepts,
    List.map_map, Function.comp_def, get_value, Bool.false_eq_true]

def check {n : ℕ} : List Gate → List (Family n) → List (Family n) → Bool
  | [], [], _ => true
  | g :: gs, t :: ts, W =>
    opAllowed g.op && subsumed (raw W g) t && subsumed t (raw W g) &&
      check gs ts (W ++ [t])
  | _, _, _ => false

def evalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem check_sound {n : ℕ} (gs : List Gate) (ts W : List (Family n))
    (ok : check gs ts W = true) (x : Fin n → Bool) :
    gs.foldl evalStep (values W x) = values (W ++ ts) x := by
  induction gs generalizing ts W with
  | nil =>
    cases ts with
    | nil => simp
    | cons => simp [check] at ok
  | cons g gs ih =>
    cases ts with
    | nil => simp [check] at ok
    | cons t ts =>
      simp only [check, Bool.and_eq_true] at ok
      obtain ⟨⟨⟨hop, hl⟩, hr⟩, tail⟩ := ok
      have eqf : accepts (raw W g) x = accepts t x :=
        Bool.eq_iff_iff.mpr ⟨subsumed_sound hl x, subsumed_sound hr x⟩
      have hstep : evalStep (values W x) g = values (W ++ [t]) x := by
        unfold evalStep
        rw [← raw_sound W g x hop, eqf]
        simp [values]
      rw [List.foldl_cons, hstep, ih ts (W ++ [t]) tail]
      simp [List.append_assoc]

end PEqualNP.Research.MonoSupport
