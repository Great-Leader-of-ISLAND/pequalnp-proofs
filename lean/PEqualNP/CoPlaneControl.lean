import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research.Plane125Control

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


private def cand : Circuit := ⟨[⟨GateOp.or, [21, 26]⟩,
    ⟨GateOp.or, [28, 38]⟩,
    ⟨GateOp.or, [42, 43]⟩,
    ⟨GateOp.or, [41, 44]⟩,
    ⟨GateOp.and, [0, 45]⟩,
    ⟨GateOp.or, [21, 22]⟩,
    ⟨GateOp.or, [27, 29]⟩,
    ⟨GateOp.or, [47, 48]⟩,
    ⟨GateOp.or, [39, 49]⟩,
    ⟨GateOp.and, [1, 50]⟩,
    ⟨GateOp.or, [22, 23]⟩,
    ⟨GateOp.or, [28, 30]⟩,
    ⟨GateOp.or, [52, 53]⟩,
    ⟨GateOp.or, [40, 54]⟩,
    ⟨GateOp.and, [2, 55]⟩,
    ⟨GateOp.or, [23, 24]⟩,
    ⟨GateOp.or, [29, 31]⟩,
    ⟨GateOp.or, [57, 58]⟩,
    ⟨GateOp.or, [41, 59]⟩,
    ⟨GateOp.and, [3, 60]⟩,
    ⟨GateOp.or, [21, 24]⟩,
    ⟨GateOp.or, [25, 30]⟩,
    ⟨GateOp.or, [62, 63]⟩,
    ⟨GateOp.or, [32, 64]⟩,
    ⟨GateOp.and, [4, 65]⟩,
    ⟨GateOp.or, [22, 25]⟩,
    ⟨GateOp.or, [26, 31]⟩,
    ⟨GateOp.or, [67, 68]⟩,
    ⟨GateOp.or, [33, 69]⟩,
    ⟨GateOp.and, [5, 70]⟩,
    ⟨GateOp.or, [23, 26]⟩,
    ⟨GateOp.or, [27, 32]⟩,
    ⟨GateOp.or, [72, 73]⟩,
    ⟨GateOp.or, [34, 74]⟩,
    ⟨GateOp.and, [6, 75]⟩,
    ⟨GateOp.or, [24, 27]⟩,
    ⟨GateOp.or, [28, 33]⟩,
    ⟨GateOp.or, [77, 78]⟩,
    ⟨GateOp.or, [35, 79]⟩,
    ⟨GateOp.and, [7, 80]⟩,
    ⟨GateOp.or, [25, 28]⟩,
    ⟨GateOp.or, [29, 34]⟩,
    ⟨GateOp.or, [82, 83]⟩,
    ⟨GateOp.or, [36, 84]⟩,
    ⟨GateOp.and, [8, 85]⟩,
    ⟨GateOp.or, [26, 29]⟩,
    ⟨GateOp.or, [30, 35]⟩,
    ⟨GateOp.or, [87, 88]⟩,
    ⟨GateOp.or, [37, 89]⟩,
    ⟨GateOp.and, [9, 90]⟩,
    ⟨GateOp.or, [27, 30]⟩,
    ⟨GateOp.or, [31, 36]⟩,
    ⟨GateOp.or, [92, 93]⟩,
    ⟨GateOp.or, [38, 94]⟩,
    ⟨GateOp.and, [10, 95]⟩,
    ⟨GateOp.or, [28, 31]⟩,
    ⟨GateOp.or, [32, 37]⟩,
    ⟨GateOp.or, [97, 98]⟩,
    ⟨GateOp.or, [39, 99]⟩,
    ⟨GateOp.and, [11, 100]⟩,
    ⟨GateOp.or, [29, 32]⟩,
    ⟨GateOp.or, [33, 38]⟩,
    ⟨GateOp.or, [102, 103]⟩,
    ⟨GateOp.or, [40, 104]⟩,
    ⟨GateOp.and, [12, 105]⟩,
    ⟨GateOp.or, [30, 33]⟩,
    ⟨GateOp.or, [34, 39]⟩,
    ⟨GateOp.or, [107, 108]⟩,
    ⟨GateOp.or, [41, 109]⟩,
    ⟨GateOp.and, [13, 110]⟩,
    ⟨GateOp.or, [21, 31]⟩,
    ⟨GateOp.or, [34, 35]⟩,
    ⟨GateOp.or, [112, 113]⟩,
    ⟨GateOp.or, [40, 114]⟩,
    ⟨GateOp.and, [14, 115]⟩,
    ⟨GateOp.or, [22, 32]⟩,
    ⟨GateOp.or, [35, 36]⟩,
    ⟨GateOp.or, [117, 118]⟩,
    ⟨GateOp.or, [41, 119]⟩,
    ⟨GateOp.and, [15, 120]⟩,
    ⟨GateOp.or, [21, 23]⟩,
    ⟨GateOp.or, [33, 36]⟩,
    ⟨GateOp.or, [122, 123]⟩,
    ⟨GateOp.or, [37, 124]⟩,
    ⟨GateOp.and, [16, 125]⟩,
    ⟨GateOp.or, [22, 24]⟩,
    ⟨GateOp.or, [34, 37]⟩,
    ⟨GateOp.or, [127, 128]⟩,
    ⟨GateOp.or, [38, 129]⟩,
    ⟨GateOp.and, [17, 130]⟩,
    ⟨GateOp.or, [23, 25]⟩,
    ⟨GateOp.or, [35, 38]⟩,
    ⟨GateOp.or, [132, 133]⟩,
    ⟨GateOp.or, [39, 134]⟩,
    ⟨GateOp.and, [18, 135]⟩,
    ⟨GateOp.or, [24, 26]⟩,
    ⟨GateOp.or, [36, 39]⟩,
    ⟨GateOp.or, [137, 138]⟩,
    ⟨GateOp.or, [40, 139]⟩,
    ⟨GateOp.and, [19, 140]⟩,
    ⟨GateOp.or, [25, 27]⟩,
    ⟨GateOp.or, [37, 40]⟩,
    ⟨GateOp.or, [142, 143]⟩,
    ⟨GateOp.or, [41, 144]⟩,
    ⟨GateOp.and, [20, 145]⟩,
    ⟨GateOp.or, [46, 51]⟩,
    ⟨GateOp.or, [56, 61]⟩,
    ⟨GateOp.or, [66, 71]⟩,
    ⟨GateOp.or, [76, 81]⟩,
    ⟨GateOp.or, [86, 91]⟩,
    ⟨GateOp.or, [96, 101]⟩,
    ⟨GateOp.or, [106, 111]⟩,
    ⟨GateOp.or, [116, 121]⟩,
    ⟨GateOp.or, [126, 131]⟩,
    ⟨GateOp.or, [136, 141]⟩,
    ⟨GateOp.or, [147, 148]⟩,
    ⟨GateOp.or, [149, 150]⟩,
    ⟨GateOp.or, [151, 152]⟩,
    ⟨GateOp.or, [153, 154]⟩,
    ⟨GateOp.or, [155, 156]⟩,
    ⟨GateOp.or, [157, 158]⟩,
    ⟨GateOp.or, [159, 160]⟩,
    ⟨GateOp.or, [146, 161]⟩,
    ⟨GateOp.or, [162, 163]⟩,
    ⟨GateOp.or, [164, 165]⟩], 166⟩
private def prefixFamilies : List (Family 42) := List.ofFn fun i : Fin 42 => [[i]]
private def families : List (Family 42) := [[[21],[26]],
    [[28],[38]],
    [[21],[26],[28],[38]],
    [[21],[26],[28],[38],[41]],
    [[0, 21],[0, 26],[0, 28],[0, 38],[0, 41]],
    [[21],[22]],
    [[27],[29]],
    [[21],[22],[27],[29]],
    [[21],[22],[27],[29],[39]],
    [[1, 21],[1, 22],[1, 27],[1, 29],[1, 39]],
    [[22],[23]],
    [[28],[30]],
    [[22],[23],[28],[30]],
    [[22],[23],[28],[30],[40]],
    [[2, 22],[2, 23],[2, 28],[2, 30],[2, 40]],
    [[23],[24]],
    [[29],[31]],
    [[23],[24],[29],[31]],
    [[23],[24],[29],[31],[41]],
    [[3, 23],[3, 24],[3, 29],[3, 31],[3, 41]],
    [[21],[24]],
    [[25],[30]],
    [[21],[24],[25],[30]],
    [[21],[24],[25],[30],[32]],
    [[4, 21],[4, 24],[4, 25],[4, 30],[4, 32]],
    [[22],[25]],
    [[26],[31]],
    [[22],[25],[26],[31]],
    [[22],[25],[26],[31],[33]],
    [[5, 22],[5, 25],[5, 26],[5, 31],[5, 33]],
    [[23],[26]],
    [[27],[32]],
    [[23],[26],[27],[32]],
    [[23],[26],[27],[32],[34]],
    [[6, 23],[6, 26],[6, 27],[6, 32],[6, 34]],
    [[24],[27]],
    [[28],[33]],
    [[24],[27],[28],[33]],
    [[24],[27],[28],[33],[35]],
    [[7, 24],[7, 27],[7, 28],[7, 33],[7, 35]],
    [[25],[28]],
    [[29],[34]],
    [[25],[28],[29],[34]],
    [[25],[28],[29],[34],[36]],
    [[8, 25],[8, 28],[8, 29],[8, 34],[8, 36]],
    [[26],[29]],
    [[30],[35]],
    [[26],[29],[30],[35]],
    [[26],[29],[30],[35],[37]],
    [[9, 26],[9, 29],[9, 30],[9, 35],[9, 37]],
    [[27],[30]],
    [[31],[36]],
    [[27],[30],[31],[36]],
    [[27],[30],[31],[36],[38]],
    [[10, 27],[10, 30],[10, 31],[10, 36],[10, 38]],
    [[28],[31]],
    [[32],[37]],
    [[28],[31],[32],[37]],
    [[28],[31],[32],[37],[39]],
    [[11, 28],[11, 31],[11, 32],[11, 37],[11, 39]],
    [[29],[32]],
    [[33],[38]],
    [[29],[32],[33],[38]],
    [[29],[32],[33],[38],[40]],
    [[12, 29],[12, 32],[12, 33],[12, 38],[12, 40]],
    [[30],[33]],
    [[34],[39]],
    [[30],[33],[34],[39]],
    [[30],[33],[34],[39],[41]],
    [[13, 30],[13, 33],[13, 34],[13, 39],[13, 41]],
    [[21],[31]],
    [[34],[35]],
    [[21],[31],[34],[35]],
    [[21],[31],[34],[35],[40]],
    [[14, 21],[14, 31],[14, 34],[14, 35],[14, 40]],
    [[22],[32]],
    [[35],[36]],
    [[22],[32],[35],[36]],
    [[22],[32],[35],[36],[41]],
    [[15, 22],[15, 32],[15, 35],[15, 36],[15, 41]],
    [[21],[23]],
    [[33],[36]],
    [[21],[23],[33],[36]],
    [[21],[23],[33],[36],[37]],
    [[16, 21],[16, 23],[16, 33],[16, 36],[16, 37]],
    [[22],[24]],
    [[34],[37]],
    [[22],[24],[34],[37]],
    [[22],[24],[34],[37],[38]],
    [[17, 22],[17, 24],[17, 34],[17, 37],[17, 38]],
    [[23],[25]],
    [[35],[38]],
    [[23],[25],[35],[38]],
    [[23],[25],[35],[38],[39]],
    [[18, 23],[18, 25],[18, 35],[18, 38],[18, 39]],
    [[24],[26]],
    [[36],[39]],
    [[24],[26],[36],[39]],
    [[24],[26],[36],[39],[40]],
    [[19, 24],[19, 26],[19, 36],[19, 39],[19, 40]],
    [[25],[27]],
    [[37],[40]],
    [[25],[27],[37],[40]],
    [[25],[27],[37],[40],[41]],
    [[20, 25],[20, 27],[20, 37],[20, 40],[20, 41]],
    [[0, 21],[0, 26],[0, 28],[0, 38],[0, 41],[1, 21],[1, 22],[1, 27],[1, 29],[1, 39]],
    [[2, 22],[2, 23],[2, 28],[2, 30],[2, 40],[3, 23],[3, 24],[3, 29],[3, 31],[3, 41]],
    [[4, 21],[4, 24],[4, 25],[4, 30],[4, 32],[5, 22],[5, 25],[5, 26],[5, 31],[5, 33]],
    [[6, 23],[6, 26],[6, 27],[6, 32],[6, 34],[7, 24],[7, 27],[7, 28],[7, 33],[7, 35]],
    [[8, 25],[8, 28],[8, 29],[8, 34],[8, 36],[9, 26],[9, 29],[9, 30],[9, 35],[9, 37]],
    [[10, 27],[10, 30],[10, 31],[10, 36],[10, 38],[11, 28],[11, 31],[11, 32],[11, 37],[11, 39]],
    [[12, 29],[12, 32],[12, 33],[12, 38],[12, 40],[13, 30],[13, 33],[13, 34],[13, 39],[13, 41]],
    [[14, 21],[14, 31],[14, 34],[14, 35],[14, 40],[15, 22],[15, 32],[15, 35],[15, 36],[15, 41]],
    [[16, 21],[16, 23],[16, 33],[16, 36],[16, 37],[17, 22],[17, 24],[17, 34],[17, 37],[17, 38]],
    [[18, 23],[18, 25],[18, 35],[18, 38],[18, 39],[19, 24],[19, 26],[19, 36],[19, 39],[19, 40]],
    [[0, 21],[0, 26],[0, 28],[0, 38],[0, 41],[1, 21],[1, 22],[1, 27],[1, 29],[1, 39],[2, 22],[2, 23],[2, 28],[2, 30],[2, 40],[3, 23],[3, 24],[3, 29],[3, 31],[3, 41]],
    [[4, 21],[4, 24],[4, 25],[4, 30],[4, 32],[5, 22],[5, 25],[5, 26],[5, 31],[5, 33],[6, 23],[6, 26],[6, 27],[6, 32],[6, 34],[7, 24],[7, 27],[7, 28],[7, 33],[7, 35]],
    [[8, 25],[8, 28],[8, 29],[8, 34],[8, 36],[9, 26],[9, 29],[9, 30],[9, 35],[9, 37],[10, 27],[10, 30],[10, 31],[10, 36],[10, 38],[11, 28],[11, 31],[11, 32],[11, 37],[11, 39]],
    [[12, 29],[12, 32],[12, 33],[12, 38],[12, 40],[13, 30],[13, 33],[13, 34],[13, 39],[13, 41],[14, 21],[14, 31],[14, 34],[14, 35],[14, 40],[15, 22],[15, 32],[15, 35],[15, 36],[15, 41]],
    [[16, 21],[16, 23],[16, 33],[16, 36],[16, 37],[17, 22],[17, 24],[17, 34],[17, 37],[17, 38],[18, 23],[18, 25],[18, 35],[18, 38],[18, 39],[19, 24],[19, 26],[19, 36],[19, 39],[19, 40]],
    [[0, 21],[0, 26],[0, 28],[0, 38],[0, 41],[1, 21],[1, 22],[1, 27],[1, 29],[1, 39],[2, 22],[2, 23],[2, 28],[2, 30],[2, 40],[3, 23],[3, 24],[3, 29],[3, 31],[3, 41],[4, 21],[4, 24],[4, 25],[4, 30],[4, 32],[5, 22],[5, 25],[5, 26],[5, 31],[5, 33],[6, 23],[6, 26],[6, 27],[6, 32],[6, 34],[7, 24],[7, 27],[7, 28],[7, 33],[7, 35]],
    [[8, 25],[8, 28],[8, 29],[8, 34],[8, 36],[9, 26],[9, 29],[9, 30],[9, 35],[9, 37],[10, 27],[10, 30],[10, 31],[10, 36],[10, 38],[11, 28],[11, 31],[11, 32],[11, 37],[11, 39],[12, 29],[12, 32],[12, 33],[12, 38],[12, 40],[13, 30],[13, 33],[13, 34],[13, 39],[13, 41],[14, 21],[14, 31],[14, 34],[14, 35],[14, 40],[15, 22],[15, 32],[15, 35],[15, 36],[15, 41]],
    [[16, 21],[16, 23],[16, 33],[16, 36],[16, 37],[17, 22],[17, 24],[17, 34],[17, 37],[17, 38],[18, 23],[18, 25],[18, 35],[18, 38],[18, 39],[19, 24],[19, 26],[19, 36],[19, 39],[19, 40],[20, 25],[20, 27],[20, 37],[20, 40],[20, 41]],
    [[0, 21],[0, 26],[0, 28],[0, 38],[0, 41],[1, 21],[1, 22],[1, 27],[1, 29],[1, 39],[2, 22],[2, 23],[2, 28],[2, 30],[2, 40],[3, 23],[3, 24],[3, 29],[3, 31],[3, 41],[4, 21],[4, 24],[4, 25],[4, 30],[4, 32],[5, 22],[5, 25],[5, 26],[5, 31],[5, 33],[6, 23],[6, 26],[6, 27],[6, 32],[6, 34],[7, 24],[7, 27],[7, 28],[7, 33],[7, 35],[8, 25],[8, 28],[8, 29],[8, 34],[8, 36],[9, 26],[9, 29],[9, 30],[9, 35],[9, 37],[10, 27],[10, 30],[10, 31],[10, 36],[10, 38],[11, 28],[11, 31],[11, 32],[11, 37],[11, 39],[12, 29],[12, 32],[12, 33],[12, 38],[12, 40],[13, 30],[13, 33],[13, 34],[13, 39],[13, 41],[14, 21],[14, 31],[14, 34],[14, 35],[14, 40],[15, 22],[15, 32],[15, 35],[15, 36],[15, 41]],
    [[0, 21],[0, 26],[0, 28],[0, 38],[0, 41],[1, 21],[1, 22],[1, 27],[1, 29],[1, 39],[2, 22],[2, 23],[2, 28],[2, 30],[2, 40],[3, 23],[3, 24],[3, 29],[3, 31],[3, 41],[4, 21],[4, 24],[4, 25],[4, 30],[4, 32],[5, 22],[5, 25],[5, 26],[5, 31],[5, 33],[6, 23],[6, 26],[6, 27],[6, 32],[6, 34],[7, 24],[7, 27],[7, 28],[7, 33],[7, 35],[8, 25],[8, 28],[8, 29],[8, 34],[8, 36],[9, 26],[9, 29],[9, 30],[9, 35],[9, 37],[10, 27],[10, 30],[10, 31],[10, 36],[10, 38],[11, 28],[11, 31],[11, 32],[11, 37],[11, 39],[12, 29],[12, 32],[12, 33],[12, 38],[12, 40],[13, 30],[13, 33],[13, 34],[13, 39],[13, 41],[14, 21],[14, 31],[14, 34],[14, 35],[14, 40],[15, 22],[15, 32],[15, 35],[15, 36],[15, 41],[16, 21],[16, 23],[16, 33],[16, 36],[16, 37],[17, 22],[17, 24],[17, 34],[17, 37],[17, 38],[18, 23],[18, 25],[18, 35],[18, 38],[18, 39],[19, 24],[19, 26],[19, 36],[19, 39],[19, 40],[20, 25],[20, 27],[20, 37],[20, 40],[20, 41]]]
private def edgeList : List (Fin 42 × Fin 42) := [(0,21), (0,26), (0,28), (0,38), (0,41), (1,21), (1,22), (1,27), (1,29), (1,39), (2,22), (2,23), (2,28), (2,30), (2,40), (3,23), (3,24), (3,29), (3,31), (3,41), (4,21), (4,24), (4,25), (4,30), (4,32), (5,22), (5,25), (5,26), (5,31), (5,33), (6,23), (6,26), (6,27), (6,32), (6,34), (7,24), (7,27), (7,28), (7,33), (7,35), (8,25), (8,28), (8,29), (8,34), (8,36), (9,26), (9,29), (9,30), (9,35), (9,37), (10,27), (10,30), (10,31), (10,36), (10,38), (11,28), (11,31), (11,32), (11,37), (11,39), (12,29), (12,32), (12,33), (12,38), (12,40), (13,30), (13,33), (13,34), (13,39), (13,41), (14,21), (14,31), (14,34), (14,35), (14,40), (15,22), (15,32), (15,35), (15,36), (15,41), (16,21), (16,23), (16,33), (16,36), (16,37), (17,22), (17,24), (17,34), (17,37), (17,38), (18,23), (18,25), (18,35), (18,38), (18,39), (19,24), (19,26), (19,36), (19,39), (19,40), (20,25), (20,27), (20,37), (20,40), (20,41)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
private theorem checked : check cand.gates families prefixFamilies = true := by decide +kernel

private theorem prefix_values (x : Fin 42 → Bool) :
    values prefixFamilies x = List.ofFn x := by
  simp [values, prefixFamilies, accepts, List.map_ofFn, Function.comp_def]

set_option maxRecDepth 16384 in
private theorem output_family :
    (prefixFamilies ++ families).getD cand.output [] = edgeList.map (fun e => [e.1,e.2]) := rfl

private theorem edge_correct (x : Fin 42 → Bool) :
    cand.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42, (u.val, v.val) ∈ (edgeList.map fun e => (e.1.val,e.2.val)) ∧
        x u = true ∧ x v = true := by
  have hw := check_sound cand.gates families prefixFamilies checked x
  rw [prefix_values] at hw
  change (cand.gates.foldl evalStep (List.ofFn x)).getD cand.output false = true ↔ _
  rw [hw, get_value, output_family]
  simp only [accepts, List.any_map, Function.comp_def, List.all_cons, List.all_nil,
    Bool.and_true, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨u,v⟩, he, hu, hv⟩
    exact ⟨u, v, List.mem_map.mpr ⟨(u,v), he, rfl⟩, hu, hv⟩
  · rintro ⟨u,v, hm, hu,hv⟩
    obtain ⟨⟨a,b⟩, he, h⟩ := List.mem_map.mp hm
    have ha : a = u := Fin.ext (congrArg Prod.fst h)
    have hb : b = v := Fin.ext (congrArg Prod.snd h)
    subst a
    subst b
    exact ⟨(u,v), he, hu, hv⟩

end PEqualNP.Research.Plane125Control

open PEqualNP.Research.Plane125Control in
set_option maxRecDepth 16384 in
theorem PEqualNP.Research.Plane125Control.upper_bound : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 125 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  refine ⟨cand, ?_, by decide, edge_correct⟩
  simp [PEqualNP.MetaComplexity.Monotone2, cand]
