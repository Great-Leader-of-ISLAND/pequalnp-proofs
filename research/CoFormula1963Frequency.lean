import PEqualNP.CoFormula1963Geometry
import PEqualNP.CoFormula1963Area

namespace CoFormula1963Frequency
open CoFormula1963Geometry CoFormula1963Local CoFormula1963Area

abbrev Y := Fin 18 × V

def indices (n : ℕ) : List (Fin n) := List.ofFn id

def cols : List Y := (indices 18).flatMap (fun r => (indices 13).map fun s => (r,s))

def word : Fin 18 → ℕ :=
  ![29,39,71,77,83,85,101,105,135,141,195,201,275,281,297,329,337,549]

def pointOn (y : Y) (p : V) := (word y.1).testBit (p-y.2).val

def lineOn (y : Y) (l : V) : Bool :=
  !(pointOn y l || pointOn y (l+1) || pointOn y (l+3) || pointOn y (l+9))

def four (a b c d : Bool) : ℕ :=
  (if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) + (if d then 8 else 0)

def pointMask (p : V) (y : Y) :=
  four (lineOn y p) (lineOn y (p-1)) (lineOn y (p-3)) (lineOn y (p-9))

def lineMask (l : V) (y : Y) :=
  four (pointOn y l) (pointOn y (l+1)) (pointOn y (l+3)) (pointOn y (l+9))

def pointCols (p : V) := cols.filter (fun y => !pointOn y p)
def lineCols (l : V) := cols.filter (fun y => !lineOn y l)

-- The insertion/permutation argument is the one already verified in
-- CoNine3024.Canon, specialized to ordinary natural numbers.
def put (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y::ys => if x≤y then x::y::ys else y::put x ys

def sort : List ℕ → List ℕ
  | [] => []
  | y::ys => put y (sort ys)

theorem perm_put (x : ℕ) (xs : List ℕ) : (put x xs).Perm (x::xs) := by
  induction xs with
  | nil => exact .refl _
  | cons y ys ih =>
    unfold put
    split
    · exact .refl _
    · exact (List.Perm.cons y ih).trans (.swap _ _ _)

theorem perm_sort (xs : List ℕ) : (sort xs).Perm xs := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih => exact (perm_put x _).trans (.cons x ih)

set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem row_bits : ∀ r : Fin 18, ∀ s v : V,
    (pointOn (r,s) v = decide (v∈quad r s)) ∧
    (lineOn (r,s) v = decide (clear (quad r s) v)) := by
  intro r
  fin_cases r <;> decide +kernel

theorem point_sorted : ∀ p : V, sort ((pointCols p).map (pointMask p)) =
    sort (blocks 27 one ++ blocks 9 two) := by
  intro p
  fin_cases p <;> decide +kernel

theorem line_sorted : ∀ l : V, sort ((lineCols l).map (lineMask l)) =
    sort (blocks 18 one ++ blocks 18 two) := by
  intro l
  fin_cases l <;> decide +kernel

theorem point_freq (p : V) :
    ((pointCols p).map (pointMask p)).Perm (blocks 27 one ++ blocks 9 two) := by
  apply (perm_sort _).symm.trans
  rw [point_sorted p]
  exact perm_sort _

theorem line_freq (l : V) :
    ((lineCols l).map (lineMask l)).Perm (blocks 18 one ++ blocks 18 two) := by
  apply (perm_sort _).symm.trans
  rw [line_sorted l]
  exact perm_sort _

#print axioms point_freq
#print axioms line_freq
end CoFormula1963Frequency
