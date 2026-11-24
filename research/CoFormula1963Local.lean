import Mathlib

namespace CoFormula1963Local

/-- A point or line has four incident positive rows. A mask in a family is
    the subset of these rows in one nonempty rectangle for this raw label. -/
def weight (mask : ℕ) := ((List.range 4).filter (fun i => mask.testBit i)).length

def compatible : List ℕ → List ℕ
  | [] => [0]
  | m::ms =>
    let old := compatible ms
    old ++ ((old.filter (fun n => n &&& m == 0)).map (fun n => n ||| m))

def least (u : List ℕ) (m : ℕ) : ℕ :=
  u.foldl (fun old x => if x &&& m == m then min old (weight x) else old) 5

def one := [1,2,4,8]
def two := [3,5,6,9,10,12]

def privateRows (F : List ℕ) : ℕ :=
  ((List.range 4).filter fun i => (List.range 4).all fun j =>
    i==j || F.any (fun m => m.testBit j && !m.testBit i)).length

def feasible (F : List ℕ) : Bool :=
  (one++two).all (fun m => least (compatible F) m < 5)

def singles (F : List ℕ) := (one.map (least (compatible F))).sum
def pairs (F : List ℕ) := (two.map (least (compatible F))).sum

def localBound (F : List ℕ) : Prop :=
    116 + 21*privateRows F ≤ 44*F.length + 3*singles F + pairs F ∧
    124 + 21*privateRows F ≤ 44*F.length + 2*singles F + 2*pairs F

instance (F : List ℕ) : Decidable (localBound F) := by unfold localBound; infer_instance

/-- Finite local classification. List entries are distinct four-bit masks in
    increasing order. A fourth rectangle already costs enough independently
    of its shape, by the elementary bound below. -/
theorem oneMask : ∀ a : Fin 16, feasible [a.val]=true → localBound [a.val] := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem twoMasks : ∀ a b : Fin 16, a.val < b.val →
    feasible [a.val,b.val]=true → localBound [a.val,b.val] := by
  intro a
  fin_cases a <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem threeMasks : ∀ a b c : Fin 16, a.val < b.val → b.val < c.val →
    feasible [a.val,b.val,c.val]=true → localBound [a.val,b.val,c.val] := by
  intro a
  fin_cases a <;> decide +kernel

theorem fourOrMore (r p area : ℕ) (many : 4 ≤ r) (small : p ≤ 4) :
    (216 ≤ area → 1044+189*p ≤ 396*r+area) ∧
    (288 ≤ area → 1116+189*p ≤ 396*r+area) := by
  constructor <;> omega

/-- Convert the two four-row inequalities to actual numbers of cells. The
    234 columns include each forced singleton/pair neighbor set 27/9 times
    at a point and 18/18 times at a line. -/
theorem expandLocal {F : List ℕ} (h : localBound F) (area : ℕ) :
    (27*singles F+9*pairs F ≤ area → 1044+189*privateRows F ≤ 396*F.length+area) ∧
    (18*singles F+18*pairs F ≤ area → 1116+189*privateRows F ≤ 396*F.length+area) := by
  obtain ⟨hp,hl⟩ := h
  constructor <;> omega

open scoped BigOperators

theorem leaves (r p area : Fin 26 → ℕ)
    (localCost : ∀ i, (if i.val < 13 then 1044 else 1116) + 189*p i ≤ 396*r i + area i)
    (privateEdges : 52 ≤ ∑ i,p i) (allCells : ∑ i,area i = 12168) :
    65 ≤ ∑ i,r i := by
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => localCost i)
  have constants : (∑ i : Fin 26, if i.val < 13 then (1044:ℕ) else 1116) = 28080 := by decide +kernel
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,constants,allCells] at total
  omega

#print axioms CoFormula1963Local.threeMasks
#print axioms CoFormula1963Local.leaves
end CoFormula1963Local
