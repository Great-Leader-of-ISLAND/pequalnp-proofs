import Mathlib

namespace CoMinor4055

/-- Use the numbering of the 42 raw wires in L-meta-4055. -/
def inc (p l : Nat) : Bool :=
  [(p + 20) % 21, p, (p + 5) % 21, (p + 7) % 21, (p + 17) % 21].contains l

def adj (x y : Nat) : Bool :=
  (decide (x < 21 ∧ 21 ≤ y ∧ y < 42) && inc x (y-21)) ||
  (decide (y < 21 ∧ 21 ≤ x ∧ x < 42) && inc y (x-21))

def joins : List Nat → List Nat → Bool
  | _, [] => true
  | seen, v :: vs => seen.any (fun u => adj v u) && joins (v::seen) vs

def linked : List Nat → Bool
  | [] => false
  | v :: vs => joins [v] vs

def touch (xs ys : List Nat) : Bool := xs.any (fun u => ys.any (adj u))

def branches : List (List Nat) :=
  [[21, 1, 4],
   [23, 2, 22],
   [25, 8, 18],
   [30, 9, 10, 27, 20],
   [31, 3, 11, 29],
   [35, 14, 15],
   [36, 16, 33, 5],
   [37, 17, 24, 7, 34, 13],
   [38, 12, 32, 6],
   [40, 19, 39],
   [41, 0, 26, 28]]

/-- All vertices appear exactly once, every group has a connected vertex order,
and every one of the 55 unordered pairs of distinct groups has a joining edge. -/
theorem eleven_groups :
    branches.length = 11 ∧ branches.flatten.length = 42 ∧ branches.flatten.Nodup ∧
    (List.range 42).all (fun i => branches.flatten.contains i) = true ∧
    branches.all linked = true ∧ branches.Pairwise (fun a b => touch a b = true) := by
  decide +kernel

end CoMinor4055
