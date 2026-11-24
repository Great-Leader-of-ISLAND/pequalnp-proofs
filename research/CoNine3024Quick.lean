import PEqualNP.CoNine3024Fast

namespace CoNine3024.Quick
open Fast

private theorem postpone {α β : Type} (bad : Bool) (xs : List α) (f : α → Option β) :
    (if bad then [] else xs.filterMap f)=xs.filterMap (fun x => if bad then none else f x) := by
  cases bad <;> simp

private theorem order (bad w pay cov : Bool) (x : State) :
    (if w && cov then (if bad then none else if pay then some x else none) else none)=
    (if bad then none else if w && pay && cov then some x else none) := by
  cases bad <;> cases w <;> cases pay <;> cases cov <;> rfl

/-- The finite row obstruction and the width rule run before the 512-row
freshness and all nine geometric counts. These are the exact original checks. -/
def staged (g : Geometry) (remain : Nat) (s : State) (a b : Atom) (more : List Atom)
    (costMore : Nat) (covMore : Cells) (d : Bool) : List State :=
  let z := operation g d a b
  let cost0 := s.spent+(a.fixed ||| b.fixed)+z.fixed+costMore
  let cov0 := separator z ||| covMore
  let bad := z.full==0 || z.full==BitVec.allOnes 512 || s.wires.any (fun w => w.full==z.full)
  ([0,1,2,3] : List Nat).filterMap fun m =>
    let keep := maskKeep a b m
    if decide (more.length+keep.length+1≤remain+1) &&
        (((cov0 ||| union keep) &&& g.need)==g.need) then
      if bad then none else if (((cost0+weight keep) &&& forbidden)==0) then
        some (child s a b z more m) else none
    else none

theorem staged_eq (g : Geometry) (k : Nat) (s : State) (a b : Atom) (r : List Atom)
    (w : Nat) (v : Cells) (d : Bool) : staged g k s a b r w v d = stage g k s a b r w v d := by
  unfold staged stage
  dsimp only
  rw [postpone]
  apply congrArg (fun f : Nat → Option State => ([0,1,2,3] : List Nat).filterMap f)
  funext m
  exact order _ _ _ _ _

def next (g : Geometry) (k : Nat) (s : State) : List State :=
  (pairs s.wires).flatMap fun (a,b) =>
    let r := rest s a b
    let w := weight r
    let c := union r
    staged g k s a b r w c false ++ staged g k s a b r w c true

theorem next_eq (g : Geometry) (k : Nat) (s : State) : next g k s=children g k s := by
  rw [←Fast.next_eq]
  unfold next Fast.next
  apply congrArg (fun f : Atom×Atom → List State => (pairs s.wires).flatMap f)
  funext q
  rcases q with ⟨a,b⟩
  exact congrArg₂ (fun (l r : List State) => l++r)
    (staged_eq g k s a b _ _ _ false) (staged_eq g k s a b _ _ _ true)

def walk (g : Geometry) : Nat → State → Bool
  | 0,s => live g s
  | k+1,s => live g s || (safe s && (next g k s).any (walk g k))

theorem walk_eq (g : Geometry) (k : Nat) : walk g k=search g k := by
  induction k with
  | zero => rfl
  | succ k ih => funext s; simp only [walk,search,ih,next_eq]

end CoNine3024.Quick
