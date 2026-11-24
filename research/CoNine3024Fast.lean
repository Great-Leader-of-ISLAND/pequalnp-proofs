import PEqualNP.CoNine3024

namespace CoNine3024.Fast

def weight : List Atom → Nat
  | [] => 0
  | a::xs => a.fixed+weight xs

def union : List Atom → Cells
  | [] => 0
  | a::xs => separator a ||| union xs

private theorem weight_from (xs : List Atom) (n : Nat) :
    xs.foldl (fun acc a => acc+a.fixed) n = n+weight xs := by
  induction xs generalizing n with
  | nil => simp [weight]
  | cons a xs ih => simp [weight,List.foldl_cons,ih,Nat.add_assoc]

private theorem union_from (xs : List Atom) (v : Cells) :
    xs.foldl (fun acc a => acc ||| separator a) v = v ||| union xs := by
  induction xs generalizing v with
  | nil => simp [union]
  | cons a xs ih => simp [union,List.foldl_cons,ih,BitVec.or_assoc]

private theorem wt_append (xs ys : List Atom) : weight (xs++ys)=weight xs+weight ys := by
  induction xs with
  | nil => simp [weight]
  | cons a xs ih => simp [weight,ih,Nat.add_assoc]

private theorem union_append (xs ys : List Atom) : union (xs++ys)=union xs ||| union ys := by
  induction xs with
  | nil => simp [union]
  | cons a xs ih => simp [union,ih,BitVec.or_assoc]

/-- Compute the unchanged part of the frontier once per pair, including its
    cost and its monotone row-pair separators. -/
def stage (g : Geometry) (remain : Nat) (s : State) (a b : Atom) (more : List Atom)
    (costMore : Nat) (covMore : Cells) (d : Bool) : List State :=
  let z := operation g d a b
  if z.full==0 || z.full==BitVec.allOnes 512 || s.wires.any (fun w => w.full==z.full) then [] else
    let cost0 := s.spent+(a.fixed ||| b.fixed)+z.fixed+costMore
    let cov0 := separator z ||| covMore
    ([0,1,2,3] : List Nat).filterMap fun m =>
      let keep := maskKeep a b m
      if decide (more.length+keep.length+1≤remain+1) &&
          (((cost0+weight keep) &&& forbidden)==0) &&
          (((cov0 ||| union keep) &&& g.need)==g.need) then
        some (child s a b z more m) else none

private theorem or_left (a b c : Cells) : a ||| (b ||| c)=b ||| (a ||| c) := by ac_rfl

private theorem stage_eq (g : Geometry) (k : Nat) (s : State) (a b : Atom) (d : Bool) :
    (let r := rest s a b; stage g k s a b r (weight r) (union r) d) = choices g k s a b d := by
  change stage g k s a b (rest s a b) _ _ d=choices g k s a b d
  unfold stage choices
  dsimp only
  split
  · rfl
  · apply congrArg (fun f : Nat → Option State => ([0,1,2,3] : List Nat).filterMap f)
    funext m
    simp only [child,safe,covered,List.length_cons,List.length_append,weight_from,union_from,
      weight,wt_append,union,union_append,BitVec.zero_or,Bool.and_eq_true,decide_eq_true_eq]
    simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,BitVec.or_assoc,or_left,BitVec.or_comm]

def next (g : Geometry) (k : Nat) (s : State) : List State :=
  (pairs s.wires).flatMap fun (a,b) =>
    let r := rest s a b
    let w := weight r
    let c := union r
    stage g k s a b r w c false ++ stage g k s a b r w c true

theorem next_eq (g : Geometry) (k : Nat) (s : State) : next g k s=children g k s := by
  unfold next children
  apply congrArg (fun f : Atom×Atom → List State => (pairs s.wires).flatMap f)
  funext q
  rcases q with ⟨a,b⟩
  exact congrArg₂ (fun (l r : List State) => l++r) (stage_eq g k s a b false) (stage_eq g k s a b true)

def walk (g : Geometry) : Nat → State → Bool
  | 0,s => live g s
  | k+1,s => live g s || (safe s && (next g k s).any (walk g k))

theorem walk_eq (g : Geometry) (k : Nat) : walk g k=search g k := by
  induction k with
  | zero => rfl
  | succ k ih => funext s; simp only [walk,search,ih,next_eq]

end CoNine3024.Fast
