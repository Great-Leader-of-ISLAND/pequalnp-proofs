import PEqualNP.CoJunctionFixed4482
import PEqualNP.CoJunctionTree4482
import PEqualNP.CoJunctionLogical4482
namespace CoJunctionFixedModel4482
open CoJunctionFixed4482 CoJunctionWire4482 CoJunctionTree4482
open CoPortRoots4482 CoPortFrontier4482 CoJunctionLogical4482

def start (seeded : Bool) : List Wire :=
  let lower := [Wire.input 0,.input 1,.input 2]
  let others := [Wire.input 3,.input 4,.input 5,.input 6,.input 7,.input 8]
  lower ++ (if seeded then [Wire.gate true (.input 0) (.input 2)] else []) ++ others

def group (seeded : Bool) (idx : Nat) : G :=
  if seeded then if idx=1 then 10 else 0
  else Fin.ofNat 12 ([0,1,2,3,4,5,9,8,7,6,10,11].getD idx 0)

structure Action where
  i : Nat
  j : Nat
  op : Bool
  da : Bool
  db : Bool
  perm : G

def decode (seeded : Bool) (tag : Nat) : Action :=
  let rule := tag/16
  let rank := rule/8
  let j := ((List.range 16).find? (fun j => decide (rank < j*(j+1)/2))).getD 15
  ⟨rank-j*(j-1)/2,j,rule.testBit 2,rule.testBit 0,rule.testBit 1,group seeded (tag%16)⟩

def use (act : Action) (xs : List Wire) : List Wire :=
  match xs[act.i]?,xs[act.j]? with
  | some a,some b => discover act.perm xs act.op a b act.da act.db
  | _,_ => []

/-- Random access follows only the selected state and its first-discovery
ancestors; the computational depth is the path length, not the state id. -/
def build (h : Graph) (seeded : Bool) : Nat → Nat → List Wire
  | 0,i => if i=0 then start seeded else []
  | fuel+1,i => if i=0 then start seeded else
      use (decode seeded (firstAction h i)) (build h seeded fuel (parent h i))

inductive Ancestry (h : Graph) : Nat → Nat → Prop
  | root : Ancestry h 0 0
  | child {i d} (ne : i≠0) (prev : Ancestry h (parent h i) d) : Ancestry h i (d+1)

theorem stable {h : Graph} (seeded : Bool) {i d} (w : Ancestry h i d)
    {n m : Nat} (en : d≤n) (em : d≤m) : build h seeded n i = build h seeded m i := by
  induction w generalizing n m with
  | root => cases n <;> cases m <;> rfl
  | @child i d ne prev ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases m with
      | zero => omega
      | succ m =>
        simp only [build,if_neg ne]
        exact congrArg _ (ih (n:=n) (m:=m) (by omega) (by omega))

def data (xs : List Wire) : List Entry :=
  xs.map fun w => ((eval w).full,(eval w).projected)

theorem data_real (xs : List Wire) : authentic (data xs) := by
  intro z hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  exact (eval w).correct

theorem data_values (xs : List Wire) : words (data xs)=values xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change value x :: words (data xs) = value x :: values xs
    rw [ih]

def table (h : Graph) (seeded : Bool) (depth : Nat) (i : Nat) : Record :=
  ⟨data (build h seeded depth i),budget h i⟩

theorem table_real (h : Graph) (seeded : Bool) (depth i : Nat) :
    authentic (table h seeded depth i).bank :=
  data_real _

theorem starts_raw : (values (start false)).toFinset=raws.toFinset := by decide +kernel
theorem starts_preset : (values (start true)).toFinset=init.toFinset := by decide +kernel

theorem root_values (h : Graph) (seeded : Bool) (depth : Nat) :
    (stateWords (table h seeded depth 0)).toFinset =
      if seeded then init.toFinset else raws.toFinset := by
  change (words (data (build h seeded depth 0))).toFinset=_
  rw [data_values]
  have base : build h seeded depth 0=start seeded := by cases depth <;> rfl
  rw [base]
  cases seeded
  · exact starts_raw
  · exact starts_preset

#print axioms stable
#print axioms table_real
#print axioms root_values
end CoJunctionFixedModel4482
