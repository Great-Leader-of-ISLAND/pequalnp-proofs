import PEqualNP.CoPortCheckMove4482

namespace CoJunctionLogical4482
open CoPortFrontier4482 CoPortRoots4482 CoPortTrace4482 CoPortCut4482

/-- A stored state's ceiling can exceed the number of gates still available on an
incoming branch. Both the current and target frontiers are full truth tables. -/
structure Record where
  bank : List Entry
  budget : Nat

def stateWords (r : Record) := words r.bank

/-- Every still-possible gate in this record has a recorded target, up to a
true graph automorphism. Unreachable branches may be rejected by the certified
coverage or width tests. This definition does not mention realizability. -/
def Routed {I : Type} (table : I → Record) (row : Record) : Prop :=
  ∀ a ∈ row.bank, ∀ b ∈ row.bank, ∀ op da db : Bool,
    a.1 ≠ b.1 → join op a.1 b.1 ∉ stateWords row →
    admitted (move row.bank op a b da db) = true →
    (words (move row.bank op a b da db)).toFinset.card ≤ 6+(row.budget-1) →
    ∃ t : I, ∃ g : G, row.budget-1 ≤ (table t).budget ∧
      (words (move row.bank op a b da db)).toFinset.image (reorder (rowEquiv g)) =
        (stateWords (table t)).toFinset

/-- The table itself may have cycles after identifying duplicate physical
frontiers with different ceiling budgets. An actual counterexample strictly
loses one gate on each routed transition. Leaves use their exact-width
certificates. -/
theorem closes {I : Type} (table : I → Record)
    (auth : ∀ s, authentic (table s).bank)
    (wide : ∀ s, 6 < (stateWords (table s)).toFinset.card)
    (branch : ∀ s, ((stateWords (table s)).toFinset.card = 6+(table s).budget ∧
       ¬ Path join (cleanCut model label 6) (table s).budget (stateWords (table s)).toFinset)
      ∨ Routed table (table s)) :
    ∀ k s, k ≤ (table s).budget → ¬ Reach k (stateWords (table s)) := by
  intro k
  induction k with
  | zero =>
    intro s _ run
    have lower := wide s
    have upper := reach_width run
    omega
  | succ k ih =>
    intro s cap run
    rcases branch s with stop | route
    · obtain ⟨j,hj,path⟩ := run
      exact stop.2 (tight_exact stop.1 ⟨j,by omega,path⟩)
    · obtain ⟨a,ha,b,hb,d,da,db,ne,fresh,cover,tail⟩ :=
        may_move (auth s) (wide s) run
      have narrow := reach_width tail
      have hk : k ≤ (table s).budget-1 := by omega
      obtain ⟨t,g,ht,image⟩ := route a ha b hb d da db ne fresh cover
        (narrow.trans (Nat.add_le_add_left hk 6))
      exact ih t (hk.trans ht) (equivalent (Nat.le_refl k) g image tail)

#print axioms closes
end CoJunctionLogical4482
