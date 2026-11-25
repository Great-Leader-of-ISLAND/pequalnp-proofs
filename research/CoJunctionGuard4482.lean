import PEqualNP.CoJunctionUnique4482
import PEqualNP.CoJunctionWidth4482
import PEqualNP.CoJunctionScan4482
namespace CoJunctionGuard4482
open CoPortRoots4482 CoPortFrontier4482 CoBitBlock4482
open CoJunctionScan4482 CoJunctionUnique4482 CoJunctionLogical4482

/-- The expensive width/coverage tests are represented by one number per
state and one exclusivity mask per wire. Both can be certified once. -/
def permits (row : Record) (size : Nat) (u : W → Bits) (a b : Entry) (op da db : Bool) :=
  decide (a.1≠b.1 ∧ join op a.1 b.1∉stateWords row ∧
    size+1-(if da then 1 else 0)-(if db then 1 else 0)≤6+(row.budget-1)) &&
    ((!da || allowed (u a.1) op b.2) && (!db || allowed (u b.1) op a.2))

theorem necessary {row : Record} {u : W → Bits}
    (cache : ∀ x∈row.bank,u x.1=privateRows row.bank x.1)
    {a b : Entry} (ha : a∈row.bank) (hb : b∈row.bank) {op da db : Bool}
    (yes : Good row a b op da db) :
    permits row (stateWords row).toFinset.card u a b op da db = true := by
  obtain ⟨ne,fresh,cover,room⟩ := yes
  have ma : a.1 ∈ stateWords row := List.mem_map.mpr ⟨a,ha,rfl⟩
  have mb : b.1 ∈ stateWords row := List.mem_map.mpr ⟨b,hb,rfl⟩
  rw [value_move] at room
  change (successor (stateWords row) op a.1 b.1 da db).toFinset.card ≤ 6+(row.budget-1) at room
  rw [CoJunctionWidth4482.size_form ma mb ne fresh da db] at room
  have lhs : (!da || allowed (u a.1) op b.2)=true := by
    cases da with
    | false => rfl
    | true => rw [cache a ha]; exact drop_left row.bank hb ne op db cover
  have rhs : (!db || allowed (u b.1) op a.2)=true := by
    cases db with
    | false => rfl
    | true => rw [cache b hb]; exact drop_right row.bank ha ne op da cover
  apply Bool.and_eq_true_iff.mpr
  exact ⟨decide_eq_true ⟨ne,fresh,room⟩,Bool.and_eq_true_iff.mpr ⟨lhs,rhs⟩⟩

def guardedAction {I : Type} (tab : I → Record) (row : Record) (f : G → W → W)
    (reply : Reply I) (size : Nat) (u : W → Bits) (a b : Entry) (op da db : Bool) : Bool :=
  if permits row size u a b op da db then
    let (t,g) := reply a b op da db
    decide (row.budget-1 ≤ (tab t).budget) &&
      CoJunctionCost4482.sameSet
        (CoJunctionImages4482.cachedStep (f g) (stateWords row) op a.1 b.1 da db)
        (stateWords (tab t))
  else true

theorem guarded_sound {I : Type} {tab : I → Record} {row : Record} {f : G → W → W}
    {reply : Reply I} {size : Nat} {u : W → Bits}
    (cache : ∀ g x,x∈stateWords row → f g x=reorder (rowEquiv g) x)
    (nums : size=(stateWords row).toFinset.card)
    (single : ∀ x∈row.bank,u x.1=privateRows row.bank x.1)
    (verified : sweep row.bank (guardedAction tab row f reply size u)=true) :
    Routed tab row := by
  subst size
  apply scan_sound (reply:=reply) cache
  apply sweep_mono _ verified
  intro a ha b hb op da db accepted
  by_cases yes : Good row a b op da db
  · have permitted := necessary single ha hb yes
    simp only [guardedAction,permitted,↓reduceIte] at accepted
    simpa only [action,if_pos yes] using accepted
  · simp only [action,if_neg yes]

#print axioms necessary
#print axioms guarded_sound
end CoJunctionGuard4482
