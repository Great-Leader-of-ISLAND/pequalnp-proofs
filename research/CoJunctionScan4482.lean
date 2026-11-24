import PEqualNP.CoJunctionImages4482
import PEqualNP.CoJunctionLogical4482
namespace CoJunctionScan4482
open CoPortRoots4482 CoPortFrontier4482 CoJunctionImages4482 CoJunctionLogical4482

private def pairs {α} : List α → List (α×α)
  | [] => []
  | x::xs => xs.map (x,·) ++ pairs xs

private theorem one_order {α} {a b : α} {xs : List α}
    (ha : a∈xs) (hb : b∈xs) (ne : a≠b) :
    (a,b) ∈ pairs xs ∨ (b,a) ∈ pairs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with hxa|tailA
    · subst x
      have hbt := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨b,hbt,rfl⟩))
    · rcases List.mem_cons.mp hb with hxb|tailB
      · subst x
        exact Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨a,tailA,rfl⟩))
      · rcases ih tailA tailB with h|h
        · exact Or.inl (List.mem_append_right _ h)
        · exact Or.inr (List.mem_append_right _ h)

private theorem filters_comm {α} (f g : α → Bool) (xs : List α) :
    (xs.filter f).filter g = (xs.filter g).filter f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hf : f x <;> cases hg : g x <;> simp [List.filter_cons,hf,hg,ih]

private theorem move_comm (xs : List Entry) (op : Bool) (a b : Entry) (da db : Bool) :
    move xs op b a db da = move xs op a b da db := by
  have gate : make op b a = make op a b := by
    cases op <;> simp [make,join,BitVec.or_comm,BitVec.and_comm]
  unfold move
  rw [gate]
  congr 1
  cases da <;> cases db
  all_goals first | rfl | exact filters_comm _ _ _

def Good (row : Record) (a b : Entry) (op da db : Bool) : Prop :=
  a.1 ≠ b.1 ∧ join op a.1 b.1 ∉ stateWords row ∧
  admitted (move row.bank op a b da db) = true ∧
  (words (move row.bank op a b da db)).toFinset.card ≤ 6+(row.budget-1)

instance {row a b op da db} : Decidable (Good row a b op da db) := by
  unfold Good
  infer_instance

abbrev Reply (I : Type) := Entry → Entry → Bool → Bool → Bool → I × G

def action {I : Type} (table : I → Record) (row : Record) (f : G → W → W)
    (reply : Reply I) (a b : Entry) (op da db : Bool) : Bool :=
  if Good row a b op da db then
    let (t,g) := reply a b op da db
    decide (row.budget-1 ≤ (table t).budget) &&
      CoJunctionCost4482.sameSet (cachedStep (f g) (stateWords row) op a.1 b.1 da db)
        (stateWords (table t))
  else true

def sweep (xs : List Entry) (p : Entry → Entry → Bool → Bool → Bool → Bool) : Bool :=
  (pairs xs).all fun (a,b) =>
    [false,true].all fun op => [false,true].all fun da => [false,true].all fun db =>
      p a b op da db

private theorem pair_inputs {α} {a b : α} {xs : List α} (h : (a,b) ∈ pairs xs) :
    a∈xs ∧ b∈xs := by
  induction xs with
  | nil => simp [pairs] at h
  | cons x xs ih =>
    rcases List.mem_append.mp h with head|tail
    · obtain ⟨y,hy,eq⟩ := List.mem_map.mp head
      cases eq
      exact ⟨List.mem_cons_self,List.mem_cons_of_mem _ hy⟩
    · obtain ⟨ha,hb⟩ := ih tail
      exact ⟨List.mem_cons_of_mem _ ha,List.mem_cons_of_mem _ hb⟩

theorem sweep_mono {xs : List Entry} {p q : Entry → Entry → Bool → Bool → Bool → Bool}
    (step : ∀ a∈xs,∀ b∈xs,∀ op da db,p a b op da db=true → q a b op da db=true)
    (yes : sweep xs p=true) : sweep xs q=true := by
  apply List.all_eq_true.mpr
  intro ab hab
  obtain ⟨a,b⟩ := ab
  obtain ⟨ha,hb⟩ := pair_inputs hab
  have hp := List.all_eq_true.mp yes (a,b) hab
  apply List.all_eq_true.mpr
  intro op hop
  have ho := List.all_eq_true.mp hp op hop
  apply List.all_eq_true.mpr
  intro da hda
  have hl := List.all_eq_true.mp ho da hda
  apply List.all_eq_true.mpr
  intro db hdb
  exact step a ha b hb op da db (List.all_eq_true.mp hl db hdb)

/-- Enumerate each unordered pair once. The finite table of replies is used
only on moves passing the semantic freshness, coverage and width tests. -/
def scan {I : Type} (table : I → Record) (row : Record) (f : G → W → W)
    (reply : Reply I) : Bool :=
  sweep row.bank (action table row f reply)

private theorem flag_mem (d : Bool) : d ∈ [false,true] := by cases d <;> simp

theorem scan_sound {I : Type} {table : I → Record} {row : Record}
    {f : G → W → W} {reply : Reply I}
    (cache : ∀ g x, x∈stateWords row → f g x = reorder (rowEquiv g) x)
    (ok : scan table row f reply = true) : Routed table row := by
  have accepted {a b : Entry} (hp : (a,b)∈pairs row.bank) (op da db : Bool) :
      action table row f reply a b op da db = true := by
    have h1 := List.all_eq_true.mp ok (a,b) hp
    have h2 := List.all_eq_true.mp h1 op (flag_mem op)
    have h3 := List.all_eq_true.mp h2 da (flag_mem da)
    exact List.all_eq_true.mp h3 db (flag_mem db)
  have step {a b : Entry} (ha : a∈row.bank) (hb : b∈row.bank)
      {op da db : Bool} (good : Good row a b op da db)
      (allowed : action table row f reply a b op da db = true) :
      ∃ t, ∃ g : G, row.budget-1 ≤ (table t).budget ∧
        (words (move row.bank op a b da db)).toFinset.image (reorder (rowEquiv g)) =
          (stateWords (table t)).toFinset := by
    obtain ⟨t,g,eq⟩ : ∃ t g,reply a b op da db=(t,g) :=
      ⟨(reply a b op da db).1,(reply a b op da db).2,rfl⟩
    simp only [action,if_pos good,eq,Bool.and_eq_true_iff,decide_eq_true_eq] at allowed
    refine ⟨t,g,allowed.1,?_⟩
    rw [value_move]
    exact cached_route (cache g) (List.mem_map.mpr ⟨a,ha,rfl⟩)
      (List.mem_map.mpr ⟨b,hb,rfl⟩) allowed.2
  intro a ha b hb op da db ne fresh cover narrow
  have distinct : a≠b := fun e => ne (congrArg Prod.fst e)
  rcases one_order ha hb distinct with direct|back
  · exact step ha hb ⟨ne,fresh,cover,narrow⟩ (accepted direct op da db)
  · have sw := move_comm row.bank op a b da db
    have gate : join op b.1 a.1 = join op a.1 b.1 := by
      cases op <;> simp [join,BitVec.and_comm,BitVec.or_comm]
    have good : Good row b a op db da := by
      unfold Good
      rw [gate,sw]
      exact ⟨ne.symm,fresh,cover,narrow⟩
    simpa only [sw] using step hb ha good (accepted back op db da)

#print axioms scan_sound
end CoJunctionScan4482
