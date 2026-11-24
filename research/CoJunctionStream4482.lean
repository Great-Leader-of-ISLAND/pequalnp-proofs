import PEqualNP.CoJunctionGuard4482
namespace CoJunctionStream4482
open CoPortRoots4482 CoPortFrontier4482 CoBitBlock4482 CoJunctionLogical4482
open CoJunctionScan4482 CoJunctionGuard4482

structure Rule where
  a : Entry
  b : Entry
  op : Bool
  da : Bool
  db : Bool

def flags : List (Bool×Bool) := [(false,false),(true,false),(false,true),(true,true)]

def runs (row : Record) (size : Nat) (u : W → Bits) : List Rule :=
  (operandPairs row.bank).flatMap fun (a,b) =>
    [false,true].flatMap fun op =>
      flags.filterMap fun (da,db) =>
        if permits row size u a b op da db then some ⟨a,b,op,da,db⟩ else none

private theorem retained {row : Record} {size : Nat} {u : W→Bits} {a b : Entry}
    (pair : (a,b)∈operandPairs row.bank) {op da db : Bool}
    (allowed : permits row size u a b op da db=true) :
    (⟨a,b,op,da,db⟩ : Rule) ∈ runs row size u := by
  apply List.mem_flatMap.mpr
  refine ⟨(a,b),pair,List.mem_flatMap.mpr ⟨op,?_,?_⟩⟩
  · cases op <;> simp
  · apply List.mem_filterMap.mpr
    refine ⟨(da,db),?_,?_⟩
    · cases da <;> cases db <;> decide
    · simp only [allowed,↓reduceIte]

def single {I : Type} (table : I → Record) (row : Record) (cache : G → W → W)
    (r : Rule) (ref : I×G) : Bool :=
  decide (row.budget-1 ≤ (table ref.1).budget) &&
    CoJunctionCost4482.sameSet
      (CoJunctionImages4482.cachedStep (cache ref.2) (stateWords row)
        r.op r.a.1 r.b.1 r.da r.db)
      (stateWords (table ref.1))

/-- The checked outgoing list holds only (target, true automorphism). The
gate/last-use choices are regenerated in exactly the native order. -/
def stream {I : Type} (table : I → Record) (row : Record) (cache : G → W → W) :
    List Rule → List (I×G) → Bool
  | [],[] => true
  | c::cs,ref::refs => single table row cache c ref && stream table row cache cs refs
  | _,_ => false

private theorem assigned {I : Type} {table : I → Record} {row : Record} {f : G → W → W}
    {r : Rule} {cs : List Rule} {out : List (I×G)}
    (ok : stream table row f cs out=true) (m : r∈cs) :
    ∃ ref,single table row f r ref=true := by
  induction cs generalizing out with
  | nil => simp at m
  | cons c cs ih =>
    cases out with
    | nil => simp [stream] at ok
    | cons ref refs =>
      obtain ⟨one,tail⟩ := Bool.and_eq_true_iff.mp ok
      rcases List.mem_cons.mp m with eq|mem
      · subst c
        exact ⟨ref,one⟩
      · exact ih tail mem

theorem stream_sound {I : Type} {table : I → Record} {row : Record}
    {f : G → W → W} {u : W → Bits} {size : Nat} {out : List (I×G)}
    (images : ∀ g x,x∈stateWords row → f g x=reorder (rowEquiv g) x)
    (nums : size=(stateWords row).toFinset.card)
    (singleRows : ∀ e∈row.bank,u e.1=CoJunctionUnique4482.privateRows row.bank e.1)
    (verified : stream table row f (runs row size u) out=true) : Routed table row := by
  subst size
  apply from_pairs
  intro a b pair op da db yes
  obtain ⟨ha,hb⟩ := operand_mem pair
  have allow := necessary singleRows ha hb yes
  obtain ⟨⟨t,g⟩,good⟩ := assigned verified (retained pair allow)
  obtain ⟨budget,matchTarget⟩ := Bool.and_eq_true_iff.mp good
  refine ⟨t,g,of_decide_eq_true budget,?_⟩
  rw [value_move]
  exact CoJunctionImages4482.cached_route (images g) (List.mem_map.mpr ⟨a,ha,rfl⟩)
    (List.mem_map.mpr ⟨b,hb,rfl⟩) matchTarget

#print axioms stream_sound
end CoJunctionStream4482
