import PEqualNP.Co4358Search

namespace CoNum4358
open CoAO3143

/-- For one positive singleton p and negative row n, original is the
    old value at n. separates bounds all rewired values which are true
    at p and false at n. -/
structure Flag where
  original : Bool
  separates : Bool
  deriving DecidableEq, Repr, Inhabited

def mergeFlag (d : Bool) (a b : Flag) : Flag :=
  if d then
    let no := a.original || b.original
    ⟨no,(a.separates || b.separates) && !no⟩
  else ⟨a.original && b.original,a.separates || b.separates⟩

abbrev PairFlag := Flag × Flag

def mergePair (d : Bool) (a b : PairFlag) : PairFlag :=
  (mergeFlag d a.1 b.1,mergeFlag d a.2 b.2)

def rawFlag (v : Nat) (p n : Nat) : Flag := ⟨n.testBit v,p.testBit v && !(n.testBit v)⟩
def rawPair : List PairFlag :=
  (List.range 7).map fun i => (rawFlag i 1 96,rawFlag i 8 18)

def represents (f : Flag) (p n : Bool) : Prop :=
  (f.original=true → n=true) ∧ (p=true → n=false → f.separates=true)

private theorem rep_top (f : Flag) : represents f true true := by simp [represents]

private theorem rep_merge (d : Bool) (a b : Flag) (ap an bp bn : Bool)
    (ha : represents a ap an) (hb : represents b bp bn) :
    represents (mergeFlag d a b) (if d then ap||bp else ap&&bp)
      (if d then an||bn else an&&bn) := by
  obtain ⟨ao,ac⟩ := a
  obtain ⟨bo,bc⟩ := b
  cases d <;> simp only [represents,mergeFlag,Bool.false_eq_true,↓reduceIte] at *
  all_goals cases an <;> cases bn <;> cases ao <;> cases bo <;> simp_all <;> tauto

def governs (t : PairFlag) (v : LiftVal) : Prop :=
  represents t.1 (v.getLsbD 0) (v.getLsbD 2) ∧
  represents t.2 (v.getLsbD 1) (v.getLsbD 4)

def governsSet (t : PairFlag) (vs : LiftSet) : Prop := ∀ v∈vs, governs t v

theorem governs_gate {a b : PairFlag} {xs ys : LiftSet}
    (ha : governsSet a xs) (hb : governsSet b ys) (d : Bool) :
    governsSet (mergePair d a b) (looseGate d xs ys) := by
  intro v hv
  rcases List.mem_cons.mp hv with h | mem
  · subst v
    exact ⟨rep_top _,rep_top _⟩
  · simp only [List.mem_eraseDups,List.mem_flatMap,List.mem_map] at mem
    obtain ⟨x,hx,y,hy,rfl⟩ := mem
    have ax := ha x hx
    have bys := hb y hy
    have p := rep_merge d a.1 b.1 _ _ _ _ ax.1 bys.1
    have q := rep_merge d a.2 b.2 _ _ _ _ ax.2 bys.2
    cases d <;> simpa [governs,mergePair,BitVec.getLsbD_or,BitVec.getLsbD_and] using And.intro p q

abbrev Tracks := List.Forall₂ governsSet

theorem Tracks.lookup {ts vs} (h : Tracks ts vs) (i : Nat) :
    governsSet (ts.getD i default) (vs.getD i []) := by
  induction h generalizing i with
  | nil => simp [governsSet]
  | cons h _ ih =>
    cases i with
    | zero => exact h
    | succ i => exact ih i

def Gate.pair (g : Gate) (ts : List PairFlag) : PairFlag :=
  mergePair g.isOr (ts.getD g.a default) (ts.getD g.b default)

private theorem tracks_snoc {ts vs} (h : Tracks ts vs) {a v} (ok : governsSet a v) :
    Tracks (ts++[a]) (vs++[v]) := by
  induction h with
  | nil => exact .cons ok .nil
  | cons hv _ ih => exact .cons hv ih

theorem Tracks.gate {ts vs} (h : Tracks ts vs) (g : Gate) :
    Tracks (ts++[g.pair ts]) (vs++[g.loose vs]) :=
  tracks_snoc h (governs_gate (h.lookup g.a) (h.lookup g.b) g.isOr)

theorem raw_tracks : Tracks rawPair rawLoose := by
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))))
  all_goals
    intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl <;> unfold governs represents <;> decide +kernel

def capability (side : Bool) (t : PairFlag) : Bool :=
  if side then t.1.separates else t.2.separates

private theorem merge_origin (side d : Bool) (a b : PairFlag)
    (h : capability side (mergePair d a b)=true) :
    capability side a=true ∨ capability side b=true := by
  cases side <;> cases d <;> simp [capability,mergePair,mergeFlag] at * <;> tauto

private theorem lastGet {α : Type} (xs : List α) (v d : α) (i : Nat) :
    (xs++[v]).getD i d = if i=xs.length then v else xs.getD i d := by
  induction xs generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ i => simp
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

theorem live_capability {k q bk bs S} (w : Walk k q bk bs S) (side : Bool)
    (ts : List PairFlag) (ht : Tracks ts bs) (hs : ts.length=bk.length) :
    ∃ i∈S, capability side (ts.getD i default)=true := by
  induction w generalizing ts with
  | done q bk bs i orig raised =>
    have pair := ht.lookup i 3 raised
    refine ⟨i,Finset.mem_singleton_self _,?_⟩
    cases side
    · exact pair.2.2 rfl rfl
    · exact pair.1.2 rfl rfl
  | @step k q bk bs U g sorted budget fresh live child ih =>
    obtain ⟨i,mem,cap⟩ := ih _ (ht.gate g) (by simp [hs])
    rw [lastGet,hs] at cap
    by_cases eqi : i=bk.length
    · rw [if_pos eqi] at cap
      rcases merge_origin side g.isOr _ _ cap with a | b
      · exact ⟨g.a,by simp,a⟩
      · exact ⟨g.b,by simp,b⟩
    · rw [if_neg eqi] at cap
      exact ⟨i,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        ((Finset.mem_insert.mp mem).resolve_left eqi)),cap⟩

def supports (ts : List PairFlag) (xs : List Nat) (side : Bool) : Bool :=
  xs.any fun i => capability side (ts.getD i default)

theorem supports_of_walk {k q bk bs S} (w : Walk k q bk bs S) (side : Bool)
    (ts : List PairFlag) (ht : Tracks ts bs) (hs : ts.length=bk.length)
    (xs : List Nat) (hx : xs.toFinset=S) : supports ts xs side=true := by
  obtain ⟨i,hi,cap⟩ := live_capability w side ts ht hs
  apply List.any_eq_true.mpr
  refine ⟨i,?_,cap⟩
  have : i∈xs.toFinset := by rwa [hx]
  simpa using this

def pairStep (next : Nat → List Sig → List PairFlag → List Nat → Bool)
    (q : Nat) (bk : List Sig) (ts : List PairFlag) (xs : List Nat) (g : Gate) : Bool :=
  decide (g.a<g.b) && decide (charge g≤q) && gateAvailable bk (g.kw bk) &&
    options.any fun keepA => options.any fun keepB =>
      next (q-charge g) (bk ++ [g.kw bk]) (ts ++ [g.pair ts])
        (bk.length :: residual xs g.a g.b keepA keepB)

def pairExplore : Nat → Nat → List Sig → List PairFlag → List Nat → Bool
  | 0,_,bk,ts,xs => xs.any fun i =>
      let f := ts.getD i default
      lookupKW bk i == target && f.1.separates && f.2.separates
  | k+1,q,bk,ts,xs =>
    (supports ts xs true && supports ts xs false && admissible (k+1) bk xs) && xs.any fun a => xs.any fun b => options.any fun d =>
      pairStep (pairExplore k) q bk ts xs ⟨d,a,b⟩

theorem pair_complete {k q bk bs S} (w : Walk k q bk bs S)
    (ts : List PairFlag) (htrack : Tracks ts bs) (hsize : ts.length=bk.length) (xs : List Nat)
    (hxs : xs.toFinset=S) : pairExplore k q bk ts xs=true := by
  induction w generalizing xs ts with
  | done q bk bs i orig raised =>
    apply List.any_eq_true.mpr
    have bound := htrack.lookup i 3 raised
    have f1 := bound.1.2 rfl rfl
    have f2 := bound.2.2 rfl rfl
    refine ⟨i,?_,?_⟩
    · have : i∈xs.toFinset := by rw [hxs]; simp
      simpa using this
    · change ((lookupKW bk i == target && (ts.getD i default).1.separates) &&
          (ts.getD i default).2.separates)=true
      rw [orig,f1,f2]
      simp
  | @step k q bk bs U g sorted budget fresh live child ih =>
    rw [pairExplore,Bool.and_eq_true]
    refine ⟨?_,?_⟩
    · simp only [Bool.and_eq_true]
      have here := Walk.step g sorted budget fresh live child
      exact ⟨⟨supports_of_walk here true ts htrack hsize xs hxs,
        supports_of_walk here false ts htrack hsize xs hxs⟩,admissible_of_live (by rwa [hxs])⟩
    · have am : g.a∈xs := by
        have : g.a∈xs.toFinset := by rw [hxs]; simp
        simpa using this
      have bm : g.b∈xs := by
        have : g.b∈xs.toFinset := by rw [hxs]; simp
        simpa using this
      apply List.any_eq_true.mpr
      refine ⟨g.a,am,List.any_eq_true.mpr ⟨g.b,bm,List.any_eq_true.mpr ⟨g.isOr,all_options _,?_⟩⟩⟩
      change pairStep (pairExplore k) q bk ts xs g = true
      simp only [pairStep,sorted,budget,fresh,decide_true,Bool.true_and]
      apply List.any_eq_true.mpr
      refine ⟨decide (g.a∈U),all_options _,List.any_eq_true.mpr ⟨decide (g.b∈U),all_options _,?_⟩⟩
      apply ih _ (htrack.gate g) (by simp [hsize])
      simp [residual_set hxs]

def pairRoot (a b : Nat) (d : Bool) : Bool :=
  pairStep (pairExplore 10) 1 rawKW rawPair (List.range 7) ⟨d,a,b⟩

def pairRow (a : Nat) : Bool := (List.range 7).any fun b => options.any fun d => pairRoot a b d

theorem excluded_of_pair_rows (rows : ∀ a : Fin 7, pairRow a.val=false) :
    ¬ Walk 11 1 rawKW rawLoose (Finset.range 7) := by
  intro walk
  have h := pair_complete walk rawPair raw_tracks (by decide +kernel) (List.range 7) (by decide +kernel)
  change ((supports rawPair (List.range 7) true && supports rawPair (List.range 7) false &&
    admissible 11 rawKW (List.range 7)) && (List.range 7).any pairRow)=true at h
  rw [Bool.and_eq_true] at h
  obtain ⟨a,am,v⟩ := List.any_eq_true.mp h.2
  exact Bool.false_ne_true ((rows ⟨a,List.mem_range.mp am⟩).symm.trans v)

end CoNum4358
