import PEqualNP.CoImplicitBlock4482
namespace CoGroupBlock4482
open CoBitBlock4482 CoBlockIntervals4482 CoImplicitBlock4482

structure Box where
  pos : Bits
  neg : Bits
  changeMask : Bits

structure BCol (k : Nat) where
  box : Box
  inc : BitVec k

def fits (b : Box) (m : Mark) : Bool :=
  (m.1 &&& b.pos == m.1) && (b.neg &&& m.2 == b.neg) &&
    ((m.1 ^^^ m.2) &&& b.changeMask == (m.1 ^^^ m.2))

def exactBox (w : Mark) : Box := ⟨w.1,w.2,w.1 ^^^ w.2⟩

theorem fits_exact (w : Mark) : fits (exactBox w) w=true := by
  simp [fits,exactBox]

private theorem included {a b : Bits} (h : a &&& b=a) (i : Row) :
    bit a i=true → bit b i=true := by
  intro yes
  have q := congrArg (fun z => bit z i) h
  change (a &&& b).getLsbD i.val=a.getLsbD i.val at q
  rw [BitVec.getLsbD_and] at q
  change bit a i && bit b i=bit a i at q
  simpa only [yes,Bool.true_and] using q

theorem fit_facts {b : Box} {w : Mark} (h : fits b w=true) (i : Row) :
    (bit w.1 i=true → bit b.pos i=true) ∧
    (bit b.neg i=true → bit w.2 i=true) ∧
    ((bit w.1 i != bit w.2 i)=true → bit b.changeMask i=true) := by
  simp only [fits,Bool.and_eq_true,beq_iff_eq] at h
  refine ⟨included h.1.1 i,included h.1.2 i,?_⟩
  have d := included h.2 i
  change ((w.1 ^^^ w.2).getLsbD i.val=true → _) at d
  rw [BitVec.getLsbD_xor] at d
  exact d

def condition (need ban member : Bool) := (!need || member) && (!ban || !member)
def laneFor {k} (membership : BitVec k) (need ban : Bool) :=
  (if need then membership else BitVec.allOnes k) &&&
  (if ban then ~~~membership else BitVec.allOnes k)

private theorem laneFor_at {k} (inc : BitVec k) (r s : Bool) (j : Fin k) :
    (laneFor inc r s).getLsbD j.val=condition r s (inc.getLsbD j.val) := by
  cases r <;> cases s <;> simp only [laneFor,condition,ite_true,ite_false,Bool.false_eq_true,
    BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes,j.isLt,decide_true,
    Bool.true_and] <;> cases inc.getLsbD j.val <;> rfl

private theorem weakening {a b c d member : Bool}
    (require : a=true → c=true) (ban : b=true → d=true) :
    condition c d member=true → condition a b member=true := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases member <;> simp_all [condition]

private theorem ban_le {p n P N : Bool} (hp : p=true → P=true) (hn : N=true → n=true) :
    (p && !n)=true → (P && !N)=true := by
  cases p <;> cases n <;> cases P <;> cases N <;> simp_all

def zoneLane {k} (c : BCol k) (e f : Row) :=
  laneFor c.inc (bit c.box.changeMask e || bit c.box.changeMask f)
    (bit c.box.pos e && !bit c.box.neg f)

private theorem zoneLane_le {k} (b : Box) (m : Mark) (inc : BitVec k)
    (h : fits b m=true) (e f : Row) (j : Fin k) :
    (zoneLane ⟨b,inc⟩ e f).getLsbD j.val=true →
    (lane (⟨m,inc⟩ : Col k) e f).getLsbD j.val=true := by
  change (laneFor inc _ _).getLsbD j.val=true →
    (laneFor inc _ _).getLsbD j.val=true
  rw [laneFor_at,laneFor_at]
  apply weakening
  · intro v
    apply Bool.or_eq_true_iff.mpr
    exact (Bool.or_eq_true_iff.mp v).imp (fit_facts h e).2.2 (fit_facts h f).2.2
  · exact ban_le (fit_facts h e).1 (fit_facts h f).2.1

def zone {k} (e f : Row) : List (BCol k) → BitVec k
  | [] => BitVec.allOnes k
  | x::xs => zoneLane x e f &&& zone e f xs

private theorem zone_le {k} {A : Type} (items : List A) (big : A→Box) (real : A→Mark)
    (inc : A→BitVec k) (bounded : ∀x∈items,fits (big x) (real x)=true) (e f : Row) (j : Fin k) :
    (zone e f (items.map (fun x => ⟨big x,inc x⟩))).getLsbD j.val=true →
    (interval e f (items.map (fun x => (⟨real x,inc x⟩ : Col k)))).getLsbD j.val=true := by
  induction items with
  | nil => exact id
  | cons x xs ih =>
    simp only [List.map_cons,zone,interval,BitVec.getLsbD_and,Bool.and_eq_true]
    rintro ⟨a,t⟩
    exact ⟨zoneLane_le _ _ _ (bounded x List.mem_cons_self) e f j a,
      ih (fun y m => bounded y (List.mem_cons_of_mem _ m)) t⟩

def proposeGroup {k} (cols : List (BCol k)) (j : Nat) :=
  let inside := (cols.filter fun w => w.inc.getLsbD j).map fun w => (w.box.pos,w.box.neg)
  let es := cols.foldr (fun w v => if w.inc.getLsbD j then v else v &&& ~~~w.box.changeMask)
    (BitVec.allOnes 258)
  findPair inside es es

def checkGroup {k} (cols : List (BCol k)) : Nat → BitVec k → Bool
  | 0,m => m==0
  | fuel+1,m =>
    if m=0 then true else
    match proposeGroup cols (least m) with
    | none => false
    | some (r,s) => checkGroup cols fuel (m &&& ~~~(zone r s cols))

/-- A shared certificate entails the original interval test for every
individually bounded live state. The Boolean fit test includes an independent
bound on actual edge changes, which can be much tighter than pos XOR neg. -/
theorem for_member {k} {A : Type} (items : List A) (big : A→Box) (real : A→Mark)
    (inc : A→BitVec k) (bounded : ∀x∈items,fits (big x) (real x)=true)
    (fuel : Nat) (m : BitVec k)
    (h : checkGroup (items.map (fun x => ⟨big x,inc x⟩)) fuel m=true) :
    ∃ pairs : List (Row×Row), m &&& cover
      (items.map fun x => (⟨real x,inc x⟩ : Col k)) pairs=m := by
  let cols := items.map (fun x => (⟨big x,inc x⟩ : BCol k))
  change checkGroup cols fuel m=true at h
  induction fuel generalizing m with
  | zero =>
    have off : m=0 := beq_iff_eq.mp h
    exact ⟨[],by simp [off]⟩
  | succ fuel ih =>
    by_cases off : m=0
    · exact ⟨[],by simp [off]⟩
    cases guess : proposeGroup cols (least m) with
    | none => simp only [checkGroup,if_neg off,guess,Bool.false_eq_true] at h
    | some rs =>
      obtain ⟨r,s⟩ := rs
      simp only [checkGroup,if_neg off,guess] at h
      obtain ⟨pairs,ok⟩ := ih _ h
      refine ⟨(r,s)::pairs,?_⟩
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      let realCols := items.map fun x => (⟨real x,inc x⟩ : Col k)
      have le : (zone r s cols).getLsbD j=true → (interval r s realCols).getLsbD j=true :=
        zone_le _ _ _ _ bounded r s ⟨j,hj⟩
      have old := congrArg (fun v : BitVec k => v.getLsbD j) ok
      change (_ &&& cover realCols pairs).getLsbD j=(_ &&& ~~~(zone r s cols)).getLsbD j at old
      change (m &&& cover realCols ((r,s)::pairs)).getLsbD j=m.getLsbD j
      simp only [cover,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,hj,
        decide_true,Bool.true_and] at old ⊢
      cases a : m.getLsbD j <;> cases b : (zone r s cols).getLsbD j <;>
        cases c : (interval r s realCols).getLsbD j <;>
        cases d : (cover realCols pairs).getLsbD j <;> simp_all

#print axioms for_member
end CoGroupBlock4482
