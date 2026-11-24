import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4482_aux

namespace CoPortTrace4482

variable {W X : Type} [DecidableEq W]

def Distinguishes (eval : W → X → Bool) (label : X → Bool) (S : Finset W) : Prop :=
  ∀ x y, label x ≠ label y → ∃ w ∈ S, eval w x ≠ eval w y

inductive Bank (join : Bool → W → W → W) (root : Finset W) : Nat → Finset W → Prop
  | initial : Bank join root 0 root
  | skip {n T} (before : Bank join root n T) : Bank join root (n+1) T
  | gate {n T} (before : Bank join root n T) (d : Bool) (a b : W) (ha : a∈T) (hb : b∈T) :
      Bank join root (n+1) (insert (join d a b) T)

theorem Bank.keeps {join : Bool → W → W → W} {root n T} (b : Bank join root n T) : root⊆T := by
  induction b with
  | initial => exact fun _ h => h
  | skip prev ih => exact ih
  | gate before d a b ha hb ih => exact fun _ h => Finset.mem_insert_of_mem (ih h)

inductive Path (join : Bool → W → W → W) (terminal : Finset W → Prop) : Nat → Finset W → Prop
  | final (S : Finset W) (h : terminal S) : Path join terminal 0 S
  | step {k U} (d : Bool) (a b : W) (ne : a≠b)
      (fresh : join d a b ∉ insert a (insert b U))
      (tail : Path join terminal k (insert (join d a b) U)) :
      Path join terminal (k+1) (insert a (insert b U))

theorem pull {join : Bool → W → W → W} {terminal : Finset W → Prop}
    (idem : ∀ d a, join d a a = a) {root n T} (built : Bank join root n T) :
    ∀ {k S}, S ⊆ T → Path join terminal k S →
      ∃ j ≤ n+k, ∃ A ⊆ root, Path join terminal j A := by
  induction built with
  | initial =>
    intro k S sub tail
    exact ⟨k,by omega,S,sub,tail⟩
  | @skip n T before ih =>
    intro k S sub tail
    obtain ⟨j,hj,A,hA,hp⟩ := ih sub tail
    exact ⟨j,by omega,A,hA,hp⟩
  | @gate n T before d a b ha hb ih =>
    intro k S sub tail
    let z := join d a b
    by_cases old : S ⊆ T
    · obtain ⟨j,hj,A,hA,hp⟩ := ih old tail
      exact ⟨j,by omega,A,hA,hp⟩
    have hz : z∈S := by
      by_contra absent
      apply old
      intro x hx
      rcases Finset.mem_insert.mp (sub hx) with eq|mem
      · apply False.elim
        apply absent
        change join d a b ∈ S
        rw [←eq]
        exact hx
      · exact mem
    have new : z∉T := by
      intro mem
      apply old
      intro x hx
      rcases Finset.mem_insert.mp (sub hx) with h|h
      · exact h.symm ▸ mem
      · exact h
    let U := S.erase z
    have us : U⊆T := by
      intro x hx
      obtain ⟨ne,m⟩ := Finset.mem_erase.mp hx
      exact (Finset.mem_insert.mp (sub m)).resolve_left ne
    have back : insert a (insert b U) ⊆ T := Finset.insert_subset ha (Finset.insert_subset hb us)
    have distinct : a≠b := by
      rintro rfl
      apply new
      change join d a a ∈ T
      rw [idem]
      exact ha
    have fresh : z∉insert a (insert b U) := fun h => new (back h)
    have after : insert z U=S := Finset.insert_erase hz
    have p : Path join terminal (k+1) (insert a (insert b U)) :=
      Path.step d a b distinct fresh (after.symm ▸ tail)
    obtain ⟨j,hj,A,hA,hp⟩ := ih back p
    exact ⟨j,by omega,A,hA,hp⟩

theorem separated {join : Bool → W → W → W} (eval : W → X → Bool) (label : X → Bool)
    (app : ∀ d a b x, eval (join d a b) x =
      if d then eval a x || eval b x else eval a x && eval b x)
    {terminal : Finset W → Prop} (atEnd : ∀ S, terminal S → Distinguishes eval label S)
    {k S} (path : Path join terminal k S) :
    Distinguishes eval label S := by
  induction path with
  | final S h => exact atEnd S h
  | @step k U d a b ne fresh tail ih =>
    intro x y different
    obtain ⟨w,hw,values⟩ := ih x y different
    rcases Finset.mem_insert.mp hw with rfl | h
    · by_cases eq : eval a x = eval a y
      · refine ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),?_⟩
        intro eqb
        exact values (by rw [app,app,eq,eqb])
      · exact ⟨a,Finset.mem_insert_self _ _,eq⟩
    · exact ⟨w,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h),values⟩

end CoPortTrace4482

namespace CoPortTrace4482
variable {W : Type} [DecidableEq W]
variable {join : Bool → W → W → W} {stop : Finset W → Prop}

theorem width {cap : Nat} (terminal : ∀ S,stop S → S.card ≤ cap)
    {k S} (p : Path join stop k S) : S.card ≤ cap+k := by
  induction p with
  | final S h => simpa using terminal S h
  | @step k U d a b ne fresh tail ih =>
    have out : join d a b ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem out] at ih
    have t := Finset.card_insert_le a (insert b U)
    have u := Finset.card_insert_le b U
    omega

def discard (S : Finset W) (v : W) (yes : Bool) := if yes then S.erase v else S

theorem rest_shape (U : Finset W) (a b : W) :
    ∃ da db : Bool, discard (discard (insert a (insert b U)) a da) b db = U := by
  refine ⟨decide (a∉U),decide (b∉U),?_⟩
  ext t
  by_cases ha : a∈U <;> by_cases hb : b∈U <;> by_cases ta : t=a <;> by_cases tb : t=b <;>
    simp_all [discard]

theorem transition {k : Nat} {S : Finset W} (path : Path join stop (k+1) S) :
    ∃ d a b da db, a∈S ∧ b∈S ∧ a≠b ∧ join d a b∉S ∧
      Path join stop k (insert (join d a b) (discard (discard S a da) b db)) := by
  cases path with
  | @step _ U d a b ne fresh tail =>
    obtain ⟨da,db,eq⟩ := rest_shape U a b
    exact ⟨d,a,b,da,db,Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      ne,fresh,by rw [eq];exact tail⟩

end CoPortTrace4482

namespace CoTightBlocks4482
open CoPortTrace4482
variable {W X : Type} [DecidableEq W]

structure Blocks (ev : W → X → Bool) (S T : Finset W) where
  owner : W → W
  lands : ∀ w∈S, owner w∈T
  onto : ∀ t∈T, ∃ w∈S, owner w=t
  mono : ∀ t∈T, ∀ p n : X,
    (∀ w∈S, owner w=t → ev w p=true → ev w n=true) → ev t p=true → ev t n=true

theorem partition {join : Bool → W → W → W} {stop : Finset W → Prop}
    (ev : W → X → Bool) (app : ∀ d a b x, ev (join d a b) x =
      if d then ev a x || ev b x else ev a x && ev b x)
    (cap : Nat) (terminal : ∀ T, stop T → T.card≤cap)
    {k S} (run : Path join stop k S) (tight : S.card=cap+k) :
    ∃ T, stop T ∧ T.card=cap ∧ Nonempty (Blocks ev S T) := by
  induction run with
  | final S h =>
    refine ⟨S,h,by simpa using tight,⟨⟨id,fun _ m => m,fun t m => ⟨t,m,rfl⟩,?_⟩⟩⟩
    intro t ht p n h yes
    exact h t ht rfl yes
  | @step k U d a b ab fresh tail ih =>
    let z := join d a b
    have hz : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have up := width terminal tail
    change (insert z U).card≤cap+k at up
    have zsize := Finset.card_insert_of_notMem hz
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    have tailSize : (insert z U).card=cap+k := by omega
    have absentA : a∉insert b U := by
      intro m
      rw [Finset.insert_eq_of_mem m] at tight
      omega
    have absentB : b∉U := by
      intro m
      rw [Finset.insert_eq_of_mem m] at tight
      have q := Finset.card_insert_le a U
      omega
    obtain ⟨T,st,sz,⟨B⟩⟩ := ih tailSize
    let owner := fun w : W => if w=a ∨ w=b then B.owner z else B.owner w
    have old {w : W} (m : w∈U) : owner w=B.owner w := by
      have na : w≠a := by rintro rfl; exact absentA (Finset.mem_insert_of_mem m)
      have nb : w≠b := by rintro rfl; exact absentB m
      simp [owner,na,nb]
    have oa : owner a=B.owner z := by simp [owner]
    have ob : owner b=B.owner z := by simp [owner]
    have ma : a∈insert a (insert b U) := Finset.mem_insert_self _ _
    have mb : b∈insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have inc {w : W} (m : w∈U) : w∈insert a (insert b U) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)
    refine ⟨T,st,sz,⟨⟨owner,?_,?_,?_⟩⟩⟩
    · intro w mw
      rcases Finset.mem_insert.mp mw with rfl|mw
      · rw [oa]; exact B.lands _ (Finset.mem_insert_self _ _)
      rcases Finset.mem_insert.mp mw with rfl|mw
      · rw [ob]; exact B.lands _ (Finset.mem_insert_self _ _)
      rw [old mw]
      exact B.lands _ (Finset.mem_insert_of_mem mw)
    · intro t ht
      obtain ⟨w,m,e⟩ := B.onto t ht
      rcases Finset.mem_insert.mp m with rfl|mw
      · exact ⟨a,ma,oa.trans e⟩
      · exact ⟨w,inc mw,(old mw).trans e⟩
    · intro t ht p n order
      apply B.mono t ht p n
      intro w m e
      rcases Finset.mem_insert.mp m with rfl|mw
      · have ao := order a ma (oa.trans e)
        have bo := order b mb (ob.trans e)
        change ev (join d a b) p=true → ev (join d a b) n=true
        rw [app,app]
        cases d <;> simp only [↓reduceIte,Bool.false_eq_true,Bool.and_eq_true,Bool.or_eq_true]
        · exact fun h => ⟨ao h.1,bo h.2⟩
        · exact fun h => h.imp ao bo
      · exact order w (inc mw) ((old mw).trans e)

def exclusive {ev : W → X → Bool} {S T} (B : Blocks ev S T) (t : W) (lo hi : X) :=
  ∀ w∈S, B.owner w≠t → ev w lo=ev w hi

theorem priceEdge {ev : W → X → Bool} {S T} (B : Blocks ev S T) {t : W} {lo hi : X}
    (exclusiveTo : exclusive B t lo hi) (ordered : ∀ w∈S, ev w lo=true → ev w hi=true)
    (dist : ∃ z∈T, ev z lo≠ev z hi) : ev t lo=false ∧ ev t hi=true := by
  obtain ⟨z,m,diff⟩ := dist
  have zt : z=t := by
    by_contra n
    have back := B.mono z m hi lo (by
      intro w h owner up
      have no : B.owner w≠t := fun e => n (owner.symm.trans e)
      rw [exclusiveTo w h no]
      exact up)
    have front := B.mono z m lo hi (fun w h _ => ordered w h)
    cases a : ev z lo <;> cases b : ev z hi <;> simp_all
  subst t
  have f := B.mono z m lo hi (fun w h _ => ordered w h)
  cases a : ev z lo <;> cases b : ev z hi <;> simp_all

theorem block_obstruction {ev : W → X → Bool} {S T} (B : Blocks ev S T) {t : W} (ht : t∈T)
    {lo hi lo' hi' : X} (one : exclusive B t lo hi) (two : exclusive B t lo' hi')
    (or1 : ∀ w∈S, ev w lo=true → ev w hi=true) (or2 : ∀ w∈S, ev w lo'=true → ev w hi'=true)
    (d1 : ∃ z∈T, ev z lo≠ev z hi) (d2 : ∃ z∈T, ev z lo'≠ev z hi') :
    ∃ w∈S, B.owner w=t ∧ ev w hi=true ∧ ev w lo'=false := by
  have p := (priceEdge B one or1 d1).2
  have n := (priceEdge B two or2 d2).1
  by_contra absent
  have pos := B.mono t ht hi lo' (by
    intro w m o yes
    cases e : ev w lo' with
    | false => exact (absent ⟨w,m,o,yes,e⟩).elim
    | true => rfl) p
  rw [n] at pos
  contradiction

end CoTightBlocks4482

namespace CoBitBlock4482

abbrev Bits := BitVec 258
abbrev Row := Fin 258
abbrev Mark := Bits × Bits
def bit (x : Bits) (i : Row) := x.getLsbD i.val
def avoid (z : Mark) (e : Bits) : Bits := e &&& ~~~(z.1 ^^^ z.2)
def exclusive (others : List Mark) : Bits := others.foldr avoid (BitVec.allOnes 258)

def bad : List Mark → Bits → Bits → Bool
  | [],p,n => p != 0 && n != 0
  | w::ws,p,n => if p=0 ∨ n=0 then false else
      bad ws (p &&& ~~~w.1) n || bad ws (p &&& w.1) (n &&& w.2)

def invalid (inside outside : List Mark) :=
  let es := exclusive outside
  bad inside es es

private theorem has_bit {w : Bits} (ne : w ≠ 0) : ∃ i : Row, bit w i=true := by
  by_contra no
  apply ne
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases e : w.getLsbD i with
  | false => simp
  | true => exact (no ⟨⟨i,hi⟩,e⟩).elim

private theorem bit_and (a b : Bits) (i : Row) : bit (a &&& b) i = (bit a i && bit b i) := by
  simp only [bit,BitVec.getLsbD_and]

private theorem bit_not (a : Bits) (i : Row) : bit (~~~a) i = !(bit a i) := by
  simp only [bit,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]

private theorem bit_xor (a b : Bits) (i : Row) : bit (a ^^^ b) i = (Bool.xor (bit a i) (bit b i)) := by
  simp only [bit,BitVec.getLsbD_xor]

theorem bad_witness (ws : List Mark) (p n : Bits) (h : bad ws p n=true) :
    ∃ i j : Row, bit p i=true ∧ bit n j=true ∧
      ∀ w∈ws, bit w.1 i=true → bit w.2 j=true := by
  induction ws generalizing p n with
  | nil =>
    simp only [bad,Bool.and_eq_true,bne_iff_ne] at h
    obtain ⟨i,pi⟩ := has_bit h.1
    obtain ⟨j,nj⟩ := has_bit h.2
    exact ⟨i,j,pi,nj,by simp⟩
  | cons w ws ih =>
    by_cases stop : p=0 ∨ n=0
    · simp only [bad,if_pos stop,Bool.false_eq_true] at h
    simp only [bad,if_neg stop,Bool.or_eq_true] at h
    rcases h with l|r
    · obtain ⟨i,j,pi,nj,inside⟩ := ih _ _ l
      rw [bit_and,bit_not,Bool.and_eq_true] at pi
      refine ⟨i,j,pi.1,nj,?_⟩
      intro a m t
      rcases List.mem_cons.mp m with rfl|m
      · simp [t] at pi
      · exact inside a m t
    · obtain ⟨i,j,pi,nj,inside⟩ := ih _ _ r
      rw [bit_and,Bool.and_eq_true] at pi nj
      refine ⟨i,j,pi.1,nj.1,?_⟩
      intro a m t
      rcases List.mem_cons.mp m with rfl|m
      · exact nj.2
      · exact inside a m t

theorem outside_equal (others : List Mark) (i : Row) (h : bit (exclusive others) i=true) :
    ∀ w∈others, bit w.1 i = bit w.2 i := by
  induction others with
  | nil => simp
  | cons a others ih =>
    change bit (avoid a (exclusive others)) i=true at h
    rw [avoid,bit_and,bit_not,bit_xor,Bool.and_eq_true] at h
    intro w m
    rcases List.mem_cons.mp m with eq|m
    · subst w
      cases l : bit a.1 i <;> cases r : bit a.2 i <;> simp_all
    · exact ih h.1 w m

theorem invalid_witness (inside outside : List Mark) (h : invalid inside outside=true) :
    ∃ i j : Row, (∀ w∈outside, bit w.1 i=bit w.2 i ∧ bit w.1 j=bit w.2 j) ∧
      ∀ w∈inside, bit w.1 i=true → bit w.2 j=true := by
  obtain ⟨i,j,pi,nj,order⟩ := bad_witness _ _ _ h
  exact ⟨i,j,fun w m => ⟨outside_equal outside i pi w m,outside_equal outside j nj w m⟩,order⟩

end CoBitBlock4482

namespace CoJunctionCost4482
open CoBitBlock4482

abbrev W := BitVec 512
abbrev Pin := W × Mark
structure Choice where
  a : Nat
  b : Nat
  op : Bool
  drop : Nat

def code (c : Choice) := ((16*c.a+c.b)*2+(if c.op then 1 else 0))*4+c.drop
def wireGate {n} (op : Bool) (a b : BitVec n) := if op then a ||| b else a &&& b
def delta (m : Mark) := m.1 ^^^ m.2

def rest (ws : List Pin) (a b : Nat) : Bits :=
  ws.zipIdx.foldl (fun acc p =>
    if p.2=a ∨ p.2=b then acc else acc ||| delta p.1.2) 0

def choices (ws : List Pin) (k : Nat) : List Choice :=
  let n := ws.length
  (List.range n).flatMap fun i => (List.range n).flatMap fun j =>
    if i≥j then [] else
    let a := ws.getD i (0,(0,0))
    let b := ws.getD j (0,(0,0))
    let keep := rest ws i j
    [false,true].flatMap fun d =>
      let full := wireGate d a.1 b.1
      if ws.any (fun w => w.1==full) then [] else
      let keepGate := keep ||| (wireGate d a.2.1 b.2.1 ^^^ wireGate d a.2.2 b.2.2)
      (List.range 4).filterMap fun drop =>
        let da := drop.testBit 0
        let db := drop.testBit 1
        let wid := n+1-(if da then 1 else 0)-(if db then 1 else 0)
        let cov := keepGate ||| (if da then 0 else delta a.2) ||| (if db then 0 else delta b.2)
        if wid≤6+(k-1) ∧ cov=BitVec.allOnes 258 then some ⟨i,j,d,drop⟩ else none

def toWords (before : List W) (c : Choice) : List W :=
  wireGate c.op (before.getD c.a 0) (before.getD c.b 0) ::
    (before.zipIdx.filter (fun w =>
      !((w.2==c.a && c.drop.testBit 0) || (w.2==c.b && c.drop.testBit 1)))).map Prod.fst

def sameSet (xs ys : List W) := xs.all ys.contains && ys.all xs.contains

def routes (transport target : Nat → List W) : List Choice → List (Nat×Nat×Nat) → Bool
  | [],[] => true
  | c::cs,(id,t,g)::rs => code c==id && sameSet (toWords (transport g) c) (target t) &&
    routes transport target cs rs
  | _,_ => false
end CoJunctionCost4482

namespace CoJunctionFixed4482

structure Column where
  width : Nat
  blocks : Array Nat

def field (c : Column) (i : Nat) : Nat :=
  (((c.blocks[i/64]?).getD 0) >>> ((i % 64)*c.width)) % 2^c.width

structure Graph where
  size : Nat
  idBits : Nat
  offsetBits : Nat
  runCount : Nat
  internalCount : Nat
  rows : Column
  actions : Column
  parentRuns : Column
  exitRuns : Column
  arcs : Column

def lowerBound (key : Nat→Nat) (x : Nat) : Nat → Nat → Nat → Nat
  | 0,lo,_ => lo
  | f+1,lo,hi =>
    if lo≥hi then lo else
    let m := (lo+hi)/2
    if key m < x then lowerBound key x f (m+1) hi else lowerBound key x f lo m

def lookupBound (key : Nat→Nat) (n x : Nat) :=
  lowerBound key x ((n+1).log2+2) 0 n

def budget (h : Graph) (i : Nat) := (field h.rows i) % 8
def leafCode (h : Graph) (i : Nat) := (field h.rows i)/8

def parent (h : Graph) (i : Nat) :=
  let pos := lookupBound (fun j => (field h.parentRuns j) >>> h.idBits) h.runCount i
  (field h.parentRuns pos) % 2^h.idBits

def firstAction (h : Graph) (i : Nat) := field h.actions (i-1)

def exits (h : Graph) (i : Nat) : Nat×Nat :=
  let pos := lookupBound (fun j => (field h.exitRuns j) >>> h.offsetBits) h.internalCount i
  let last := field h.exitRuns pos
  if pos≥h.internalCount ∨ last >>> h.offsetBits ≠ i then (0,0) else
    (if pos=0 then 0 else (field h.exitRuns (pos-1)) % 2^h.offsetBits,last % 2^h.offsetBits)

def references (h : Graph) (i : Nat) : List (Nat×Nat) :=
  let (start,stop) := exits h i
  (List.range (stop-start)).map fun d =>
    let v := field h.arcs (start+d)
    (v/16,v % 16)

end CoJunctionFixed4482

namespace CoPortBank4482
open PEqualNP.CircuitLowerBounds CoPortTrace4482

structure Model (W X : Type) where
  zero : W
  one : W
  join : Bool → W → W → W
  val : W → X → Bool
  atZero : ∀ x, val zero x = false
  atOne : ∀ x, val one x = true
  applyJoin : ∀ d a b x, val (join d a b) x =
    if d then val a x || val b x else val a x && val b x

variable {W X : Type} [DecidableEq W] (M : Model W X)

def mode (g : Gate) : Bool := g.op.eval [true,false]

def operand (ws : List W) (g : Gate) (pin : Nat) : W :=
  match g.inputs[pin]? with
  | some j => ws.getD j M.zero
  | none => if mode g then M.zero else M.one

def value (ws : List W) (g : Gate) : W :=
  M.join (mode g) (operand M ws g 0) (operand M ws g 1)

def write (ws : List W) (g : Gate) := ws ++ [value M ws g]

def history (ws : List W) (gs : List Gate) := gs.foldl (write M) ws

def Covers (T : Finset W) (ws : List W) := ∀ w∈ws, w∈T

theorem read_mem {ws : List W} {T : Finset W} (cov : Covers T ws)
    (zero : M.zero∈T) (j : Nat) : ws.getD j M.zero∈T := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[j]? with
  | none => exact zero
  | some w => exact cov w (List.mem_of_getElem? h)

private theorem operand_mem {ws : List W} {T : Finset W} (cov : Covers T ws)
    (zero : M.zero∈T) (one : M.one∈T) (g : Gate) (i) : operand M ws g i∈T := by
  cases h : g.inputs[i]? with
  | none =>
    simp only [operand,h]
    split <;> assumption
  | some j => simpa only [operand,h] using read_mem M cov zero j

theorem bank (gs : List Gate) {root T n ws} (zero : M.zero∈T) (one : M.one∈T)
    (cov : Covers T ws) (before : Bank M.join root n T) :
    ∃ T', Bank M.join root (n+gs.length) T' ∧ Covers T' (history M ws gs) := by
  induction gs generalizing T n ws with
  | nil => exact ⟨T,by simpa using before,cov⟩
  | cons g gs ih =>
    let z := value M ws g
    have hz : Bank M.join root (n+1) (insert z T) :=
      Bank.gate before (mode g) _ _ (operand_mem M cov zero one g 0) (operand_mem M cov zero one g 1)
    have next : Covers (insert z T) (write M ws g) := by
      intro w hw
      rcases List.mem_append.mp hw with h|h
      · exact Finset.mem_insert_of_mem (cov w h)
      · have eq : w=z := List.mem_singleton.mp h
        exact eq.symm ▸ Finset.mem_insert_self z T
    obtain ⟨P,hP,covered⟩ := ih (Finset.mem_insert_of_mem zero) (Finset.mem_insert_of_mem one) next hz
    exact ⟨P,by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hP,covered⟩

theorem read_values (ws : List W) (x : X) (i : Nat) :
    (ws.map fun w => M.val w x).getD i false = M.val (ws.getD i M.zero) x := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact (M.atZero x).symm
  | some w => rfl

private theorem read_option (ws : List W) (x : X) (j : Nat) :
    (ws[j]?.map (fun w => M.val w x)).getD false = M.val (ws[j]?.getD M.zero) x := by
  cases h : ws[j]? with
  | none => exact (M.atZero x).symm
  | some w => rfl

theorem correct_gate (ws : List W) (g : Gate) (x : X)
    (op : g.op=.and ∨ g.op=.or) (arity : g.inputs.length≤2) :
    M.val (value M ws g) x =
      g.op.eval (g.inputs.map fun j => (ws.map fun w => M.val w x).getD j false) := by
  rcases g with ⟨kind,ids⟩
  change kind=.and ∨ kind=.or at op
  change ids.length≤2 at arity
  rcases op with eq|eq <;> subst kind
  all_goals
    rcases ids with _|⟨a,as⟩
    · simp [value,operand,mode,GateOp.eval,M.applyJoin,M.atZero,M.atOne]
    · rcases as with _|⟨b,bs⟩
      · simp [value,operand,mode,GateOp.eval,M.applyJoin,M.atZero,M.atOne,read_option]
      · rcases bs with _|⟨c,cs⟩
        · simp [value,operand,mode,GateOp.eval,M.applyJoin,M.atZero,M.atOne,read_option]
        · simp at arity

theorem correct (gs : List Gate) (ws : List W) (x : X)
    (valid : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    (history M ws gs).map (fun w => M.val w x) =
      gs.foldl (fun wires g => wires++[g.op.eval (g.inputs.map (fun i => wires.getD i false))])
        (ws.map fun w => M.val w x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have legal := valid g List.mem_cons_self
    have rest := ih (write M ws g) (fun a ha => valid a (List.mem_cons_of_mem _ ha))
    change (history M (write M ws g) gs).map _ = _
    rw [rest]
    simp only [write,List.map_append,List.map_cons,List.map_nil,correct_gate M ws g x legal.1 legal.2,
      List.foldl_cons]

end CoPortBank4482

namespace CoPortCut4482
open CoPortBank4482 CoPortTrace4482 PEqualNP.CircuitLowerBounds

variable {W X : Type} [DecidableEq W]

theorem avoid {join : Bool → W → W → W} {stop : Finset W → Prop} {c : W}
    (dead : ∀ d a b, a=c ∨ b=c → join d a b=a ∨ join d a b=b)
    (atEnd : ∀ S, stop S → c∉S) {k S} (p : Path join stop k S) : c∉S := by
  induction p with
  | final S h => exact atEnd S h
  | @step k U d a b ne fresh tail ih =>
    intro hc
    rcases Finset.mem_insert.mp hc with same|rest
    · rcases dead d a b (Or.inl same.symm) with ea|eb
      · exact fresh (ea.symm ▸ Finset.mem_insert_self _ _)
      · exact fresh (eb.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    · rcases Finset.mem_insert.mp rest with same|old
      · rcases dead d a b (Or.inr same.symm) with ea|eb
        · exact fresh (ea.symm ▸ Finset.mem_insert_self _ _)
        · exact fresh (eb.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      · exact ih (Finset.mem_insert_of_mem old)

def cleanCut (M : Model W X) (label : X → Bool) (limit : Nat) (S : Finset W) : Prop :=
  S.card≤limit ∧ Distinguishes M.val label S ∧ M.zero∉S ∧ M.one∉S

theorem observation {M : Model W X} (label : X → Bool) (limit : Nat)
    {n : Nat} {root last : Finset W} (history : Bank M.join root n last)
    (idem : ∀ d a, M.join d a a=a) (word : Nat → W) (O : Finset Nat)
    (cap : O.card≤limit) (sound : ∀ i∈O, word i∈last)
    (detect : ∀ x y, label x ≠ label y → ∃ i∈O, M.val (word i) x ≠ M.val (word i) y) :
    ∃ j ≤ n, ∃ A ⊆ root, Path M.join (cleanCut M label limit) j A := by
  let S := (O.image word).filter fun w => w≠M.zero ∧ w≠M.one
  have sub : S⊆last := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hw).1
    exact sound i hi
  have card : S.card≤limit := (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans cap)
  have dist : Distinguishes M.val label S := by
    intro x y ne
    obtain ⟨i,hi,d⟩ := detect x y ne
    have h0 : word i ≠ M.zero := by
      intro e
      exact d (by rw [e,M.atZero,M.atZero])
    have h1 : word i ≠ M.one := by
      intro e
      exact d (by rw [e,M.atOne,M.atOne])
    exact ⟨word i,Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hi,h0,h1⟩,d⟩
  have stop : cleanCut M label limit S :=
    ⟨card,dist,fun h => (Finset.mem_filter.mp h).2.1 rfl,fun h => (Finset.mem_filter.mp h).2.2 rfl⟩
  simpa only [Nat.add_zero] using pull idem history sub (Path.final S stop)

end CoPortCut4482

namespace CoPortRoots4482
open CoPortBank4482 CoPortCut4482 CoPortTrace4482 PEqualNP.CircuitLowerBounds

abbrev W := BitVec 512
abbrev R := Fin 512
abbrev Input := Fin 9 → Bool

def raw : Fin 9 → W := ![
  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def seed : W := raw 0 ||| raw 2
def raws : List W := List.ofFn raw
def init : List W := raws++[seed]
def top : W := BitVec.allOnes 512
def roots : Finset W := insert 0 (insert top init.toFinset)
def cell (w : W) (r : R) := w.getLsbD r.val
def row (r : R) : Input := fun j => cell (raw j) r
def graph (x : Input) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any fun e =>
  x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10))
def label (r : R) := graph (row r)

def join (d : Bool) (a b : W) : W := if d then a ||| b else a &&& b

def model : Model W R where
  zero := 0
  one := top
  join := join
  val := cell
  atZero := by intro r; simp [cell]
  atOne := by intro r; simp only [cell,top,BitVec.getLsbD_allOnes,r.isLt,decide_true]
  applyJoin := by intro d a b r; cases d <;> simp [join,cell,BitVec.getLsbD_or,BitVec.getLsbD_and]

def lo : Fin 9 → R := ![20,1,9,4,1,1,2,4,8]
def hi : Fin 9 → R := ![21,3,13,12,17,33,66,132,264]

private theorem critical : ∀ i : Fin 9, label (lo i) ≠ label (hi i) ∧
    ((0::top::init).all fun w => w==raw i || cell w (lo i)==cell w (hi i))=true := by
  decide +kernel

private theorem necessary {A : Finset W} (sub : A⊆roots) (d : Distinguishes cell label A) :
    raws.toFinset ⊆ A := by
  intro w hw
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hw)
  obtain ⟨z,hz,ne⟩ := d _ _ (critical j).1
  have mem : z∈0::top::init := by
    simpa only [roots,Finset.mem_insert,List.mem_toFinset,List.mem_cons] using sub hz
  have or := List.all_eq_true.mp (critical j).2 z mem
  simp only [Bool.or_eq_true] at or
  rcases or with eq|bad
  · exact (beq_iff_eq.mp eq) ▸ hz
  · exact (ne (beq_iff_eq.mp bad)).elim

theorem only_roots {k A} (sub : A⊆roots) (path : Path join (cleanCut model label 6) k A) :
    A=raws.toFinset ∨ A=init.toFinset := by
  have d := separated cell label model.applyJoin (fun _ h => h.2.1) path
  have lower := necessary sub d
  have z : (0 : W)∉A := avoid (c:=(0:W)) (by
    intro d a b eq
    rcases eq with rfl|rfl <;> cases d <;> simp [join]) (fun _ h => h.2.2.1) path
  have o : top∉A := avoid (c:=top) (by
    intro d a b eq
    rcases eq with rfl|rfl <;> cases d
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [join,Bool.false_eq_true,↓reduceIte,ite_false,top,BitVec.getLsbD_and,BitVec.getLsbD_allOnes,hi,decide_true,Bool.true_and]
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [join,ite_true,top,BitVec.getLsbD_or,BitVec.getLsbD_allOnes,hi,decide_true,Bool.true_or]
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [join,Bool.false_eq_true,↓reduceIte,ite_false,top,BitVec.getLsbD_and,BitVec.getLsbD_allOnes,hi,decide_true,Bool.and_true]
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [join,ite_true,top,BitVec.getLsbD_or,BitVec.getLsbD_allOnes,hi,decide_true,Bool.or_true]) (fun _ h => h.2.2.2) path
  have upper : A⊆init.toFinset := by
    intro a ha
    rcases Finset.mem_insert.mp (sub ha) with rfl|rest
    · exact (z ha).elim
    rcases Finset.mem_insert.mp rest with rfl|h
    · exact (o ha).elim
    · exact h
  by_cases keep : seed∈A
  · right
    apply Finset.Subset.antisymm upper
    intro w hw
    rcases List.mem_append.mp (List.mem_toFinset.mp hw) with r|s
    · exact lower (List.mem_toFinset.mpr r)
    · exact (List.mem_singleton.mp s).symm ▸ keep
  · left
    apply Finset.Subset.antisymm _ lower
    intro w hw
    rcases List.mem_append.mp (List.mem_toFinset.mp (upper hw)) with r|s
    · exact List.mem_toFinset.mpr r
    · exact (keep (List.mem_singleton.mp s ▸ hw)).elim

end CoPortRoots4482

namespace CoBlockIntervals4482
open CoBitBlock4482

structure Col (k : Nat) where
  data : Mark
  inc : BitVec k

def lane {k} (d : Col k) (e f : Row) : BitVec k :=
  let A := bit d.data.1 e
  let B := bit d.data.2 e
  let C := bit d.data.1 f
  let D := bit d.data.2 f
  (if A != B || C != D then d.inc else BitVec.allOnes k) &&&
    (if A && !D then ~~~d.inc else BitVec.allOnes k)

def interval {k} (e f : Row) : List (Col k) → BitVec k
  | [] => BitVec.allOnes k
  | h::t => lane h e f &&& interval e f t

def cover {k} (cols : List (Col k)) : List (Row×Row) → BitVec k
  | [] => 0
  | h::t => interval h.1 h.2 cols ||| cover cols t

private theorem lane_bit {k} (x : Col k) (e f : Row) (j : Fin k) :
    (lane x e f).getLsbD j.val = (
      (!(bit x.data.1 e != bit x.data.2 e || bit x.data.1 f != bit x.data.2 f) ||
        x.inc.getLsbD j.val) &&
      (!(bit x.data.1 e && !(bit x.data.2 f)) || !(x.inc.getLsbD j.val))) := by
  unfold lane
  cases a : (bit x.data.1 e != bit x.data.2 e || bit x.data.1 f != bit x.data.2 f) <;>
    cases b : (bit x.data.1 e && !bit x.data.2 f) <;>
    simp only [a,b,ite_true,ite_false,Bool.false_eq_true,BitVec.getLsbD_and,
      BitVec.getLsbD_not,BitVec.getLsbD_allOnes,j.isLt,decide_true,Bool.true_and] <;>
    cases x.inc.getLsbD j.val <;> rfl

private theorem local_sound {a b c d x : Bool}
    (ok : ((!(a != b || c != d) || x) && (!(a && !d) || !x))=true) :
    (x=false → a=b ∧ c=d) ∧ (x=true → a=true → d=true) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> simp_all

theorem interval_sound {k} (e f : Row) (cols : List (Col k)) (j : Fin k)
    (hit : (interval e f cols).getLsbD j.val = true) : ∀ w∈cols,
      (w.inc.getLsbD j.val=false → bit w.data.1 e=bit w.data.2 e ∧
        bit w.data.1 f=bit w.data.2 f) ∧
      (w.inc.getLsbD j.val=true → bit w.data.1 e=true → bit w.data.2 f=true) := by
  induction cols with
  | nil => simp
  | cons a xs ih =>
    simp only [interval,BitVec.getLsbD_and,Bool.and_eq_true] at hit
    intro w hw
    rcases List.mem_cons.mp hw with rfl|m
    · exact local_sound (by rw [←lane_bit]; exact hit.1)
    · exact ih hit.2 w m

theorem cover_witness {k} (cols : List (Col k)) (pairs : List (Row×Row)) (j : Fin k)
    (hit : (cover cols pairs).getLsbD j.val=true) :
    ∃ e f : Row, ∀ w∈cols,
      (w.inc.getLsbD j.val=false → bit w.data.1 e=bit w.data.2 e ∧
        bit w.data.1 f=bit w.data.2 f) ∧
      (w.inc.getLsbD j.val=true → bit w.data.1 e=true → bit w.data.2 f=true) := by
  induction pairs with
  | nil => simp [cover] at hit
  | cons a t ih =>
    simp only [cover,BitVec.getLsbD_or,Bool.or_eq_true] at hit
    rcases hit with v|v
    · exact ⟨a.1,a.2,interval_sound _ _ _ _ v⟩
    · exact ih v

theorem required_witness {k} (cols : List (Col k)) (pairs : List (Row×Row)) (must : BitVec k)
    (verified : must &&& cover cols pairs = must) (j : Fin k) (demand : must.getLsbD j.val=true) :
    ∃e f : Row, ∀w∈cols,
      (w.inc.getLsbD j.val=false → bit w.data.1 e=bit w.data.2 e ∧
        bit w.data.1 f=bit w.data.2 f) ∧
      (w.inc.getLsbD j.val=true → bit w.data.1 e=true → bit w.data.2 f=true) := by
  have eq := congrArg (fun s : BitVec k => s.getLsbD j.val) verified
  simp only [BitVec.getLsbD_and,demand,Bool.true_and] at eq
  exact cover_witness _ _ j eq

end CoBlockIntervals4482

namespace CoPortEdgeRows4482
open CoPortRoots4482 CoPortTrace4482 CoPortCut4482 CoBitBlock4482

def lowCodes : Nat := 0x32592c964b2590c86432190c160b0582c16070381c0e070380c060301148a45229148a44a25128944a2110884420b0582c160b058241209048240a05028140a030180c06030080401a0d068341a0d064b2592c964b2190c86432182c160b0582c060301809249249249248241209045229148a45229128944a25128844221108241209048140a050280401d0e8743a1d0e070381c0e068341a0d06834190c86432190c06030180a8542a150a85028140a049249249249241209048229148a452291488442211082412090480401a0d068341a0c86432190c86430180c0602a150a8542a150a05028140a048241209048221108844221008040140a050281209048241008028140a050281209048241208040200a05028140a04020100402010040201
def highCodes : Nat := 0x3a5b2cd65b27d0d86632991e168b1586c1f074391c4e1707c0d06230994aa4d239168ad4a651a8b44ea1308c4470b4592c561b07c2512490c8350a450a8340e832188c26074090423a0f06c351a4d1e4ba5b2cd65f21d0d86632b82e168b1587c07031184d2592692c93582612891c5329549a4722f12a94ca3517885426118c25121906a148a1506a0425d1e87c3b1d6e0f03c1c8e368741e0d86a34d91c86c33196c0e031186a8d42e158ab502c148a349349649a4ba4160984aa2b14ca552691e88c42611a82612890e80429a2d078361acc964721d0d86730580e0632a551a8742e15ca15038160a648a4160984b22511884c239028042940e0582a520d058261808c28941a0702e12290c83417080c0310a250a8340e84060188406018842203
def endpoint (codes : Nat) (i : Row) : R :=
  ⟨(codes >>> (9*i.val)) % 512,Nat.mod_lt _ (by decide)⟩
def lower := endpoint lowCodes
def upper := endpoint highCodes
def flips : Nat := 0x653206532065320654321653276531065320653076543176531653206543165385321085421854218542185216532053208654208542185426520542152873108731087421087310871087310831085421842187543187318541818731087632087308764208742087310876208707310632030864208542184275431731620541
def flipped (i : Row) : Fin 9 := ⟨((flips >>> (4*i.val)) % 16) % 9,Nat.mod_lt _ (by decide)⟩

theorem one_flip : ∀ i : Row, (lower i).val.testBit (flipped i).val=false ∧
    (upper i).val=(lower i).val ||| 2^(flipped i).val := by decide +kernel

theorem labels : ∀ i : Row, label (lower i)=false ∧ label (upper i)=true := by decide +kernel
theorem raw_order : ∀ t : Fin 9, ∀ i : Row,
    cell (raw t) (lower i)=true → cell (raw t) (upper i)=true := by decide +kernel

def project (r : Row → R) (w : W) : Bits :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => cell w (r i)))).cast List.length_ofFn

theorem projected (r : Row → R) (w : W) (i : Row) :
    bit (project r w) i=cell w (r i) := by
  simp only [bit,project,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

def mark (w : W) : Mark := (project upper w,project lower w)
theorem positive (w : W) (i : Row) : bit (mark w).1 i=cell w (upper i) := projected _ _ _
theorem negative (w : W) (i : Row) : bit (mark w).2 i=cell w (lower i) := projected _ _ _

theorem difference (w : W) (i : Row) :
    ((mark w).1 ^^^ (mark w).2).getLsbD i.val =
      (cell w (upper i) != cell w (lower i)) := by
  rw [BitVec.getLsbD_xor]
  change Bool.xor (bit (mark w).1 i) (bit (mark w).2 i)=_
  rw [positive,negative]

private theorem proj_gate (r : Row→R) (d : Bool) (a b : W) :
    project r (join d a b)=if d then project r a ||| project r b else project r a &&& project r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Row := ⟨j,hj⟩
  have V (w : W) : (project r w).getLsbD j=cell w (r i) := projected r w i
  cases d <;> simp only [Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,BitVec.getLsbD_or,V,
    join,cell]

theorem mark_gate (d : Bool) (a b : W) : mark (join d a b)=
    if d then ((mark a).1 ||| (mark b).1,(mark a).2 ||| (mark b).2)
      else ((mark a).1 &&& (mark b).1,(mark a).2 &&& (mark b).2) := by
  cases d <;> simp only [mark,proj_gate,Bool.false_eq_true,↓reduceIte]

def Ordered (w : W) := ∀ i : Row,cell w (lower i)=true → cell w (upper i)=true

theorem join_ordered (d : Bool) {a b : W} (A : Ordered a) (B : Ordered b) :
    Ordered (join d a b) := by
  intro i
  cases d <;> simp only [join,cell,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,
    BitVec.getLsbD_or,Bool.and_eq_true,Bool.or_eq_true]
  · exact fun h => ⟨A i h.1,B i h.2⟩
  · exact fun h => h.imp (A i) (B i)

theorem start_ordered {w : W} (h : w∈init) : Ordered w := by
  change w∈raws++[seed] at h
  rcases List.mem_append.mp h with hr|hs
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact raw_order i
  · have e : w=seed := List.mem_singleton.mp hs
    rw [e]
    exact join_ordered true (raw_order 0) (raw_order 2)

theorem terminal_dist (S : Finset W) (finish : cleanCut model label 6 S) (i : Row) :
    ∃w∈S, cell w (lower i)≠cell w (upper i) := by
  have ne : label (lower i)≠label (upper i) := by rw [(labels i).1,(labels i).2]; decide
  exact finish.2.1 _ _ ne

theorem terminal_mark (S : Finset W) (finish : cleanCut model label 6 S) (i : Row) :
    ∃w∈S, bit (mark w).1 i≠bit (mark w).2 i := by
  obtain ⟨w,m,d⟩ := terminal_dist S finish i
  exact ⟨w,m,by rw [positive,negative]; exact Ne.symm d⟩

def basis : Fin 9 → Mark := ![(0x210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f,0x7e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07),
  (0x3e0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279,0x3e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038),
  (0x421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0,0x1f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0),
  (0x84208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc480,0xffc0000fffe00001f80001ff00000001ffc000007ffc000),
  (0x3ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff9088802,0x3ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000),
  (0x10842084210822109042108882108917fffffc00802010fffffffffe000101004,0x7fffffc00000000fffffffffe000000000),
  (0x21084108421044213ffffff004001007ffffffffffffff0100400040102000020,0x3fffffe000000007ffffffffffffff0000000000000000000),
  (0x3ffffff0002080003ffffffffffffffa108211000041004208821085000002100,0x3fffffe0000000003ffffffffffffff8000000000000000000000000000000000),
  (0x3fffffffffffffffe084210008210004210422110882228411042108004210000,0x3fffffffffffffffc000000000000000000000000000000000000000000000000)]

theorem basis_matches : ∀ i : Fin 9, mark (raw i)=basis i := by
  intro i
  fin_cases i <;> decide +kernel

theorem seed_matches : mark seed=((basis 0).1 ||| (basis 2).1,(basis 0).2 ||| (basis 2).2) := by
  change mark (join true (raw 0) (raw 2))=_
  simp only [mark_gate,basis_matches,↓reduceIte]

end CoPortEdgeRows4482

namespace CoRecipe4482
open CoPortRoots4482 CoPortEdgeRows4482 CoBitBlock4482

structure Entry where
  full : W
  projected : Mark
  correct : projected=mark full
  ordered : Ordered full

def input (i : Fin 9) : Entry :=
  ⟨raw i,basis i,(basis_matches i).symm,raw_order i⟩

def gate (d : Bool) (a b : Entry) : Entry where
  full := join d a.full b.full
  projected :=
    if d then (a.projected.1 ||| b.projected.1,a.projected.2 ||| b.projected.2)
    else (a.projected.1 &&& b.projected.1,a.projected.2 &&& b.projected.2)
  correct := by rw [mark_gate,←a.correct,←b.correct]
  ordered := join_ordered d a.ordered b.ordered

def fromFields : Nat → List Nat → Array Entry → Option (Array Entry × List Nat)
  | 0,fields,entries => some (entries,fields)
  | _+1,[],_ => none
  | n+1,t::fields,entries =>
    if h : t<9 then fromFields n fields (entries.push (input ⟨t,h⟩))
    else match fields with
    | [] => none
    | b::tail =>
      match entries[(t-9)/2]?,entries[b]? with
      | some a,some b =>
        fromFields n tail (entries.push (gate (decide ((t-9) % 2=1)) a b))
      | _,_ => none

theorem entry_projection {n fields entries encoded tail}
    (_built : fromFields n fields entries=some (encoded,tail))
    {a : Entry} (_member : a∈encoded) : a.projected=mark a.full ∧ Ordered a.full :=
  ⟨a.correct,a.ordered⟩

end CoRecipe4482

namespace CoPortTrace4482
variable {W V : Type} [DecidableEq W] [DecidableEq V]

theorem transport {join : Bool → W → W → W} {join' : Bool → V → V → V}
    {stop : Finset W → Prop} {stop' : Finset V → Prop} (f : W → V)
    (inj : Function.Injective f) (op : ∀ d a b,f (join d a b)=join' d (f a) (f b))
    (terminal : ∀ S,stop S → stop' (S.image f))
    {k S} (p : Path join stop k S) : Path join' stop' k (S.image f) := by
  induction p with
  | final S h => exact Path.final _ (terminal S h)
  | @step k U d a b ne fresh tail ih =>
    have strict : join' d (f a) (f b) ∉ (insert a (insert b U)).image f := by
      intro h
      obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp h
      exact fresh (inj (eq.trans (op d a b).symm) ▸ hw)
    simp only [Finset.image_insert,op] at ih strict ⊢
    exact Path.step d (f a) (f b) (fun e => ne (inj e)) strict ih

end CoPortTrace4482

namespace CoPortRoots4482
open CoPortTrace4482 CoPortCut4482

def packRows {n : Nat} (f : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem packRows_value {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (packRows f).getLsbD i.val=f i := by
  rw [packRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  have h : i.val < (List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

def reorder (g : R ≃ R) (w : W) : W := packRows (fun r => cell w (g r))

theorem value_reorder (g : R ≃ R) (w : W) (r : R) : cell (reorder g w) r = cell w (g r) :=
  packRows_value _ r

theorem cell_ext {a b : W} (h : ∀ r : R,cell a r=cell b r) : a=b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact h ⟨i,hi⟩

theorem reorder_inj (g : R ≃ R) : Function.Injective (reorder g) := by
  intro u v eq
  apply cell_ext
  intro r
  simpa only [value_reorder,Equiv.apply_symm_apply] using congrArg (fun w => cell w (g.symm r)) eq

theorem reorder_join (g : R ≃ R) (d : Bool) (u v : W) :
    reorder g (join d u v) = join d (reorder g u) (reorder g v) := by
  apply cell_ext
  intro r
  have joinVal (a b : W) (s : R) : cell (join d a b) s =
      (if d then cell a s || cell b s else cell a s && cell b s) := model.applyJoin d a b s
  simp only [value_reorder,joinVal]

set_option maxRecDepth 4000 in
theorem reorder_path (g : R ≃ R) (inv : ∀ r, label (g r)=label r)
    {k S} (p : Path join (cleanCut model label 6) k S) :
    Path join (cleanCut model label 6) k (S.image (reorder g)) := by
  apply transport (reorder g) (reorder_inj g) (reorder_join g) _ p
  intro T terminal
  obtain ⟨cap,dist,z,o⟩ := terminal
  have h0 : reorder g (0:W)=0 := by
    apply cell_ext
    intro r
    rw [value_reorder]
    change model.val model.zero (g r)=model.val model.zero r
    rw [model.atZero,model.atZero]
  have h1 : reorder g top=top := by
    apply cell_ext
    intro r
    rw [value_reorder]
    change model.val model.one (g r)=model.val model.one r
    rw [model.atOne,model.atOne]
  refine ⟨Finset.card_image_le.trans cap,?_,?_,?_⟩
  · intro x y different
    have ne : label (g x) ≠ label (g y) := by simpa only [inv] using different
    obtain ⟨w,wt,unlike⟩ := dist (g x) (g y) ne
    refine ⟨reorder g w,Finset.mem_image_of_mem _ wt,?_⟩
    change cell (reorder g w) x ≠ cell (reorder g w) y
    rw [value_reorder,value_reorder]
    exact unlike
  · intro hit
    obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp hit
    have same : w=(0 : W) := reorder_inj g (eq.trans h0.symm)
    rw [same] at hw
    exact z hw
  · intro hit
    obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp hit
    have same : w=top := reorder_inj g (eq.trans h1.symm)
    rw [same] at hw
    exact o hw

end CoPortRoots4482

namespace CoPortRoots4482
abbrev G := Fin 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
def permutations : G → Nat := ![0xffffbfbfcfdfebf3f8fbfdbebf4f9fcbe3f0f7fbbdbecf5fabd3e8f3f9bcbe4f1f8bc3e0eff7bbbdcedf6bb3d8ebf5babd4e9f4ba3d0e7f3b9bcce5f2b93c8e3f1b8bc4e1f0b83c0dfefb7bbcddeeb73b8dbedb6bb4d9ecb63b0d7ebb5bacd5eab53a8d3e9b4ba4d1e8b43a0cfe7b3b9ccde6b3398cbe5b2b94c9e4b2390c7e3b1b8cc5e2b1388c3e1b0b84c1e0b0380bfdfafb7cbddeaf378bbddaeb74b9dcae370b7dbadb6cb5daad368b3d9acb64b1d8ac360afd7abb5cadd6ab358abd5aab54a9d4aa350a7d3a9b4ca5d2a9348a3d1a8b44a1d0a83409fcfa7b3c9dcea73389bcda6b3499cca633097cba5b2c95caa532893c9a4b2491c8a43208fc7a3b1c8dc6a33188bc5a2b1489c4a231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99cae471b89c2e06fb79badc6db69b2d86bb59aad469b49a2d067b399acc65b2992c863b198ac461b0982c05faf97abc5dae972b85bad96ab459ac962b057ab95aac55aa952a853a994aa451a8942a04fa793a9c4da6932984ba592a9449a49229047a391a8c45a29128843a190a8441a0902803f9f8fa7c3d9e8f2783b9d8ea74399c8e270379b8da6c359a8d26833998ca6431988c2602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200,0xfffddfef7eff5dbed7ff7d9fcf6ef759bcd6f7f9ddee7e7f1d9ec7f7799dce6e77199cc6fdfcdf6f3edf4db6d3fd7c9f4f2ed749b4d2f5f8dd6e3e5f0d96c3f5789d4e2e570994c2dfedd7eb7cfe5d3e97df6d97cb6cf6593c96d7e9d5ea7c7e1d1e87d76995ca6c76191c86ddecd76b3cde4d3693dd6c974b2cd6493492d5e8d56a3c5e0d1683d568954a2c56091482bfddcfe77afd5cbe57bf5d8fc76af558bc56b7d9cde67a7d1c9e47b7598dc66a75189c46bddccf673add4cb653bd5c8f472ad548b452b5d8cd663a5d0c9643b5588d462a550894429fcdc7e378fc5c3e179f4d87c368f4583c1697c9c5e2787c1c1e07974985c26874181c069dccc76338dc4c36139d4c874328d448341295c8c562385c0c1603954885422854081402fefd5faf5eef55bad5fe7d1f8f4ee751b8d4f6f95dae5e6f159ac5f6791d8e4e671198c4fcfc5f2f1ecf45b2d1fc7c1f0f0ec741b0d0f4f85d2e1e4f0592c1f4781d0e0e470190c0deed57ab5cee553a95de6d178b4ce6513894d6e955aa5c6e151a85d669158a4c66111884dcec572b1cce453291dc6c170b0cc6413090d4e8552a1c4e051281d468150a0c46011080bedd4fa75aed54ba55be5d0f874ae550b854b6d94da65a6d149a45b6590d864a65109844bcdc4f271acd44b251bc5c0f070ac540b050b4d84d261a4d049241b4580d060a450090409ecd47a358ec543a159e4d078348e450381496c945a2586c141a059649058248641018049ccc472318cc4432119c4c070308c440301094c84522184c041201944805020844001000,0xffffbbfde7fbf9bedefbfdbafd67bbd9aed6f7fbb9fce77bb99ecef3f9b8fc673b998ec6feff3bbdc7ebf1badcfafd3abd47abd1aad4f6fb39bcc76bb19accf2f938bc472b918ac4bfdfabf5e3f9f8be5ebbddaaf563b9d8ae56b7dba9f4e379b89e4eb3d9a8f46339988e46bedf2bb5c3e9f0ba5cbadd2ab543a9d0aa54b6db29b4c369b09a4cb2d928b44329908a44dfefb3f9e5faf93e9edbedb2f965bad92e96d7ebb1f8e57ab91e8ed3e9b0f8653a990e86deef33b9c5eaf13a9cdaed32b945aad12a94d6eb31b8c56ab11a8cd2e930b8452a910a849fcfa3f1e1f8f83e1e9bcda2f161b8d82e1697cba1f0e178b81e0e93c9a0f06138980e069ecf23b1c1e8f03a1c9acd22b141a8d02a1496cb21b0c168b01a0c92c920b04128900a04fdfebb7da7dbe9b6daf9fcba7d279bc9a6d2f5fab97ca75ba996caf1f8b87c271b8986c2fcfe3b3d87cbe1b2d8f8fc3a3d078bc1a2d0f4fa393c874ba192c8f0f8383c070b8182c0bddeab75a3d9e8b65ab9dcaa752399c8a652b5daa974a359a8964ab1d8a8742319888642bcde2b3583c9e0b258b8dc2a350389c0a250b4da29348349a09248b0d828340309808240ddeeb379a5dae9369ad9ecb279259ac92692d5eab178a55aa9168ad1e8b078251a890682dcee333985cae13298d8ec3239058ac12290d4ea3138854aa11288d0e83038050a8102809dcea371a1d8e8361a99cca2712198c8261295caa170a158a8160a91c8a07021188806029cce233181c8e0321898cc22310188c0221094ca21308148a0120890c820300108800200,0xfffdff7f3fefd7f3f1ff7dbf5f2fe7d3f1f0f7f9fd7e3f6f97d3e1f779bd5e2f6793d1e07fbddf6f37ebd5f2f17f3d9f4f27e3d1f0f077b9dd6e376b95d2e177399d4e276391d0e0bfddef773bedd6f371bf5daf572be5d2f170b7d9ed763b6d96d361b759ad562b6592d1603f9dcf6733e9d4f2713f1d8f4723e1d0f0703799cd66336994d26137198d46236190d060dfedf77b3deed773b1df6db75b2de6d371b0d7e9f57a3d6e9753a1d769b55a2d669351a05fadd76b35ead572b15f2d974b25e2d170b057a9d56a356a9552a15729954a25629150a09fcde77339ecd673319f4da75329e4d2713097c9e572396c9653219749a55229649251201f8dc76331e8d472311f0d874321e0d070301789c5623168945221170985422160905020eff5fb7d3eef57b3d1ef75bb5d2ee753b1d0e7f1f97c3e6f1793c1e771b95c2e671391c06fb5db6d36eb55b2d16f359b4d26e351b0d067b1d96c366b1592c16731994c26631190c0afd5eb753aed56b351af55ab552ae552b150a7d1e9743a6d169341a751a9542a651291402f95cb6532e954b2512f158b4522e150b0502791c9643269149241271189442261109040cfe5f3793cee573391cf65b3592ce6533190c7e1f1783c6e171381c761b1582c661311804fa5d36934ea5532914f25934924e251309047a1d168346a1512814721914824621110808fc5e37138ec5633118f45a35128e452311087c1e170386c1613018741a15028641211000f85c36130e85432110f05834120e05030100781c1603068141201070181402060101000,0xffff7fdfceff77bddc7fbf5fcfc6fb75bcdcdfef77dbccfe773d9c5faf57cbc4fa753c9cfdfe7f5f8edf67b5d87dbe5f4f86db65b4d8ddee775b8cde6735985dae574b84da653498f7fb7ddece7f379dcc77bb5dcec67b359cccd7eb75dacc7e371d8c57ab55cac47a351c8cf5fa7d5e8e5f2795c875ba5d4e865b2594c8d5ea755a8c5e27158855aa554a845a251488bfdf6fd7cafd76bd5c3f9f4fc7c2f974bc5c9fcf67d3c8fc763d1c1f8f47c3c0f8743c1cbdde6f578add66b5583d9e4f4782d964b4589dce675388dc6635181d8e474380d8643418b7db6dd6ca7d369d4c379b4dc6c279349c4c97cb65d2c87c361d0c178b45c2c078341c0cb5da6d568a5d269548359a4d46825924944895ca6552885c261508158a45428058241408fbfd7edf4ebf57add47bbd5ecf46bb55acd4dbed76db4cbe572d945bad56cb44ba552c94f9fc7e5f0e9f47a5d079bc5e4f069b45a4d0d9ec765b0c9e47259059ac564b049a452490f3f97cde4e3f178dc473b95cce463b158cc4d3e974da4c3e170d8453a954ca443a150c84f1f87c5e0e1f0785c071b85c4e061b0584c0d1e8745a0c1e07058051a8544a041a050480bbdd6ed74abd56ad543b9d4ec742b954ac549bcd66d348bc562d141b8d46c340b8542c14b9dc6e570a9d46a550399c4e47029944a45099cc6653089c462510198c46430098442410b3d96cd64a3d168d4433994cc64239148c4493c964d2483c160d04138944c24038140c04b1d86c560a1d06854031984c46021904844091c86452081c060500118844420018040400,0xffbffeef7fdbefe6f3febf7eaf5fcbe7e2f1dfaff6eb7ddaef66b3deaf76ab5dcae762b1efb7faed7edb6fa6d3eeb77aad5ecb67a2d1cfa7f2e97cda6f2693cea772a95cca672291f7bbfcee7f5bafc6e3f6bb7cae5f4ba7c2e1d7abf4ea7d5aaf46a3d6ab74aa5d4aa742a1e7b3f8ec7e5b2f86c3e6b378ac5e4b2782c1c7a3f0e87c5a2f0683c6a370a85c4a270281bf9feee77bd9eee673be9f6ea75bc9e6e2719f8fe6e379d8ee66339e8f66a359c8e66231af97eae57ad96ea653ae976aa55ac966a2518f87e2e178d86e26138e8762a158c8662211b79bece67b59aec663b69b6ca65b49a6c261978be4e27958ae4623968b64a25948a64221a793e8e47a592e8643a69368a45a492682418783e0e078582e0603868360a05848260201ff3fbecf6fd3ebe4f2fe3f3e8f4fc3e3e0f0df2fb6cb6dd2eb64b2de2f368b4dc2e360b0ef37bacd6ed36ba4d2ee373a8d4ec363a0d0cf27b2c96cd26b2492ce2732894cc2632090f73bbcce6f53abc4e2f63b3c8e4f43a3c0e0d72bb4ca6d52ab44a2d62b348a4d42a340a0e733b8cc6e532b84c2e633388c4e432380c0c723b0c86c522b0482c62330884c42230080bf1faec76bd1eae472be1f2e874bc1e2e0709f0fa6c369d0ea64329e0f268349c0e26030af17aac56ad16aa452ae172a854ac162a0508f07a2c168d06a24128e07228148c0622010b71bacc66b51aac462b61b2c864b41a2c060970ba4c26950aa4422960b24824940a24020a713a8c46a512a8442a61328844a412280408703a0c068502a0402860320804840220000,0xffff7f7f9fbfd7e7f17fbf5f6f97bbd5e6f1dfef777b9dbed767b15faf576b95bad566b1ff7f3f5f8fb7d3e5f07f3f1f4f87b3d1e4f0df6f375b8db6d365b05f2f174b85b2d164b0bfdf6f779bbdd6e7713f9f4f6793b9d4e6719fcf677399bcd667311f8f476391b8d46631bf5f2f578bb5d2e5703f1f0f4783b1d0e4709f4f275389b4d265301f0f074381b0d06430f7fb7d7e9f3f97c7e177bb5d6e973b95c6e1d7eb757a9d3e9747a157ab556a953a9546a1f77b3d5e8f3793c5e0773b1d4e873391c4e0d76b355a8d369345a0572b154a85329144a0b7db6d769b3d96c761379b4d66933994c66197cb6572993c964721178b45629138944621b75b2d568b3592c560371b0d46833190c460974b25528934924520170b05428130904420eff77b7d9ebf57a7d16fb75b6d96bb55a6d1cfe773799cbe5727914fa7536994ba552691ef773b5d8eb753a5d06f371b4d86b351a4d0cf6733598cb65325904f27134984b2512490afd76b759abd56a7512f974b6592b954a6518fc7637198bc5627110f87436190b8542611af572b558ab552a5502f170b4582b150a4508f47235188b45225100f07034180b0502410e7f3797c9e3f1787c167b3596c963b1586c1c7e371789c3e17078147a35168943a150681e773395c8e371385c06733194c86331184c0c76331588c36130580472311488432110480a7d369749a3d16874127934964923914864187c36170983c160701078341609038140601a75329548a35128540271309448231108440874321508834120500070301408030100400,0xffbffbedfff3fbbcdefebf7baddfe3f3b8dcdfaff3e9fdf2fb3c9edeaf73a9dde2f3389cfbbdfaed7fb3dbacd6fabd7aad5fa3d3a8d4dbadf2e97db2db2c96daad72a95da2d32894bf9febe5fbf1fabc5ebe9f6ba5dbe1f2b85c9f8fe3e1f9f0fa3c1e9e8f63a1d9e0f2381cbb9deae57bb1daac56ba9d6aa55ba1d2a8549b8de2e179b0da2c169a8d62a159a0d22814f7bbf9ecff73bb9ccef6bb79acdf63b398ccd7abf1e8fd72bb1c8ed6ab71a8dd62b3188cf3b9f8ec7f339b8cc6f2b978ac5f239388c4d3a9f0e87d329b0c86d2a970a85d22930884b79be9e4fb71ba9c4eb69b69a4db61b2984c978be1e0f970ba1c0e968b61a0d960b2180cb399e8e47b319a8c46b29968a45b219288449389e0e079309a0c06928960a05920920804fdbefb6dbfd3ebb4dafcbe7b2d9fc3e3b0d8ddaef369bdd2eb349adcae73299dc2e33098f9bcfa6d3f93cba4d2f8bc7a2d1f83c3a0d0d9acf2693d92cb2492d8ac72291d82c32090bd9eeb65bbd1eab45abc9e6b259bc1e2b0589d8ee361b9d0ea341a9c8e632199c0e23018b99cea653b91caa452b89c6a251b81c2a050998ce2613990ca2412988c62211980c22010f5baf96cbf53ab94caf4ba792c9f43a390c8d5aaf168bd52ab148ad4aa71289d42a31088f1b8f86c3f138b84c2f0b8782c1f038380c0d1a8f0683d128b0482d0a870281d02830080b59ae964bb51aa944ab49a69249b41a29048958ae160b950aa140a948a61209940a21008b198e8643b118a8442b09868241b018280409188e06039108a0402908860201900820000,0xfffefeff37fbedeef3eff6fafd36fb6daed3bfdeeef733f9ecee73afd6eaf532f96cae53fefe7ebf17ebe5eaf1eef67abd16eb65aad1bede6eb713e9e4ea71aed66ab512e964aa51f7fafcfe377badcee3e7f2f8fc367b2d8ec3b7daecf63379acce63a7d2e8f432792c8e43f6fa7cbe176ba5cae1e6f278bc166b258ac1b6da6cb61369a4ca61a6d268b41269248a41dfeef6fb35faed6eb3cfe6f2f934fa6d2e939fcee6f331f8ec6e338fc6e2f130f86c2e13deee76bb15eae56ab1cee672b914ea652a919ece66b311e8e46a318ec662b110e8642a11d7eaf4fa357aad4ea3c7e2f0f8347a2d0e8397cae4f23178ac4e2387c2e0f030782c0e03d6ea74ba156aa54aa1c6e270b8146a250a8196ca64b21168a44a2186c260b01068240a01ff7ebedf27f3e9ecf2ef76badd26f369acd2bf5eaed723f1e8ec72af56aad522f168ac52fe7e3e9f07e3e1e8f0ee763a9d06e361a8d0be5e2e9703e1e0e870ae562a9502e160a850f77abcde2773a9cce2e772b8dc2673298cc2b75aacd62371a8cc62a752a8d42271288c42f67a3c9e0763a1c8e0e672389c06632188c0b65a2c960361a0c860a65228940261208840df6eb6db25f2e96cb2cf66b2d924f2692c929f4ea6d321f0e86c328f46a2d120f0682c12de6e369b05e2e168b0ce66329904e26128909e4e269301e0e068308e46229100e0602810d76ab4da2572a94ca2c762b0d82472290c82974aa4d22170a84c228742a0d02070280c02d66a349a0562a148a0c66230980462210880964a24920160a04820864220900060200800,0xfff7ffddefef77f9dcfdf6ff5dafcf67f1d8bfd7efd5ebed76f95cbdd6ef55abcd66f1587fb7dfcde7eb75f8dc7db6df4da7cb65f0d83f97cfc5e3e974f85c3d96cf45a3c964f058f7f3fddcef6f37d9ccf5f2fd5caf4f27d1c8b7d3edd4eb6d36d94cb5d2ed54ab4d26d14877b3ddcce76b35d8cc75b2dd4ca74b25d0c83793cdc4e36934d84c3592cd44a34924d048dfe7f7d9edee77799cdde6f759adce6771989fc7e7d1e9ec76791c9dc6e751a9cc6671185fa7d7c9e5ea75789c5da6d749a5ca6570981f87c7c1e1e874781c1d86c741a1c8647018d7e3f5d8ed6e37598cd5e2f558ad4e27518897c3e5d0e96c36590c95c2e550a94c26510857a3d5c8e56a35588c55a2d548a54a2550881783c5c0e16834580c1582c540a148245008fbf5fedd6faf57e9d4f9f4fe5d2f8f47e1d0bbd5eed56bad56e954b9d4ee552b8d46e1507bb5decd67ab55e8d479b4de4d278b45e0d03b95cec563a954e8543994ce45238944e050f3f1fcdc6f2f17c9c4f1f0fc5c2f0f07c1c0b3d1ecd46b2d16c944b1d0ec542b0d06c14073b1dccc672b15c8c471b0dc4c270b05c0c03391ccc4632914c8443190cc44230904c040dbe5f6d96dae576994d9e4f6592d8e4761909bc5e6d169ac56691499c4e651298c4661105ba5d6c965aa55689459a4d649258a4560901b85c6c161a85468141984c6412188446010d3e1f4d86d2e174984d1e0f4582d0e07418093c1e4d0692c16490491c0e450290c06410053a1d4c8652a15488451a0d448250a0540801381c4c061281448041180c4402108044000,0xfffeffbf9ff7ebf9f8eff6fbbd9ef76bb9d8bfdeefb79bf5eaf978afd6ebb59af56ab958fbfcfebf1fb7cbe9f0ebf4fabd1eb74ba9d0bbdceeb71bb5cae970abd4eab51ab54aa950dfeef7bb9df6eb79b8cfe6f3b99cf66b39989fcee7b399f4ea79388fc6e3b198f46a3918dbecf6bb1db6cb69b0cbe4f2b91cb64b29909bcce6b319b4ca69308bc4e2b118b44a2910f7fafdbe9f77abd9e8e7f2f9bc9e772b99c8b7daedb69b75aad968a7d2e9b49a752a9948f3f8fcbe1f378bc9e0e3f0f8bc1e370b89c0b3d8ecb61b358ac960a3d0e8b41a350a8940d7eaf5ba9d76ab59a8c7e2f1b89c762b198897cae5b29974aa592887c2e1b098742a1908d3e8f4ba1d368b49a0c3e0f0b81c360b098093c8e4b219348a492083c0e0b018340a09007fbedfaf97f3e9f8f86fb6dbad96f369b8d83f9ecfa793f1e8f8782f96cba592f168b8587bbcdeaf17b3c9e8f06bb4daad16b349a8d03b9ccea713b1c8e8702b94caa512b148a8505faed7ab95f2e978b84fa6d3a994f26938981f8ec7a391f0e878380f86c3a190f06838185bacd6ab15b2c968b04ba4d2a914b24928901b8cc6a311b0c868300b84c2a110b048281077baddae9773a9d8e867b2d9ac96732998c8379acda69371a8d8682792c9a4927128984873b8dcae173389c8e063b0d8ac16330988c03398cca6133188c8602390c8a4123108884057aad5aa9572a958a847a2d1a89472291888178ac5a29170a858280782c1a0907028180853a8d4aa15328948a043a0d0a814320908801388c4a211308848200380c0a01030080800,0xfff7dfedffbf5deed7fdf6df6dbf9f4de6d3bfd7cfe5fbbd5cee57bdd6cf65bb9d4ce653ff779fcdefb759ecd6fd769f4daf9749e4d2bf578fc5ebb558ec56bd568f45ab9548e452dfe7d7e9fdbe5d6e97dde6d769bd9e4d66939fc7c7e1f9bc5c6e179dc6c761b99c4c6613df6797c9edb6596c96dd669749ad964964929f4787c1e9b4586c169d468741a994486412f7f3ddecff3f1dcec7f5f2dd6cbf1f0dc6c3b7d3cde4fb3d1cce47b5d2cd64bb1d0cc643f7739dccef3719ccc6f5729d4caf1709c4c2b7538dc4eb3518cc46b5528d44ab1508c442d7e3d5e8fd3e1d4e87d5e2d568bd1e0d468397c3c5e0f93c1c4e0795c2c560b91c0c4603d76395c8ed36194c86d5629548ad16094482974385c0e934184c0695428540a914084402fef75faddfaf55ead5fcf65f2d9f8f45e2d1bed74fa5dbad54ea55bcd64f259b8d44e251fe771f8dcfa751e8d4fc761f0d8f8741e0d0be570f85cba550e854bc560f058b8540e050dee757a9ddae556a95dce657299d8e4562919ec747a1d9ac546a159cc64721998c446211de671789cda6516894dc6617098d864160909e470781c9a45068149c4607018984406010f6f35dacdf2f15cac5f4f25d2c9f0f05c2c1b6d34da4db2d14ca45b4d24d249b0d04c241f6731d8ccf2711c8c4f4721d0c8f0701c0c0b6530d84cb2510c844b4520d048b0500c040d6e355a8dd2e154a85d4e255289d0e05428196c345a0d92c144a0594c24520990c044201d6631588cd26114884d46215088d0601408096430580c924104804944205008904004000]
def inverse : G → G := ![0,1,2,3,4,5,9,8,7,6,10,11]
def shift (g : G) (r : R) : R := Fin.ofNat 512 ((permutations g) >>> (9*r.val))
def coordinate (g : G) (i : Fin 9) : Fin 9 := (![![0,1,2,3,4,5,6,7,8],![3,8,5,0,4,2,6,7,1],![0,5,8,3,4,1,7,6,2],![3,2,1,0,4,8,7,6,5],![1,0,5,8,6,2,4,7,3],![8,3,2,1,6,5,4,7,0],![5,0,1,2,7,8,4,6,3],![2,3,8,5,7,1,4,6,0],![8,5,0,1,6,3,7,4,2],![1,2,3,8,6,0,7,4,5],![2,1,0,5,7,3,6,4,8],![5,8,3,2,7,0,6,4,1]] : G → Fin 9 → Fin 9) g i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem back (g : G) : ∀ r : R, shift (inverse g) (shift g r)=r := by
  fin_cases g <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem order2 : ∀ g : G,inverse (inverse g)=g := by decide +kernel
def rowEquiv (g : G) : R ≃ R where
  toFun := shift g
  invFun := shift (inverse g)
  left_inv := back g
  right_inv := fun r => by simpa only [order2] using back (inverse g) r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem respects_label (g : G) : ∀ r : R,label (rowEquiv g r)=label r := by
  change ∀ r : R,label (shift g r)=label r
  fin_cases g <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem raw_cell (g : G) (i : Fin 9) : ∀ r : R,
    cell (raw i) (shift g r)=cell (raw (coordinate g i)) r := by
  fin_cases g <;> fin_cases i <;> decide +kernel

theorem raw_reordered (g : G) (i : Fin 9) : reorder (rowEquiv g) (raw i)=raw (coordinate g i) := by
  apply cell_ext
  intro r
  rw [value_reorder]
  exact raw_cell g i r

end CoPortRoots4482

namespace CoPortFrontier4482
open CoPortRoots4482 CoPortTrace4482 CoPortCut4482 CoPortEdgeRows4482 CoBitBlock4482

def Reach (k : Nat) (xs : List W) := ∃ j≤k, Path join (cleanCut model label 6) j xs.toFinset

def eraseIf (xs : List W) (v : W) (drop : Bool) : List W :=
  if drop then xs.filter (fun w => w != v) else xs

def successor (xs : List W) (op : Bool) (a b : W) (da db : Bool) : List W :=
  join op a b :: eraseIf (eraseIf xs a da) b db

theorem set_eraseIf (xs : List W) (v : W) (d : Bool) :
    (eraseIf xs v d).toFinset=CoPortTrace4482.discard xs.toFinset v d := by
  cases d
  · rfl
  · ext w
    simp [eraseIf,CoPortTrace4482.discard,and_comm]

theorem set_successor (xs : List W) (op : Bool) (a b : W) (da db : Bool) :
    (successor xs op a b da db).toFinset =
      insert (join op a b) (CoPortTrace4482.discard (CoPortTrace4482.discard xs.toFinset a da) b db) := by
  simp only [successor,List.toFinset_cons,set_eraseIf]

theorem reach_width {xs k} (p : Reach k xs) : xs.toFinset.card ≤ 6+k := by
  obtain ⟨j,hj,h⟩ := p
  have bound := width (fun T (st : cleanCut model label 6 T) => st.1) h
  omega

theorem tight_exact {xs k} (h : xs.toFinset.card=6+k) (p : Reach k xs) :
    Path join (cleanCut model label 6) k xs.toFinset := by
  obtain ⟨j,hj,run⟩ := p
  have bound := width (fun T (st : cleanCut model label 6 T) => st.1) run
  have eq : j=k := by omega
  exact eq ▸ run

theorem children {xs k} (room : 6<xs.toFinset.card) (p : Reach (k+1) xs) :
    ∃ a∈xs, ∃ b∈xs, ∃ d da db : Bool,
      a≠b ∧ join d a b∉xs ∧ Reach k (successor xs d a b da db) := by
  obtain ⟨j,lo,run⟩ := p
  cases j with
  | zero =>
    cases run with
    | final _ st => exact False.elim ((Nat.not_le_of_gt room) st.1)
  | succ j =>
    obtain ⟨d,a,b,da,db,ma,mb,ne,fresh,sub⟩ := transition run
    exact ⟨a,List.mem_toFinset.mp ma,b,List.mem_toFinset.mp mb,d,da,db,ne,
      fun m => fresh (List.mem_toFinset.mpr m),j,by omega,by rwa [set_successor]⟩

def cov : List Mark → Bits
  | [] => 0
  | m::ms => (m.1 ^^^ m.2) ||| cov ms

theorem cov_member {ms : List Mark} {m : Mark} (i : Row) (mem : m∈ms)
    (on : (m.1 ^^^ m.2).getLsbD i.val=true) : (cov ms).getLsbD i.val=true := by
  induction ms with
  | nil => simp at mem
  | cons a t ih =>
    simp only [cov,BitVec.getLsbD_or,Bool.or_eq_true]
    rcases List.mem_cons.mp mem with rfl|inTail
    · exact Or.inl on
    · exact Or.inr (ih inTail)

theorem covered {xs k} (p : Reach k xs) : cov (xs.map mark)=BitVec.allOnes 258 := by
  obtain ⟨j,hj,path⟩ := p
  have sep := separated cell label model.applyJoin (fun T (t : cleanCut model label 6 T) => t.2.1) path
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  let i : Row := ⟨t,ht⟩
  have diff : label (lower i)≠label (upper i) := by rw [(labels i).1,(labels i).2]; decide
  obtain ⟨w,hw,ne⟩ := sep (lower i) (upper i) diff
  simp only [BitVec.getLsbD_allOnes,ht,decide_true]
  apply cov_member i (List.mem_map.mpr ⟨w,List.mem_toFinset.mp hw,rfl⟩)
  rw [difference]
  exact bne_iff_ne.mpr ne.symm

theorem equivalent {xs ys : List W} {k k' : Nat} (hk : k≤k') (g : G)
    (image : xs.toFinset.image (reorder (rowEquiv g))=ys.toFinset) (p : Reach k xs) : Reach k' ys := by
  obtain ⟨j,hj,run⟩ := p
  exact ⟨j,hj.trans hk,image ▸ reorder_path (rowEquiv g) (respects_label g) run⟩

end CoPortFrontier4482

namespace CoPortFrontier4482
open CoPortRoots4482 CoPortTrace4482 CoPortCut4482 CoPortEdgeRows4482 CoBitBlock4482

abbrev Entry := W × Mark
def authentic (xs : List Entry) := ∀ e∈xs,e.2=mark e.1
def words (xs : List Entry) := xs.map Prod.fst
def obs (xs : List Entry) := xs.map Prod.snd

theorem observations_match_words {xs : List Entry} (h : authentic xs) :
    obs xs=(words xs).map mark := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have tail := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    change a.2 :: obs xs=mark a.1 :: (words xs).map mark
    rw [ha,tail]

def make (d : Bool) (a b : Entry) : Entry :=
  (join d a.1 b.1,if d then (a.2.1 ||| b.2.1,a.2.2 ||| b.2.2)
    else (a.2.1 &&& b.2.1,a.2.2 &&& b.2.2))

def removeEntry (xs : List Entry) (w : W) (d : Bool) :=
  if d then xs.filter fun e => e.1!=w else xs

def move (xs : List Entry) (d : Bool) (a b : Entry) (da db : Bool) :=
  make d a b :: removeEntry (removeEntry xs a.1 da) b.1 db

theorem value_remove (xs : List Entry) (w : W) (d : Bool) :
    words (removeEntry xs w d)=eraseIf (words xs) w d := by
  cases d
  · rfl
  · induction xs with
    | nil => rfl
    | cons t ts ih =>
      cases h : t.1!=w <;> simp_all [words,removeEntry,eraseIf,List.filter_cons]

theorem value_move (xs : List Entry) (d : Bool) (a b : Entry) (da db : Bool) :
    words (move xs d a b da db)=successor (words xs) d a.1 b.1 da db := by
  change (join d a.1 b.1)::words (removeEntry (removeEntry xs a.1 da) b.1 db)=_
  rw [value_remove,value_remove]
  rfl

theorem authentic_remove {xs : List Entry} (h : authentic xs) (w : W) (d : Bool) :
    authentic (removeEntry xs w d) := by
  cases d
  · exact h
  · intro t m
    exact h t (List.mem_filter.mp m).1

theorem authentic_move {xs : List Entry} (h : authentic xs) (d : Bool) {a b : Entry}
    (ha : a∈xs) (hb : b∈xs) (da db : Bool) : authentic (move xs d a b da db) := by
  intro e he
  rcases List.mem_cons.mp he with eq|old
  · subst e
    change (if d then _ else _)=mark (join d a.1 b.1)
    rw [mark_gate,←h a ha,←h b hb]
  · exact authentic_remove (authentic_remove h a.1 da) b.1 db e old

def admitted (ys : List Entry) := cov (obs ys)==BitVec.allOnes 258

theorem may_move {xs : List Entry} {k : Nat} (auth : authentic xs)
    (room : 6<(words xs).toFinset.card) (p : Reach (k+1) (words xs)) :
    ∃ a∈xs, ∃ b∈xs,∃ d da db : Bool,
      a.1≠b.1 ∧ join d a.1 b.1∉words xs ∧ admitted (move xs d a b da db)=true ∧
      Reach k (words (move xs d a b da db)) := by
  obtain ⟨u,hu,v,hv,d,da,db,ne,fresh,child⟩ := children room p
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hu
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hv
  rw [←value_move xs d a b da db] at child
  refine ⟨a,ha,b,hb,d,da,db,ne,fresh,?_,child⟩
  exact beq_iff_eq.mpr ((congrArg cov (observations_match_words (authentic_move auth d ha hb da db))).trans (covered child))

end CoPortFrontier4482

namespace CoRecipeOrbit4482
open CoPortRoots4482 CoPortFrontier4482

structure Orbit where
  base : CoRecipe4482.Entry
  view : G → W
  correct : ∀ g, view g = reorder (rowEquiv g) base.full

def rawWord (i : Fin 9) : Orbit where
  base := CoRecipe4482.input i
  view := fun g => raw (coordinate g i)
  correct := fun g => (raw_reordered g i).symm

def gateWord (d : Bool) (a b : Orbit) : Orbit where
  base := CoRecipe4482.gate d a.base b.base
  view := fun g => join d (a.view g) (b.view g)
  correct := by
    intro g
    change join d (a.view g) (b.view g) = reorder (rowEquiv g) (join d a.base.full b.base.full)
    rw [a.correct g,b.correct g,reorder_join]

def payload (a : Orbit) : Entry := (a.base.full,a.base.projected)
def record (xs : List Orbit) := xs.map payload

theorem real (xs : List Orbit) : authentic (record xs) := by
  intro e he
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
  exact a.base.correct

theorem increasing (xs : List Orbit) {w : W} (m : w∈words (record xs)) :
    CoPortEdgeRows4482.Ordered w := by
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp m
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
  exact a.base.ordered

def lookup (g : G) (w : W) : List Orbit → W
  | [] => 0
  | a::xs => if a.base.full=w then a.view g else lookup g w xs

theorem lookup_correct (g : G) (w : W) (xs : List Orbit) (m : w∈words (record xs)) :
    lookup g w xs = reorder (rowEquiv g) w := by
  induction xs with
  | nil => simp [words,record] at m
  | cons a xs ih =>
    change w ∈ a.base.full :: words (record xs) at m
    by_cases eq : a.base.full=w
    · rw [lookup,if_pos eq,a.correct g,eq]
    · simp only [lookup,if_neg eq]
      exact ih ((List.mem_cons.mp m).resolve_left (fun h => eq h.symm))

def fromFields : Nat → List Nat → Array Orbit → Option (Array Orbit × List Nat)
  | 0,fields,entries => some (entries,fields)
  | _+1,[],_ => none
  | n+1,t::fields,entries =>
    if h : t<9 then fromFields n fields (entries.push (rawWord ⟨t,h⟩)) else
      match fields with
      | [] => none
      | b::tail =>
        match entries[(t-9)/2]?,entries[b]? with
        | some a,some b =>
          fromFields n tail (entries.push (gateWord (decide ((t-9) % 2=1)) a b))
        | _,_ => none

end CoRecipeOrbit4482

namespace CoJunctionWire4482
open CoPortRoots4482

inductive Wire where
  | input (i : Fin 9)
  | gate (op : Bool) (a b : Wire)

def eval : Wire → CoRecipe4482.Entry
  | .input i => CoRecipe4482.input i
  | .gate op a b => CoRecipe4482.gate op (eval a) (eval b)

def rename (g : G) : Wire → Wire
  | .input i => .input (coordinate g i)
  | .gate op a b => .gate op (rename g a) (rename g b)

theorem full_rename (g : G) (w : Wire) :
    (eval (rename g w)).full=reorder (rowEquiv g) (eval w).full := by
  induction w with
  | input i => exact (raw_reordered g i).symm
  | gate op a b ha hb =>
    change join op (eval (rename g a)).full (eval (rename g b)).full =
      reorder (rowEquiv g) (join op (eval a).full (eval b).full)
    rw [ha,hb,reorder_join]

def code (w : Wire) : CoRecipeOrbit4482.Orbit :=
  ⟨eval w,fun g => (eval (rename g w)).full,fun g => full_rename g w⟩

def successor (xs : List Wire) (i j : Nat) (op da db : Bool) (g : G) : Option (List Wire) := do
  let a ← xs[i]?
  let b ← xs[j]?
  let held := (xs.zipIdx.filter (fun q =>
    !((q.2==i && da)||(q.2==j && db)))).map Prod.fst
  let updated := (.gate op a b :: held).map (rename g)
  pure (updated.mergeSort (fun x y => decide ((eval x).full.toNat ≤ (eval y).full.toNat)))

end CoJunctionWire4482

namespace CoJunctionTree4482
open CoPortRoots4482 CoPortFrontier4482 CoJunctionWire4482

def value (w : Wire) := (eval w).full
def values (xs : List Wire) := xs.map value

private def insertWire (w : Wire) : List Wire → List Wire
  | [] => [w]
  | x::xs =>
    if (value w).toNat ≤ (value x).toNat then w::x::xs else x::insertWire w xs

private theorem inInsert (w a : Wire) (xs : List Wire) :
    a∈insertWire w xs ↔ a=w ∨ a∈xs := by
  induction xs with
  | nil => simp [insertWire]
  | cons x xs ih =>
    by_cases le : (value w).toNat≤(value x).toNat
    · simp [insertWire,le]
    · simp only [insertWire,if_neg le,List.mem_cons,ih]
      tauto

private def ordered : List Wire → List Wire
  | [] => []
  | x::xs => insertWire x (ordered xs)

private theorem inOrdered (xs : List Wire) (a : Wire) : a∈ordered xs ↔ a∈xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [ordered,inInsert,ih,List.mem_cons]

def imageBank (g : G) (xs : List Wire) := ordered (xs.map (rename g))

theorem set_image (g : G) (xs : List Wire) :
    (values (imageBank g xs)).toFinset = (values xs).toFinset.image (reorder (rowEquiv g)) := by
  ext w
  constructor
  · intro m
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp m)
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ((inOrdered _ y).mp hy)
    exact Finset.mem_image.mpr ⟨value x,List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hx,rfl⟩),
      (full_rename g x).symm⟩
  · intro m
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp m
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨rename g x,(inOrdered _ _).mpr (List.mem_map.mpr ⟨x,hx,rfl⟩),full_rename g x⟩

def forget (xs : List Wire) (w : W) (d : Bool) :=
  if d then xs.filter fun x => value x != w else xs

private theorem forget_values (xs : List Wire) (w : W) (d : Bool) :
    values (forget xs w d) = eraseIf (values xs) w d := by
  cases d with
  | false => rfl
  | true =>
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      cases h : value x != w <;> simp_all [values,forget,eraseIf,List.filter_cons]

def discover (g : G) (xs : List Wire) (op : Bool) (a b : Wire) (da db : Bool) :=
  imageBank g (.gate op a b :: forget (forget xs (value a) da) (value b) db)

theorem discovery_route (g : G) (xs : List Wire) (op : Bool) (a b : Wire) (da db : Bool) :
    (CoPortFrontier4482.successor (values xs) op (value a) (value b) da db).toFinset.image
       (reorder (rowEquiv g)) = (values (discover g xs op a b da db)).toFinset := by
  unfold discover
  rw [set_image]
  have eq : values (.gate op a b :: forget (forget xs (value a) da) (value b) db) =
      CoPortFrontier4482.successor (values xs) op (value a) (value b) da db := by
    change join op (value a) (value b) :: values (forget (forget xs (value a) da) (value b) db) = _
    rw [forget_values,forget_values]
    rfl
  rw [eq]

end CoJunctionTree4482

namespace CoJunctionLogical4482
open CoPortFrontier4482 CoPortRoots4482 CoPortTrace4482 CoPortCut4482

structure Record where
  bank : List Entry
  budget : Nat

def stateWords (r : Record) := words r.bank

def Routed {I : Type} (table : I → Record) (row : Record) : Prop :=
  ∀ a ∈ row.bank, ∀ b ∈ row.bank, ∀ op da db : Bool,
    a.1 ≠ b.1 → join op a.1 b.1 ∉ stateWords row →
    admitted (move row.bank op a b da db) = true →
    (words (move row.bank op a b da db)).toFinset.card ≤ 6+(row.budget-1) →
    ∃ t : I, ∃ g : G, row.budget-1 ≤ (table t).budget ∧
      (words (move row.bank op a b da db)).toFinset.image (reorder (rowEquiv g)) =
        (stateWords (table t)).toFinset

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

end CoJunctionLogical4482

namespace CoJunctionFixedModel4482
open CoJunctionFixed4482 CoJunctionWire4482 CoJunctionTree4482
open CoPortRoots4482 CoPortFrontier4482 CoJunctionLogical4482

def start (seeded : Bool) : List Wire :=
  let lower := [Wire.input 0,.input 1,.input 2]
  let others := [Wire.input 3,.input 4,.input 5,.input 6,.input 7,.input 8]
  lower ++ (if seeded then [Wire.gate true (.input 0) (.input 2)] else []) ++ others

def graphView (seeded : Bool) (idx : Nat) : G :=
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
  ⟨rank-j*(j-1)/2,j,rule.testBit 2,rule.testBit 0,rule.testBit 1,graphView seeded (tag % 16)⟩

def applyAction (act : Action) (xs : List Wire) : List Wire :=
  match xs[act.i]?,xs[act.j]? with
  | some a,some b => discover act.perm xs act.op a b act.da act.db
  | _,_ => []

def build (h : Graph) (seeded : Bool) : Nat → Nat → List Wire
  | 0,i => if i=0 then start seeded else []
  | fuel+1,i => if i=0 then start seeded else
      applyAction (decode seeded (firstAction h i)) (build h seeded fuel (parent h i))

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

theorem first_route (h : Graph) (seeded : Bool) {k p t d : Nat} (nt : t≠0)
    (par : parent h t=p) (old : Ancestry h p d) (room : d≤k) {a b : Wire}
    (ha : (build h seeded (k+1) p)[(decode seeded (firstAction h t)).i]?=some a)
    (hb : (build h seeded (k+1) p)[(decode seeded (firstAction h t)).j]?=some b) :
    let act := decode seeded (firstAction h t)
    (CoPortFrontier4482.successor (stateWords (table h seeded (k+1) p)) act.op
      (value a) (value b) act.da act.db).toFinset.image (reorder (rowEquiv act.perm)) =
      (stateWords (table h seeded (k+1) t)).toFinset := by
  let act := decode seeded (firstAction h t)
  let xs := build h seeded (k+1) p
  have same : build h seeded k p=xs :=
    stable seeded old room (room.trans (Nat.le_succ _))
  have th : build h seeded (k+1) t=discover act.perm xs act.op a b act.da act.db := by
    rw [build,if_neg nt,par,same]
    change applyAction act xs=_
    simp only [applyAction,show xs[act.i]?=some a from ha,show xs[act.j]?=some b from hb]
  change (CoPortFrontier4482.successor (words (data xs)) act.op (value a) (value b)
    act.da act.db).toFinset.image (reorder (rowEquiv act.perm)) =
    (words (data (build h seeded (k+1) t))).toFinset
  rw [data_values,data_values,th]
  exact discovery_route act.perm xs act.op a b act.da act.db

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

end CoJunctionFixedModel4482

namespace CoJunctionUnique4482
open CoPortRoots4482 CoPortFrontier4482 CoBitBlock4482

def privateRows (xs : List Entry) (w : W) : Bits :=
  exclusive (obs (removeEntry xs w true))

def allowed (u : Bits) (op : Bool) (other : Mark) : Bool :=
  (u &&& (if op then other.2 else ~~~other.1)) == 0

private theorem source (ms : List Mark) (i : Row) (on : bit (cov ms) i=true) :
    ∃ w∈ms, bit (w.1 ^^^ w.2) i=true := by
  induction ms with
  | nil => simp [cov,bit] at on
  | cons a ms ih =>
    change ((a.1 ^^^ a.2) ||| cov ms).getLsbD i.val=true at on
    rw [BitVec.getLsbD_or,Bool.or_eq_true] at on
    rcases on with aOn|tOn
    · exact ⟨a,List.mem_cons_self,aOn⟩
    · obtain ⟨x,m,one⟩ := ih tOn
      exact ⟨x,List.mem_cons_of_mem _ m,one⟩

private theorem pin (outside live : List Entry) (a b : Entry) (op : Bool)
    (hb : b∈outside) (within : ∀ x∈live,x∈outside)
    (coverage : admitted (make op a b :: live)=true) :
    allowed (exclusive (obs outside)) op b.2=true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  let i : Row := ⟨t,ht⟩
  by_cases yes : bit (exclusive (obs outside)) i=true
  · have eqFor (e : Entry) (m : e∈outside) : bit e.2.1 i = bit e.2.2 i :=
      outside_equal _ i yes e.2 (List.mem_map.mpr ⟨e,m,rfl⟩)
    have cover : cov (obs (make op a b :: live)) = BitVec.allOnes 258 :=
      beq_iff_eq.mp coverage
    have one : bit (cov (obs (make op a b :: live))) i=true := by
      rw [cover]
      simp only [bit,BitVec.getLsbD_allOnes,i.isLt,decide_true]
    obtain ⟨z,hz,diff⟩ := source _ i one
    rcases List.mem_map.mp hz with ⟨v,hv,rfl⟩
    rcases List.mem_cons.mp hv with head|old
    · subst v
      have eqB := eqFor b hb
      change b.2.1.getLsbD t = b.2.2.getLsbD t at eqB
      change ((make op a b).2.1 ^^^ (make op a b).2.2).getLsbD t=true at diff
      change (exclusive (obs outside)).getLsbD t=true at yes
      cases op <;>
        simp only [make,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_xor,
          BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
          ht,decide_true,Bool.true_and,yes,eqB] at diff ⊢ <;>
        cases aa : a.2.1.getLsbD t <;> cases ab : a.2.2.getLsbD t <;>
        cases bb : b.2.2.getLsbD t <;> simp_all
    · have eqV := eqFor v (within v old)
      change v.2.1.getLsbD t=v.2.2.getLsbD t at eqV
      change (v.2.1 ^^^ v.2.2).getLsbD t=true at diff
      simp [BitVec.getLsbD_xor,eqV] at diff
  · have off : (exclusive (obs outside)).getLsbD t=false := by
      cases h : (exclusive (obs outside)).getLsbD t <;> first | rfl | exact (yes h).elim
    simp [BitVec.getLsbD_and,off]

private theorem rem_subset {xs : List Entry} {w : W} {d : Bool} {e : Entry}
    (h : e∈removeEntry xs w d) : e∈xs := by
  cases d with
  | false => exact h
  | true => exact (List.mem_filter.mp h).1

theorem drop_left (xs : List Entry) {a b : Entry} (hb : b∈xs)
    (ne : a.1≠b.1) (op db : Bool)
    (h : admitted (move xs op a b true db)=true) :
    allowed (privateRows xs a.1) op b.2=true := by
  apply pin (removeEntry xs a.1 true) _ a b op _ _ h
  · exact List.mem_filter.mpr ⟨hb,bne_iff_ne.mpr ne.symm⟩
  · intro e he
    exact rem_subset he

theorem drop_right (xs : List Entry) {a b : Entry} (ha : a∈xs)
    (ne : a.1≠b.1) (op da : Bool)
    (h : admitted (move xs op a b da true)=true) :
    allowed (privateRows xs b.1) op a.2=true := by
  have comm : make op a b=make op b a := by
    cases op <;> simp [make,join,BitVec.or_comm,BitVec.and_comm]
  unfold move at h
  rw [comm] at h
  apply pin (removeEntry xs b.1 true) _ b a op _ _ h
  · exact List.mem_filter.mpr ⟨ha,bne_iff_ne.mpr ne⟩
  · intro e he
    obtain ⟨inside,other⟩ := List.mem_filter.mp he
    exact List.mem_filter.mpr ⟨rem_subset inside,other⟩

end CoJunctionUnique4482

namespace CoJunctionWidth4482
open CoPortRoots4482 CoPortFrontier4482 CoPortTrace4482

private theorem discard_subset (s : Finset W) (x : W) (d : Bool) :
    discard s x d ⊆ s := by
  cases d with
  | false => exact fun _ h => h
  | true => exact Finset.erase_subset _ _

theorem size_form {xs : List W} {a b : W} {d : Bool}
    (ha : a∈xs) (hb : b∈xs) (ne : a≠b) (fresh : join d a b∉xs) (da db : Bool) :
    (successor xs d a b da db).toFinset.card =
      xs.toFinset.card+1-(if da then 1 else 0)-(if db then 1 else 0) := by
  let s := xs.toFinset
  have ma : a∈s := List.mem_toFinset.mpr ha
  have mb : b∈s := List.mem_toFinset.mpr hb
  have missing : join d a b ∉ discard (discard s a da) b db :=
    fun m => fresh (List.mem_toFinset.mp (discard_subset s a da (discard_subset _ b db m)))
  have two : 1<s.card := Finset.one_lt_card.mpr ⟨a,ma,b,mb,ne⟩
  have bkept : b ∈ s.erase a := Finset.mem_erase.mpr ⟨ne.symm,mb⟩
  rw [set_successor,Finset.card_insert_of_notMem missing]
  cases da <;> cases db
  · rfl
  · change (s.erase b).card+1=s.card+1-0-1
    rw [Finset.card_erase_of_mem mb]
    omega
  · change (s.erase a).card+1=s.card+1-1-0
    rw [Finset.card_erase_of_mem ma]
    omega
  · change ((s.erase a).erase b).card+1=s.card+1-1-1
    rw [Finset.card_erase_of_mem bkept,Finset.card_erase_of_mem ma]
    omega

end CoJunctionWidth4482

namespace CoJunctionImages4482
open CoPortRoots4482 CoPortFrontier4482

def cachedStep (f : W → W) (xs : List W) (op : Bool) (a b : W) (da db : Bool) :=
  join op (f a) (f b) :: (eraseIf (eraseIf xs a da) b db).map f

private theorem erase_subset {xs : List W} {w z : W} {d : Bool}
    (h : z ∈ eraseIf xs w d) : z ∈ xs := by
  cases d with
  | false => exact h
  | true => exact (List.mem_filter.mp h).1

private theorem agreeMap {α β : Type} {f g : α → β} (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : xs.map f = xs.map g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons]
    rw [h a List.mem_cons_self,ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem cached_map {f : W → W} {xs : List W} {g : G}
    (cache : ∀ x∈xs, f x = reorder (rowEquiv g) x)
    {a b : W} (ha : a∈xs) (hb : b∈xs) (op da db : Bool) :
    cachedStep f xs op a b da db =
      (successor xs op a b da db).map (reorder (rowEquiv g)) := by
  change join op (f a) (f b) :: _ =
    (reorder (rowEquiv g) (join op a b)) :: _
  rw [cache a ha,cache b hb,reorder_join]
  have tail := agreeMap (f:=f) (g:=reorder (rowEquiv g)) (eraseIf (eraseIf xs a da) b db)
    (fun x hx => cache x (erase_subset (erase_subset hx)))
  exact congrArg (List.cons (join op (reorder (rowEquiv g) a) (reorder (rowEquiv g) b))) tail

theorem equalSet {xs ys : List W} (h : CoJunctionCost4482.sameSet xs ys = true) :
    xs.toFinset = ys.toFinset := by
  obtain ⟨hxy,hyx⟩ := Bool.and_eq_true_iff.mp h
  ext w
  simp only [List.mem_toFinset]
  constructor
  · intro m
    simpa using List.all_eq_true.mp hxy w m
  · intro m
    simpa using List.all_eq_true.mp hyx w m

theorem cached_route {f : W → W} {xs tgt : List W} {g : G}
    (cache : ∀ x∈xs, f x = reorder (rowEquiv g) x)
    {a b : W} (ha : a∈xs) (hb : b∈xs) {op da db : Bool}
    (matchTarget : CoJunctionCost4482.sameSet (cachedStep f xs op a b da db) tgt = true) :
    (successor xs op a b da db).toFinset.image (reorder (rowEquiv g))=tgt.toFinset := by
  rw [cached_map cache ha hb op da db] at matchTarget
  have eq := equalSet matchTarget
  rw [←eq]
  ext y
  simp

end CoJunctionImages4482

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

def scan {I : Type} (table : I → Record) (row : Record) (f : G → W → W)
    (reply : Reply I) : Bool :=
  sweep row.bank (action table row f reply)

def operandPairs (xs : List Entry) := pairs xs

theorem operand_mem {a b : Entry} {xs : List Entry} (h : (a,b)∈operandPairs xs) :
    a∈xs ∧ b∈xs := pair_inputs h

def Destination {I : Type} (table : I → Record) (row : Record)
    (a b : Entry) (op da db : Bool) : Prop :=
  ∃ t, ∃ g : G, row.budget-1 ≤ (table t).budget ∧
    (words (move row.bank op a b da db)).toFinset.image (reorder (rowEquiv g)) =
      (stateWords (table t)).toFinset

theorem from_pairs {I : Type} {table : I → Record} {row : Record}
    (accepted : ∀ {a b},(a,b)∈operandPairs row.bank → ∀ op da db,
      Good row a b op da db → Destination table row a b op da db) :
    Routed table row := by
  intro a ha b hb op da db ne fresh cover narrow
  have distinct : a≠b := fun e => ne (congrArg Prod.fst e)
  rcases one_order ha hb distinct with direct|back
  · exact accepted direct op da db ⟨ne,fresh,cover,narrow⟩
  · have sw := move_comm row.bank op a b da db
    have gate : join op b.1 a.1 = join op a.1 b.1 := by
      cases op <;> simp [join,BitVec.and_comm,BitVec.or_comm]
    have good : Good row b a op db da := by
      unfold Good
      rw [gate,sw]
      exact ⟨ne.symm,fresh,cover,narrow⟩
    simpa only [Destination,sw] using accepted back op db da good

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

end CoJunctionScan4482

namespace CoJunctionGuard4482
open CoPortRoots4482 CoPortFrontier4482 CoBitBlock4482
open CoJunctionScan4482 CoJunctionUnique4482 CoJunctionLogical4482

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

end CoJunctionGuard4482

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

end CoJunctionStream4482

namespace CoJunctionActual4482
open CoPortRoots4482 CoPortFrontier4482 CoJunctionLogical4482
open CoJunctionFixed4482 CoJunctionTree4482 CoJunctionWire4482
open CoJunctionStream4482

def picture (g : G) (w : W) : List Wire → W
  | [] => 0
  | a::xs => if value a=w then value (rename g a) else picture g w xs

theorem picture_correct (g : G) (w : W) (xs : List Wire) (hw : w∈values xs) :
    picture g w xs = reorder (rowEquiv g) w := by
  induction xs with
  | nil => simp [values] at hw
  | cons a xs ih =>
    change w∈value a::values xs at hw
    by_cases eq : value a=w
    · rw [picture,if_pos eq]
      exact (full_rename g a).trans (congrArg (reorder (rowEquiv g)) eq)
    · rw [picture,if_neg eq]
      exact ih ((List.mem_cons.mp hw).resolve_left (fun h => eq h.symm))

def recordAt (h : Graph) (seeded : Bool) (depth : Nat) (i : Fin h.size) :=
  CoJunctionFixedModel4482.table h seeded depth i.val

def arcsAt (h : Graph) [NeZero h.size] (seeded : Bool) (i : Fin h.size) : List (Fin h.size×G) :=
  (references h i.val).map fun (ref,g) => (Fin.ofNat h.size ref,CoJunctionFixedModel4482.graphView seeded g)

def internal (h : Graph) [NeZero h.size] (seeded : Bool) (depth : Nat) (i : Fin h.size) : Bool :=
  let row := recordAt h seeded depth i
  let xs := CoJunctionFixedModel4482.build h seeded depth i.val
  let frame := (stateWords row).toFinset.card
  stream (recordAt h seeded depth) row (fun g w => picture g w xs)
    (runs row frame (CoJunctionUnique4482.privateRows row.bank)) (arcsAt h seeded i)

theorem internal_sound {h : Graph} [NeZero h.size] {seeded : Bool} {depth : Nat} {i : Fin h.size}
    (accepted : internal h seeded depth i=true) :
    Routed (recordAt h seeded depth) (recordAt h seeded depth i) := by
  let xs := CoJunctionFixedModel4482.build h seeded depth i.val
  have views (g : G) (w : W) (hw : w∈stateWords (recordAt h seeded depth i)) :
      picture g w xs = reorder (rowEquiv g) w := by
    apply picture_correct
    change w∈words (CoJunctionFixedModel4482.data xs) at hw
    rwa [CoJunctionFixedModel4482.data_values] at hw
  exact stream_sound views rfl (fun _ _ => rfl) accepted

end CoJunctionActual4482

namespace CoBlockPartition4482

def splits {α : Type} : List α → List (List α × List α)
  | [] => [([],[])]
  | x::xs =>
    let v := splits xs
    v.map (fun (l,r) => (x::l,r)) ++ v.map (fun (l,r) => (l,x::r))

theorem take_split {α : Type} (p : α→Bool) (xs : List α) :
    (xs.filter p,xs.filter (fun x => !(p x)))∈splits xs := by
  induction xs with
  | nil => simp [splits]
  | cons x xs ih =>
    cases hp : p x
    · simp only [List.filter_cons,hp,Bool.false_eq_true,↓reduceIte,Bool.not_false]
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨_,ih,rfl⟩
    · simp only [List.filter_cons,hp,↓reduceIte,Bool.not_true,Bool.false_eq_true]
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨_,ih,rfl⟩

def possible {α : Type} (ok : List α→List α→Bool) : Nat → List α → List α → Bool
  | 0,todo,_ => todo.isEmpty
  | _+1,[],_ => false
  | k+1,a::xs,closed =>
    if xs.length=k then true
    else if xs.length<k then false
    else (splits xs).any fun (take,remain) =>
      decide (k≤remain.length) && ok (a::take) (closed++remain) &&
      possible ok k remain ((a::take)++closed)

theorem possible_of_owner {α γ : Type} [DecidableEq γ] (ok : List α→List α→Bool)
    (owner : α→γ) (S : Finset α) (k : Nat) (T : Finset γ)
    (size : T.card=k) (todo closed : List α)
    (lands : ∀ w∈todo, owner w∈T) (past : ∀ w∈closed, owner w∉T)
    (onto : ∀ t∈T, ∃ w∈todo, owner w=t)
    (cover : ∀ w∈S,w∈todo∨w∈closed)
    (good : ∀ t∈T, ∀ part outside : List α,
       (∀w∈part,owner w=t) → (∀w∈outside,owner w≠t) →
       (∀w∈S,w∈part∨w∈outside) → ok part outside=true) :
    possible ok k todo closed=true := by
  classical
  induction k generalizing T todo closed with
  | zero =>
    have ht : T=∅ := Finset.card_eq_zero.mp size
    cases todo with
    | nil => rfl
    | cons a xs =>
      have bad := lands a (List.mem_cons_self)
      simp [ht] at bad
  | succ k ih =>
    have count {G : Finset γ} {zs : List α} (h : ∀g∈G,∃z∈zs,owner z=g) :
        G.card≤zs.length := by
      have incl : G⊆zs.toFinset.image owner := by
        intro g mg
        obtain ⟨w,wm,e⟩ := h g mg
        exact Finset.mem_image.mpr ⟨w,List.mem_toFinset.mpr wm,e⟩
      exact (Finset.card_le_card incl).trans (Finset.card_image_le.trans (List.toFinset_card_le zs))
    have enough := count onto
    cases todo with
    | nil => change T.card≤0 at enough; omega
    | cons a xs =>
      let t := owner a
      let take := xs.filter (fun x => decide (owner x=t))
      let rest := xs.filter (fun x => !(decide (owner x=t)))
      have mt : t∈T := lands a List.mem_cons_self
      have ins (w) : w∈take ↔ w∈xs ∧ owner w=t := by simp [take]
      have out (w) : w∈rest ↔ w∈xs ∧ owner w≠t := by simp [rest]
      have pa (w) (hw : w∈a::take) : owner w=t := by
        rcases List.mem_cons.mp hw with rfl|m
        · rfl
        · exact ((ins w).mp m).2
      have extn (w) (hw : w∈closed++rest) : owner w≠t := by
        rcases List.mem_append.mp hw with m|m
        · intro eq
          exact past w m (eq.symm ▸ mt)
        · exact ((out w).mp m).2
      have all (w) (hw : w∈S) : w∈a::take ∨ w∈closed++rest := by
        rcases cover w hw with m|m
        · rcases List.mem_cons.mp m with rfl|m
          · exact Or.inl List.mem_cons_self
          by_cases e : owner w=t
          · exact Or.inl (List.mem_cons_of_mem _ ((ins w).mpr ⟨m,e⟩))
          · exact Or.inr (List.mem_append_right _ ((out w).mpr ⟨m,e⟩))
        · exact Or.inr (List.mem_append_left _ m)
      have accepted := good t mt (a::take) (closed++rest) pa extn all
      have ksize : (T.erase t).card=k := by rw [Finset.card_erase_of_mem mt,size]; omega
      have remains (g) (m : g∈T.erase t) : ∃ w∈rest, owner w=g := by
        obtain ⟨ne,mg⟩ := Finset.mem_erase.mp m
        obtain ⟨w,wm,e⟩ := onto g mg
        have no : owner w≠t := fun eq => ne (e.symm.trans eq)
        rcases List.mem_cons.mp wm with rfl|wm
        · exact (no rfl).elim
        · exact ⟨w,(out w).mpr ⟨wm,no⟩,e⟩
      have next := ih (T.erase t) ksize rest ((a::take)++closed) (by
        intro w m
        obtain ⟨mw,n⟩ := (out w).mp m
        exact Finset.mem_erase.mpr ⟨n,lands w (List.mem_cons_of_mem _ mw)⟩) (by
        intro w mw hit
        rcases List.mem_append.mp mw with early|old
        · exact (Finset.mem_erase.mp hit).1 (pa w early)
        · exact past w old (Finset.mem_erase.mp hit).2) remains (by
        intro w m
        rcases all w m with assigned|q
        · exact Or.inr (List.mem_append_left _ assigned)
        rcases List.mem_append.mp q with old|untouched
        · exact Or.inr (List.mem_append_right _ old)
        · exact Or.inl untouched) (by
        intro g m
        exact good g (Finset.mem_erase.mp m).2)
      have options : (take,rest)∈splits xs := take_split _ _
      have length := count remains
      rw [ksize] at length
      simp only [possible]
      split
      · rfl
      · split
        · simp only [List.length_cons] at enough
          omega
        · apply List.any_eq_true.mpr
          refine ⟨(take,rest),options,?_⟩
          exact Bool.and_eq_true_iff.mpr
            ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true length,accepted⟩,next⟩

end CoBlockPartition4482

namespace CoBlockPhysical4482
open CoPortTrace4482 CoTightBlocks4482
open CoBitBlock4482 (Mark Row bit)

variable {W X : Type} [DecidableEq W]

theorem no_pair {ev : W → X → Bool} {S T : Finset W}
    (B : Blocks ev S T) (lo hi : Row → X) (mark : W → Mark)
    (pos : ∀ w i, bit (mark w).1 i=ev w (hi i))
    (neg : ∀ w i, bit (mark w).2 i=ev w (lo i))
    (ord : ∀ i w, w∈S → ev w (lo i)=true → ev w (hi i)=true)
    (det : ∀ i, ∃ w∈T, ev w (lo i)≠ev w (hi i))
    {t : W} (mt : t∈T) (i j : Row)
    (out : ∀ w∈S, B.owner w≠t →
      bit (mark w).1 i=bit (mark w).2 i ∧ bit (mark w).1 j=bit (mark w).2 j)
    (inside : ∀ w∈S, B.owner w=t →
      bit (mark w).1 i=true → bit (mark w).2 j=true) : False := by
  have ei : exclusive B t (lo i) (hi i) := by
    intro w mw offt
    rw [←neg w i,←pos w i]
    exact (out w mw offt).1.symm
  have ej : exclusive B t (lo j) (hi j) := by
    intro w mw offt
    rw [←neg w j,←pos w j]
    exact (out w mw offt).2.symm
  obtain ⟨w,mw,wt,p,n⟩ := block_obstruction B mt ei ej (ord i) (ord j) (det i) (det j)
  have p' : bit (mark w).1 i=true := (pos w i).trans p
  have n' : bit (mark w).2 j=false := (neg w j).trans n
  have both := inside w mw wt p'
  rw [n'] at both
  contradiction

theorem physical_possible {ev : W → X → Bool} {join : Bool → W → W → W}
    {stop : Finset W → Prop} (app : ∀ d a b x, ev (join d a b) x =
      if d then ev a x || ev b x else ev a x && ev b x)
    {cap k : Nat} {S : Finset W} (terminal : ∀ T, stop T → T.card≤cap)
    (run : Path join stop k S) (tight : S.card=cap+k)
    (lo hi : Row → X) (mark : W → Mark)
    (pos : ∀ w i, bit (mark w).1 i=ev w (hi i))
    (neg : ∀ w i, bit (mark w).2 i=ev w (lo i))
    (ord : ∀ i w, w∈S → ev w (lo i)=true → ev w (hi i)=true)
    (det : ∀ T, stop T → ∀ i, ∃ w∈T, ev w (lo i)≠ev w (hi i))
    (ws : List W) (live : ∀ w, w∈ws ↔ w∈S) :
    CoBlockPartition4482.possible
      (fun ins outs : List W =>
        !(CoBitBlock4482.invalid (ins.map mark) (outs.map mark))) cap ws []=true := by
  classical
  obtain ⟨T,st,sz,⟨B⟩⟩ := partition ev app cap terminal run tight
  apply CoBlockPartition4482.possible_of_owner _ B.owner S cap T sz ws []
  · intro w m
    exact B.lands w ((live w).mp m)
  · simp
  · intro t mt
    obtain ⟨w,m,e⟩ := B.onto t mt
    exact ⟨w,(live w).mpr m,e⟩
  · exact fun w m => Or.inl ((live w).mpr m)
  · intro t mt ins outside inward outward covered
    change !(CoBitBlock4482.invalid (ins.map mark) (outside.map mark))=true
    cases h : CoBitBlock4482.invalid (ins.map mark) (outside.map mark) with
    | false => rfl
    | true =>
      obtain ⟨i,j,out,inside⟩ := CoBitBlock4482.invalid_witness _ _ h
      exfalso
      apply no_pair B lo hi mark pos neg ord (det T st) mt i j
      · intro w m ne
        rcases covered w m with inside'|outside'
        · exact (ne (inward w inside')).elim
        · exact out _ (List.mem_map.mpr ⟨w,outside',rfl⟩)
      · intro w m e
        rcases covered w m with inside'|outside'
        · exact inside _ (List.mem_map.mpr ⟨w,inside',rfl⟩)
        · exact (outward w outside' e).elim

end CoBlockPhysical4482

namespace CoSevenAnchors4482
open CoTightBlocks4482 CoBitBlock4482 CoBlockIntervals4482
variable {W X : Type} [DecidableEq W]

theorem anchored_block {ev : W → X → Bool} {S T : Finset W}
    (B : Blocks ev S T) (A : Finset W) (sub : A⊆S) (many : T.card<A.card) :
    ∃ t∈T, ∃ a∈A, ∃ b∈A, a≠b ∧ B.owner a=t ∧ B.owner b=t ∧
      (S.filter (fun w => B.owner w=t)).card + (T.card-1) ≤ S.card := by
  classical
  let f : ↥A → ↥T := fun x => ⟨B.owner x.val, B.lands _ (sub x.property)⟩
  have collision : ∃ x y : ↥A, x≠y ∧ f x=f y := by
    by_contra no
    have inj : Function.Injective f := by
      intro x y e
      by_contra ne
      exact no ⟨x,y,ne,e⟩
    have small : A.card≤T.card := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f inj
    omega
  obtain ⟨a,b,ab,same⟩ := collision
  let t := B.owner a.val
  have ht : t∈T := B.lands _ (sub a.property)
  have bt : B.owner b.val=t := (congrArg Subtype.val same).symm
  let block := S.filter (fun w => B.owner w=t)
  have small : block⊆S := Finset.filter_subset _ _
  have loaded : T.erase t ⊆ (S \ block).image B.owner := by
    intro z mz
    obtain ⟨ne,mz⟩ := Finset.mem_erase.mp mz
    obtain ⟨w,mw,e⟩ := B.onto z mz
    have off : w∉block := by
      intro hit
      exact ne (e.symm.trans (Finset.mem_filter.mp hit).2)
    exact Finset.mem_image.mpr ⟨w,Finset.mem_sdiff.mpr ⟨mw,off⟩,e⟩
  have count := (Finset.card_le_card loaded).trans Finset.card_image_le
  rw [Finset.card_erase_of_mem ht,Finset.card_sdiff_of_subset small] at count
  have blocksize := Finset.card_le_card small
  exact ⟨t,ht,a.val,a.property,b.val,b.property,fun h => ab (Subtype.ext h),
    rfl,bt,by change block.card+(T.card-1)≤S.card; omega⟩

theorem covered_impossible {ev : W → X → Bool} {S T : Finset W}
    (B : Blocks ev S T) (lo hi : Row → X) (mark : W → Mark)
    (pos : ∀ w i, bit (mark w).1 i=ev w (hi i))
    (neg : ∀ w i, bit (mark w).2 i=ev w (lo i))
    (ord : ∀ i w, w∈S → ev w (lo i)=true → ev w (hi i)=true)
    (det : ∀ i, ∃ w∈T, ev w (lo i)≠ev w (hi i))
    (A : Finset W) (sub : A⊆S) (many : T.card<A.card)
    {k : Nat} (col : W → Col k) (cols : List (Col k))
    (incl : ∀w∈S,col w∈cols) (marks : ∀w∈S,(col w).data=mark w)
    (pairs : List (Row×Row)) (must : BitVec k) (verified : must &&& cover cols pairs=must)
    (slots : ∀ t∈T, ∀ a∈A, ∀ b∈A, a≠b → B.owner a=t → B.owner b=t →
      (S.filter (fun w => B.owner w=t)).card+(T.card-1)≤S.card →
      ∃ j : Fin k, must.getLsbD j.val=true ∧
        ∀ w∈S, (col w).inc.getLsbD j.val=decide (B.owner w=t)) : False := by
  obtain ⟨t,mt,a,ma,b,mb,ab,oa,ob,sz⟩ := anchored_block B A sub many
  obtain ⟨j,yes,eq⟩ := slots _ mt _ ma _ mb ab oa ob sz
  obtain ⟨i,i',hit⟩ := required_witness cols pairs must verified j yes
  apply CoBlockPhysical4482.no_pair B lo hi mark pos neg ord det mt i i'
  · intro w mw outside
    have zero : (col w).inc.getLsbD j.val=false := by rw [eq w mw]; exact decide_eq_false outside
    have h := (hit _ (incl w mw)).1 zero
    rw [marks w mw] at h
    exact h
  · intro w mw inside
    have one : (col w).inc.getLsbD j.val=true := by rw [eq w mw]; exact decide_eq_true inside
    have h := (hit _ (incl w mw)).2 one
    rw [marks w mw] at h
    exact h

end CoSevenAnchors4482

namespace CoBlockSlots4482
open CoTightBlocks4482 CoBitBlock4482 CoBlockIntervals4482

def pack {n : Nat} (f : Fin n → Bool) : Fin (2^n) :=
  (BitVec.ofBoolListLE (List.ofFn f)).toFin.cast (by simp [List.length_ofFn])

theorem pack_bit {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (pack f).val.testBit i.val=f i := by
  change (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

def members {n : Nat} (j : Fin (2^n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => j.val.testBit i.val=true

theorem impossible {W X : Type} [DecidableEq W] {ev : W → X → Bool} {S T : Finset W}
    (B : Blocks ev S T) (lo hi : Row → X) (mark : W → Mark)
    (pos : ∀ w i, bit (mark w).1 i=ev w (hi i))
    (neg : ∀ w i, bit (mark w).2 i=ev w (lo i))
    (ord : ∀ i w, w∈S → ev w (lo i)=true → ev w (hi i)=true)
    (det : ∀ i, ∃ w∈T, ev w (lo i)≠ev w (hi i))
    {n : Nat} (e : Fin n ≃ ↥S) (core : Finset (Fin n)) (many : T.card<core.card)
    (inc : Fin n → BitVec (2^n))
    (digits : ∀ i (j : Fin (2^n)), (inc i).getLsbD j.val=j.val.testBit i.val)
    (must : BitVec (2^n)) (need : ∀ j : Fin (2^n),
      (members j).card+(T.card-1)≤S.card → 2≤((members j)∩core).card →
      must.getLsbD j.val=true)
    (pairs : List (Row×Row)) (verified : must &&& cover
      (List.ofFn (fun i : Fin n => (⟨mark (e i).val,inc i⟩ : Col (2^n)))) pairs=must) :
    False := by
  classical
  let value := fun i : Fin n => (e i).val
  have inj : Function.Injective value := fun _ _ h => e.injective (Subtype.ext h)
  let A := core.image value
  have sub : A⊆S := by
    intro w mw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp mw
    exact (e i).property
  have cA : A.card=core.card := Finset.card_image_of_injective _ inj
  obtain ⟨t,mt,a,ma,b,mb,ab,oa,ob,sz⟩ :=
    CoSevenAnchors4482.anchored_block B A sub (by omega)
  let block := S.filter (fun w => B.owner w=t)
  let pred := fun i : Fin n => decide (B.owner (value i)=t)
  let j := pack pred
  have digit (i : Fin n) : j.val.testBit i.val=decide (B.owner (value i)=t) := pack_bit pred i
  have mem (i : Fin n) : i∈members j ↔ B.owner (value i)=t := by
    simp [members,digit]
  let embed : ↥(members j) → ↥block := fun z =>
    ⟨value z.val,Finset.mem_filter.mpr ⟨(e z.val).property,(mem _).mp z.property⟩⟩
  have inj2 : Function.Injective embed := by
    intro x y eq
    apply Subtype.ext
    apply inj
    exact congrArg (fun z : ↥block => (z.val : W)) eq
  have small : (members j).card≤block.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective embed inj2
  have sm : (members j).card+(T.card-1)≤S.card := by
    change block.card+(T.card-1)≤S.card at sz
    omega
  obtain ⟨i,mi,ia⟩ := Finset.mem_image.mp ma
  obtain ⟨h,mh,hb⟩ := Finset.mem_image.mp mb
  have it : i∈members j := (mem i).mpr (by rw [ia]; exact oa)
  have ht : h∈members j := (mem h).mpr (by rw [hb]; exact ob)
  have enough : 1<((members j)∩core).card := Finset.one_lt_card.mpr
    ⟨i,Finset.mem_inter.mpr ⟨it,mi⟩,h,Finset.mem_inter.mpr ⟨ht,mh⟩,
      fun eq => ab (ia.symm.trans ((congrArg value eq).trans hb))⟩
  obtain ⟨r,s,hit⟩ := required_witness _ pairs must verified j (need j sm enough)
  let col (l : Fin n) := (⟨mark (value l), inc l⟩ : Col (2^n))
  have found (w : W) (mw : w∈S) : ∃ l : Fin n, value l=w ∧ col l∈List.ofFn col := by
    let l := e.symm ⟨w,mw⟩
    refine ⟨l,?_,List.mem_ofFn.mpr ⟨l,rfl⟩⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨w,mw⟩)
  apply CoBlockPhysical4482.no_pair B lo hi mark pos neg ord det mt r s
  · intro w mw offt
    obtain ⟨l,lw,ml⟩ := found w mw
    have sign : (inc l).getLsbD j.val=false := by rw [digits,digit,lw]; exact decide_eq_false offt
    have z := (hit (col l) ml).1 sign
    change bit (mark (value l)).1 r=bit (mark (value l)).2 r ∧
      bit (mark (value l)).1 s=bit (mark (value l)).2 s at z
    simpa only [lw] using z
  · intro w mw ont
    obtain ⟨l,lw,ml⟩ := found w mw
    have sign : (inc l).getLsbD j.val=true := by rw [digits,digit,lw]; exact decide_eq_true ont
    have z := (hit (col l) ml).2 sign
    change bit (mark (value l)).1 r=true → bit (mark (value l)).2 s=true at z
    simpa only [lw] using z

end CoBlockSlots4482

namespace CoImplicitBlock4482
open CoBitBlock4482 CoBlockIntervals4482

def least {n : Nat} (w : BitVec n) : Nat := (w &&& (-w)).toNat.log2
def pickRow (w : Bits) : Row := ⟨least w % 258,Nat.mod_lt _ (by decide)⟩

def findPair : List Mark → Bits → Bits → Option (Row×Row)
  | [],p,n => if p=0 ∨ n=0 then none else some (pickRow p,pickRow n)
  | w::ws,p,n =>
    if p=0 ∨ n=0 then none else
      match findPair ws (p &&& ~~~w.1) n with
      | some r => some r
      | none => findPair ws (p &&& w.1) (n &&& w.2)

def propose {k} (cols : List (Col k)) (j : Nat) : Option (Row×Row) :=
  let inside := (cols.filter fun c => c.inc.getLsbD j).map Col.data
  let es := cols.foldr (fun c v => if c.inc.getLsbD j then v else avoid c.data v)
    (BitVec.allOnes 258)
  findPair inside es es

def check {k} (cols : List (Col k)) : Nat → BitVec k → Bool
  | 0,m => m==0
  | fuel+1,m =>
    if m=0 then true else
    match propose cols (least m) with
    | none => false
    | some (r,s) => check cols fuel (m &&& ~~~(interval r s cols))

theorem check_sound {k} (cols : List (Col k)) (fuel : Nat) (m : BitVec k)
    (h : check cols fuel m=true) : ∃ pairs : List (Row×Row), m &&& cover cols pairs=m := by
  induction fuel generalizing m with
  | zero =>
    have off : m=0 := beq_iff_eq.mp h
    exact ⟨[],by simp [off]⟩
  | succ fuel ih =>
    by_cases off : m=0
    · exact ⟨[],by simp [off]⟩
    cases guess : propose cols (least m) with
    | none => simp only [check,if_neg off,guess,Bool.false_eq_true] at h
    | some rs =>
      obtain ⟨r,s⟩ := rs
      simp only [check,if_neg off,guess] at h
      obtain ⟨pairs,covered⟩ := ih _ h
      refine ⟨(r,s)::pairs,?_⟩
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      have old := congrArg (fun v : BitVec k => v.getLsbD j) covered
      simp only [cover,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,
        hj,decide_true,Bool.true_and] at old ⊢
      cases v : m.getLsbD j <;> cases t : (interval r s cols).getLsbD j <;>
        cases p : (cover cols pairs).getLsbD j <;> simp_all

end CoImplicitBlock4482

namespace CoSmallTail4482
open CoBitBlock4482 CoPortTrace4482

def merge (d : Bool) (a b : Mark) : Mark :=
  if d then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)

def changed (w : Mark) := w.1 ^^^ w.2
def coverage : List Mark → Bits
  | [] => 0
  | a::xs => changed a ||| coverage xs

def picks {α : Type} : List α → List (α × List α)
  | [] => []
  | x::xs => (x,xs)::((picks xs).map fun (a,r) => (a,x::r))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | x::xs => ((picks xs).map fun (y,r) => (x,y,r)) ++
    ((pairs xs).map fun (a,b,r) => (a,b,x::r))

def solve : Nat → List Mark → Bool
  | 0,ws => coverage ws == BitVec.allOnes 258
  | k+1,ws =>
    coverage ws == BitVec.allOnes 258 && (pairs ws).any fun (a,b,r) =>
      solve k (merge false a b :: r) || solve k (merge true a b :: r)

private theorem take_one {W : Type} (mark : W→Mark) (w : W) (ws : List W) (m : w∈ws) :
    ∃ rest : List W, (mark w,rest.map mark)∈picks (ws.map mark) ∧
      ∀ z∈ws, z≠w → z∈rest := by
  induction ws with
  | nil => simp at m
  | cons a ws ih =>
    rcases List.mem_cons.mp m with eq|old
    · subst w
      refine ⟨ws,by simp [picks],?_⟩
      intro z mz ne
      exact (List.mem_cons.mp mz).resolve_left ne
    · obtain ⟨r,mr,keep⟩ := ih old
      refine ⟨a::r,?_,?_⟩
      · apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨_,mr,rfl⟩
      · intro z mz ne
        rcases List.mem_cons.mp mz with rfl|mz
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (keep z mz ne)

private theorem take_pair {W : Type} (mark : W→Mark) (a b : W) (ab : a≠b)
    (ws : List W) (ma : a∈ws) (mb : b∈ws) :
    ∃ x y r, (x=a ∧ y=b ∨ x=b ∧ y=a) ∧
      (mark x,mark y,List.map mark r) ∈ pairs (ws.map mark) ∧
      ∀ z∈ws, z≠a → z≠b → z∈r := by
  classical
  induction ws with
  | nil => simp at ma
  | cons v vs ih =>
    by_cases va : v=a
    · subst v
      have mbr := (List.mem_cons.mp mb).resolve_left (Ne.symm ab)
      obtain ⟨r,mr,keep⟩ := take_one mark b vs mbr
      refine ⟨a,b,r,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨_,mr,rfl⟩
      · intro z mz na nb
        exact keep z ((List.mem_cons.mp mz).resolve_left na) nb
    by_cases vb : v=b
    · subst v
      have mar := (List.mem_cons.mp ma).resolve_left ab
      obtain ⟨r,mr,keep⟩ := take_one mark a vs mar
      refine ⟨b,a,r,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨_,mr,rfl⟩
      · intro z mz na nb
        exact keep z ((List.mem_cons.mp mz).resolve_left nb) na
    obtain ⟨x,y,r,orient,mr,keep⟩ := ih
      ((List.mem_cons.mp ma).resolve_left (Ne.symm va)) ((List.mem_cons.mp mb).resolve_left (Ne.symm vb))
    refine ⟨x,y,v::r,orient,?_,?_⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨_,mr,rfl⟩
    · intro z mz na nb
      rcases List.mem_cons.mp mz with rfl|mz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (keep z mz na nb)

private theorem merge_comm (d : Bool) (a b : Mark) : merge d a b=merge d b a := by
  cases d <;> simp [merge,BitVec.and_comm,BitVec.or_comm]

private theorem read_coverage {w : Mark} {ws : List Mark} {i : Row} (mw : w∈ws)
    (diff : bit w.1 i≠bit w.2 i) : bit (coverage ws) i=true := by
  induction ws with
  | nil => simp at mw
  | cons a ws ih =>
    simp only [bit,coverage,BitVec.getLsbD_or]
    rcases List.mem_cons.mp mw with eq|m
    · subst w
      apply Bool.or_eq_true_iff.mpr
      left
      simp only [changed,BitVec.getLsbD_xor]
      change (Bool.xor (bit a.1 i) (bit a.2 i))=true
      cases x : bit a.1 i <;> cases y : bit a.2 i <;> simp_all
    · exact Bool.or_eq_true_iff.mpr (Or.inr (ih m))

private theorem all_coverage {ws : List Mark}
    (full : ∀ i : Row, ∃ w∈ws, bit w.1 i≠bit w.2 i) :
    coverage ws=BitVec.allOnes 258 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨w,m,d⟩ := full ⟨i,hi⟩
  simp only [BitVec.getLsbD_allOnes,hi,decide_true]
  exact read_coverage m d

variable {W : Type} [DecidableEq W] {join : Bool→W→W→W} {stop : Finset W→Prop}

private theorem edge_kept (mark : W→Mark)
    (hom : ∀d a b, mark (join d a b)=merge d (mark a) (mark b))
    (terminal : ∀T,stop T → ∀i : Row, ∃w∈T, bit (mark w).1 i≠bit (mark w).2 i)
    {k S} (path : Path join stop k S) (i : Row) :
    ∃w∈S,bit (mark w).1 i≠bit (mark w).2 i := by
  induction path with
  | final S h => exact terminal S h i
  | @step _ U d a b ne fresh tail ih =>
    obtain ⟨z,m,dh⟩ := ih
    rcases Finset.mem_insert.mp m with rfl|m
    · by_cases da : bit (mark a).1 i≠bit (mark a).2 i
      · exact ⟨a,Finset.mem_insert_self _ _,da⟩
      · refine ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),?_⟩
        intro db
        apply dh
        have ea : bit (mark a).1 i=bit (mark a).2 i := by simpa using da
        rw [hom]
        cases d <;> simp only [merge,Bool.false_eq_true,↓reduceIte,bit,
          BitVec.getLsbD_and,BitVec.getLsbD_or] at ea db ⊢ <;> rw [ea,db]
    · exact ⟨z,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m),dh⟩

theorem physical (mark : W→Mark)
    (hom : ∀d a b, mark (join d a b)=merge d (mark a) (mark b))
    (cap : Nat) (bound : ∀T,stop T → T.card≤cap)
    (terminal : ∀T,stop T → ∀i : Row, ∃w∈T, bit (mark w).1 i≠bit (mark w).2 i)
    {k S} (path : Path join stop k S) (tight : S.card=cap+k)
    (ws : List W) (haveAll : ∀w∈S,w∈ws) : solve k (ws.map mark)=true := by
  let full : ∀ {j R}, Path join stop j R → ∀ vs : List W, (∀w∈R,w∈vs) →
      coverage (vs.map mark)=BitVec.allOnes 258 := by
    intro j R p vs hv
    apply all_coverage
    intro i
    obtain ⟨w,mw,d⟩ := edge_kept mark hom terminal p i
    exact ⟨mark w,List.mem_map.mpr ⟨w,hv w mw,rfl⟩,d⟩
  induction path generalizing ws with
  | final S h =>
    simp [solve,full (Path.final S h) ws haveAll]
  | @step k U d a b ab fresh tail ih =>
    have seen := full (Path.step d a b ab fresh tail) ws haveAll
    have hz : join d a b∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have up := width bound tail
    have cn := Finset.card_insert_of_notMem hz
    have ca := Finset.card_insert_le a (insert b U)
    have cb := Finset.card_insert_le b U
    have top : (insert (join d a b) U).card=cap+k := by omega
    have na : a∉U := by
      intro m
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem m)] at tight
      omega
    have nb : b∉U := by
      intro m
      rw [Finset.insert_eq_of_mem m] at tight
      have c := Finset.card_insert_le a U
      omega
    obtain ⟨x,y,r,o,m,keep⟩ := take_pair mark a b ab ws
      (haveAll _ (Finset.mem_insert_self _ _))
      (haveAll _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    have next := ih top (join d a b::r) (by
      intro z mz
      rcases Finset.mem_insert.mp mz with rfl|old
      · exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ (keep z (haveAll z (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem old))) (fun h => na (h ▸ old)) (fun h => nb (h ▸ old))))
    have align : mark (join d a b)=merge d (mark x) (mark y) := by
      rcases o with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact hom _ _ _
      · exact (hom _ _ _).trans (merge_comm _ _ _)
    simp only [List.map_cons,align] at next
    simp only [solve,seen,beq_self_eq_true,Bool.true_and]
    apply List.any_eq_true.mpr
    refine ⟨_,m,?_⟩
    cases d
    · exact Bool.or_eq_true_iff.mpr (Or.inl next)
    · exact Bool.or_eq_true_iff.mpr (Or.inr next)

end CoSmallTail4482

namespace CoActualTight4482
open CoPortRoots4482 CoPortTrace4482 CoPortCut4482 CoTightBlocks4482
open CoBitBlock4482 CoBlockIntervals4482 CoPortEdgeRows4482 CoBlockSlots4482

theorem implicit_excludes {S : Finset W} {k n : Nat} (tight : S.card=6+k)
    (ordered : ∀w∈S,Ordered w)
    (e : Fin n ≃ ↥S) (vals : Fin n→Mark) (same : ∀i,vals i=mark (e i).val)
    (core : Finset (Fin n)) (many : 6<core.card)
    (inc : Fin n → BitVec (2^n))
    (digits : ∀i (j : Fin (2^n)), (inc i).getLsbD j.val=j.val.testBit i.val)
    (must : BitVec (2^n)) (need : ∀ j : Fin (2^n),
      (members j).card+5≤S.card → 2≤((members j)∩core).card → must.getLsbD j.val=true)
    (fuel : Nat) (accepted : CoImplicitBlock4482.check
      (List.ofFn (fun i => (⟨vals i,inc i⟩ : Col (2^n)))) fuel must=true) :
    ¬Path join (cleanCut model label 6) k S := by
  intro path
  obtain ⟨T,st,sz,⟨B⟩⟩ := partition cell model.applyJoin 6 (fun _ h => h.1) path tight
  obtain ⟨pairs,valid⟩ := CoImplicitBlock4482.check_sound _ _ _ accepted
  have cols : vals=(fun i => mark (e i).val) := funext same
  rw [cols] at valid
  apply impossible B lower upper mark positive negative (fun i w hw => ordered w hw i)
    (terminal_dist T st) e core (by omega) inc digits must _ pairs valid
  intro j bound a
  apply need j _ a
  simpa [sz] using bound

theorem small_excludes {S : Finset W} {k : Nat} (tight : S.card=6+k)
    (ws : List W) (haveAll : ∀w∈S,w∈ws)
    (rejected : CoSmallTail4482.solve k (ws.map mark)=false) :
    ¬Path join (cleanCut model label 6) k S := by
  intro path
  have h := CoSmallTail4482.physical mark mark_gate 6 (fun _ st => st.1)
    terminal_mark path tight ws haveAll
  rw [rejected] at h
  contradiction

end CoActualTight4482

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
  change (bit a i && bit b i)=bit a i at q
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

end CoGroupBlock4482

namespace CoActualGroup4482
open CoPortRoots4482 CoPortTrace4482 CoPortCut4482 CoTightBlocks4482
open CoBitBlock4482 CoBlockIntervals4482 CoPortEdgeRows4482 CoBlockSlots4482
open CoGroupBlock4482

theorem group_excludes {S : Finset W} {k n : Nat} (tight : S.card=6+k)
    (ordered : ∀w∈S,Ordered w)
    (e : Fin n ≃ ↥S) (vals : Fin n→Mark) (same : ∀i,vals i=mark (e i).val)
    (big : Fin n→Box) (bounded : ∀i,fits (big i) (vals i)=true)
    (core : Finset (Fin n)) (many : 6<core.card)
    (inc : Fin n→BitVec (2^n))
    (digits : ∀i (j : Fin (2^n)), (inc i).getLsbD j.val=j.val.testBit i.val)
    (must : BitVec (2^n)) (need : ∀ j : Fin (2^n),
      (members j).card+5≤S.card → 2≤((members j)∩core).card → must.getLsbD j.val=true)
    (fuel : Nat) (accepted : checkGroup
      (List.ofFn (fun i => (⟨big i,inc i⟩ : BCol (2^n)))) fuel must=true) :
    ¬Path join (cleanCut model label 6) k S := by
  intro path
  obtain ⟨T,st,sz,⟨B⟩⟩ := partition cell model.applyJoin 6 (fun _ h => h.1) path tight
  obtain ⟨pairs,valid⟩ := for_member (List.ofFn (fun i : Fin n => i)) big vals inc
    (fun i _ => bounded i) fuel must (by simpa only [List.map_ofFn,Function.comp_def] using accepted)
  have cols : vals=(fun i => mark (e i).val) := funext same
  simp only [List.map_ofFn,Function.comp_def,cols] at valid
  apply impossible B lower upper mark positive negative (fun i w hw => ordered w hw i)
    (terminal_dist T st) e core (by omega) inc digits must _ pairs valid
  intro j bound a
  apply need j _ a
  simpa [sz] using bound

end CoActualGroup4482

namespace CoMaskShape4482

def ofBits {k : Nat} (f : Fin k→Bool) : BitVec k :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem ofBits_at {k : Nat} (f : Fin k→Bool) (j : Fin k) :
    (ofBits f).getLsbD j.val=f j := by
  simp only [ofBits,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]

def atMost {k : Nat} : List (BitVec k) → Nat → BitVec k
  | [],_ => BitVec.allOnes k
  | a::xs,0 => (~~~a) &&& atMost xs 0
  | a::xs,h+1 => ifTrue a (atMost xs h) (atMost xs (h+1))
where
  ifTrue (a y n : BitVec k) := (a &&& y) ||| ((~~~a) &&& n)

theorem atMost_get {k} (ws : List (BitVec k)) (j : Fin k) (h : Nat) :
    (atMost ws h).getLsbD j.val =
      decide ((ws.filter (fun a => a.getLsbD j.val)).length≤h) := by
  induction ws generalizing h with
  | nil => simp only [atMost,BitVec.getLsbD_allOnes,j.isLt,decide_true,
      List.filter_nil,List.length_nil,Nat.zero_le]
  | cons a xs ih =>
    cases h with
    | zero =>
      cases b : a.getLsbD j.val <;>
        simp only [atMost,BitVec.getLsbD_and,BitVec.getLsbD_not,j.isLt,decide_true,Bool.true_and,b,ih,List.filter_cons] <;> simp
    | succ h =>
      cases b : a.getLsbD j.val <;>
        simp only [atMost,atMost.ifTrue,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,
          j.isLt,decide_true,Bool.true_and,b,ih,List.filter_cons] <;> simp

end CoMaskShape4482

namespace CoAnchorMask4482
open CoBlockSlots4482

def levels {k : Nat} : List (BitVec k) → BitVec k × BitVec k
  | [] => (0,0)
  | a::xs =>
    let rest := levels xs
    (a ||| rest.1,(a &&& rest.1) ||| rest.2)

private theorem first {k : Nat} (cols : List (BitVec k)) (j : Fin k)
    (x : BitVec k) (m : x∈cols) (v : x.getLsbD j.val=true) :
    (levels cols).1.getLsbD j.val=true := by
  induction cols with
  | nil => simp at m
  | cons a xs ih =>
    simp only [levels,BitVec.getLsbD_or,Bool.or_eq_true]
    rcases List.mem_cons.mp m with e|e
    · exact Or.inl (e ▸ v)
    · exact Or.inr (ih e)

private theorem second {A : Type} {k : Nat} (cols : List A) (val : A→BitVec k) (j : Fin k)
    (a b : A) (ab : a≠b) (ma : a∈cols) (mb : b∈cols)
    (pa : (val a).getLsbD j.val=true) (pb : (val b).getLsbD j.val=true) :
    (levels (cols.map val)).2.getLsbD j.val=true := by
  induction cols with
  | nil => simp at ma
  | cons h t ih =>
    simp only [List.map_cons,levels,BitVec.getLsbD_or,BitVec.getLsbD_and,
      Bool.or_eq_true,Bool.and_eq_true]
    rcases List.mem_cons.mp ma with ah|tailA
    · subst h
      have tail := (List.mem_cons.mp mb).resolve_left (Ne.symm ab)
      exact Or.inl ⟨pa,first _ j _ (List.mem_map.mpr ⟨b,tail,rfl⟩) pb⟩
    rcases List.mem_cons.mp mb with bh|tailB
    · exact Or.inl ⟨bh ▸ pb,first _ j _ (List.mem_map.mpr ⟨a,tailA,rfl⟩) pa⟩
    · exact Or.inr (ih tailA tailB)

def mask {n : Nat} (width : BitVec (2^n)) (inc : Fin n → BitVec (2^n))
    (anchors : List (Fin n)) : BitVec (2^n) := width &&& (levels (anchors.map inc)).2

theorem twoOn {A : Type} {k : Nat} (cols : List A) (val : A→BitVec k) (j : Fin k)
    (a b : A) (ab : a≠b) (ma : a∈cols) (mb : b∈cols)
    (pa : (val a).getLsbD j.val=true) (pb : (val b).getLsbD j.val=true) :
    (levels (cols.map val)).2.getLsbD j.val=true :=
  second cols val j a b ab ma mb pa pb

theorem needed {n : Nat} (width : BitVec (2^n)) (inc : Fin n → BitVec (2^n))
    (anchors : List (Fin n)) (digits : ∀i (j : Fin (2^n)), (inc i).getLsbD j.val=j.val.testBit i.val)
    (j : Fin (2^n)) (allowed : width.getLsbD j.val=true)
    (two : 2≤((members j)∩anchors.toFinset).card) :
    (mask width inc anchors).getLsbD j.val=true := by
  obtain ⟨a,ma,b,mb,ab⟩ := Finset.one_lt_card.mp two
  obtain ⟨av,aa⟩ := Finset.mem_inter.mp ma
  obtain ⟨bv,bb⟩ := Finset.mem_inter.mp mb
  have digit (x : Fin n) (m : x∈members j) : (inc x).getLsbD j.val=true := by
    rw [digits]
    exact (Finset.mem_filter.mp m).2
  have ge := second anchors inc j a b ab (List.mem_toFinset.mp aa) (List.mem_toFinset.mp bb)
    (digit a av) (digit b bv)
  simp [mask,BitVec.getLsbD_and,allowed,ge]

end CoAnchorMask4482

namespace CoGlobalShape4482
open CoMaskShape4482 CoAnchorMask4482 CoBlockSlots4482

private theorem count_map {A B : Type} (xs : List A) (f : A→B) (p : B→Bool) :
    ((xs.map f).filter p).length=(xs.filter (fun x => p (f x))).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : p (f a) <;> simp only [List.map_cons,List.filter_cons,h,Bool.false_eq_true,
      ↓reduceIte,List.length_cons,ih]

def required {n} (ids anchors : List (Fin n)) (inc : Fin n→BitVec (2^n)) : BitVec (2^n) :=
  mask (atMost (ids.map inc) (n-5)) inc anchors

theorem required_at {n} (ids anchors : List (Fin n)) (inc : Fin n→BitVec (2^n))
    (nd : ids.Nodup) (complete : ∀i,i∈ids)
    (digits : ∀i (j : Fin (2^n)), (inc i).getLsbD j.val=j.val.testBit i.val)
    (j : Fin (2^n)) (small : (members j).card+5≤n)
    (two : 2≤((members j)∩anchors.toFinset).card) :
    (required ids anchors inc).getLsbD j.val=true := by
  apply needed _ inc anchors digits j _ two
  rw [atMost_get,count_map]
  let filtered := ids.filter (fun i => (inc i).getLsbD j.val)
  have dis : filtered.Nodup := nd.filter _
  have equal : filtered.toFinset=members j := by
    ext i
    simp only [List.mem_toFinset,filtered,List.mem_filter,members,Finset.mem_filter,
      Finset.mem_univ,true_and,digits]
    exact and_iff_right (complete i)
  have count := List.toFinset_card_of_nodup dis
  rw [equal] at count
  change decide (filtered.length≤n-5)=true
  apply decide_eq_true
  omega

end CoGlobalShape4482

namespace CoJunctionLeaf4482
open CoPortRoots4482 CoPortFrontier4482 CoPortTrace4482 CoPortCut4482
open CoBlockSlots4482 CoBitBlock4482 CoGroupBlock4482 CoJunctionLogical4482

noncomputable def slots {n : Nat} (v : Fin n → W) (inj : Function.Injective v) :
    Fin n ≃ ↥((List.ofFn v).toFinset) :=
  Equiv.ofBijective (fun i => ⟨v i,List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩)⟩)
    ⟨fun _ _ h => inj (congrArg Subtype.val h),by
      intro y
      obtain ⟨i,h⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp y.property)
      exact ⟨i,Subtype.ext h⟩⟩

theorem group_leaf {row : Record} {n : Nat} (g : G) (w : Fin n → CoRecipe4482.Entry)
    (inj : Function.Injective (fun i => (w i).full))
    (image : (stateWords row).toFinset.image (reorder (rowEquiv g)) =
      (List.ofFn (fun i => (w i).full)).toFinset)
    (size : n=6+row.budget)
    (anchors : List (Fin n)) (seven : 6<anchors.toFinset.card)
    (big : Fin n→Box) (bounds : ∀ i, fits (big i) (w i).projected=true)
    (inc : Fin n→BitVec (2^n))
    (digits : ∀i (j : Fin (2^n)), (inc i).getLsbD j.val=j.val.testBit i.val)
    (ids : List (Fin n)) (nd : ids.Nodup) (allIds : ∀ i, i∈ids)
    (fuel : Nat) (certified : checkGroup
      (List.ofFn (fun i => (⟨big i,inc i⟩ : BCol (2^n))))
      fuel (CoGlobalShape4482.required ids anchors inc)=true) :
    ¬ Path join (cleanCut model label 6) row.budget (stateWords row).toFinset := by
  let v := fun i => (w i).full
  let S := (List.ofFn v).toFinset
  let e := slots v inj
  have card : S.card=n := by
    calc S.card = Fintype.card (↥S) := (Fintype.card_coe S).symm
         _ = Fintype.card (Fin n) := (Fintype.card_congr e).symm
         _ = n := Fintype.card_fin n
  have ordered : ∀ z∈S,CoPortEdgeRows4482.Ordered z := by
    intro z mz
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp mz)
    exact eq ▸ (w i).ordered
  have stop := CoActualGroup4482.group_excludes (S:=S) (k:=row.budget)
    (card.trans size) ordered e (fun i => (w i).projected) (fun i => (w i).correct)
    big bounds anchors.toFinset seven inc digits (CoGlobalShape4482.required ids anchors inc)
    (fun j small many => CoGlobalShape4482.required_at ids anchors inc nd allIds digits j
      (by rwa [card] at small) many) fuel certified
  intro actual
  have moved := reorder_path (rowEquiv g) (respects_label g) actual
  rw [image] at moved
  exact stop moved

end CoJunctionLeaf4482

namespace CoJunctionLeafCheck4482
open CoPortRoots4482 CoPortFrontier4482 CoPortTrace4482 CoPortCut4482
open CoBitBlock4482 CoBlockIntervals4482 CoBlockSlots4482
open CoJunctionWire4482 CoJunctionTree4482

def axis {n : Nat} (i : Fin n) : BitVec (2^n) :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin (2^n) => j.val.testBit i.val))).cast List.length_ofFn

theorem digit {n : Nat} (i : Fin n) (j : Fin (2^n)) :
    (axis i).getLsbD j.val=j.val.testBit i.val := by
  simp only [axis,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn]
  simp [j.isLt]

def ids (n : Nat) := (List.ofFn (fun i : Fin n => i)).dedup
def anchors (n mask : Nat) := (ids n).filter (fun i => mask.testBit i.val)
def valAt (xs : List Wire) (i : Fin xs.length) := value (xs.get i)
def markAt (xs : List Wire) (i : Fin xs.length) := (eval (xs.get i)).projected

theorem real_set (xs : List Wire) : (List.ofFn (valAt xs)).toFinset = (values xs).toFinset := by
  ext z
  simp only [List.mem_toFinset,List.mem_ofFn,values,List.mem_map]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨xs.get i,List.get_mem _ _,hi⟩
  · rintro ⟨w,hw,hv⟩
    obtain ⟨i,eq⟩ := List.mem_iff_get.mp hw
    exact ⟨i,(congrArg value eq).trans hv⟩

def checkWith (xs : List Wire) (k mask fuel : Nat) (inc : Fin xs.length→BitVec (2^xs.length))
    (must : BitVec (2^xs.length)) : Bool :=
  let n := xs.length
  decide (n=6+k ∧
    (∀ i j : Fin n,valAt xs i=valAt xs j → i=j) ∧
    6<(anchors n mask).toFinset.card) &&
    CoImplicitBlock4482.check (List.ofFn (fun i => (⟨markAt xs i,inc i⟩ : Col (2^n)))) fuel must

def check (xs : List Wire) (k mask fuel : Nat) :=
  checkWith xs k mask fuel axis (CoGlobalShape4482.required (ids xs.length) (anchors xs.length mask) axis)

theorem checkWith_sound {xs : List Wire} {k mask fuel : Nat}
    {inc : Fin xs.length→BitVec (2^xs.length)} {must : BitVec (2^xs.length)}
    (digits : ∀ i (j : Fin (2^xs.length)),(inc i).getLsbD j.val=j.val.testBit i.val)
    (needed : ∀ j : Fin (2^xs.length), (members j).card+5≤xs.length →
      2≤((members j)∩(anchors xs.length mask).toFinset).card → must.getLsbD j.val=true)
    (ok : checkWith xs k mask fuel inc must=true) :
    (values xs).toFinset.card=6+k ∧ ¬Path join (cleanCut model label 6) k (values xs).toFinset := by
  obtain ⟨data,cert⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨size,inj,core⟩ := of_decide_eq_true data
  let S := (List.ofFn (valAt xs)).toFinset
  let e := CoJunctionLeaf4482.slots (valAt xs) inj
  have card : S.card=xs.length := by
    calc S.card = Fintype.card (↥S) := (Fintype.card_coe S).symm
         _ = Fintype.card (Fin xs.length) := (Fintype.card_congr e).symm
         _ = xs.length := Fintype.card_fin _
  have order : ∀ w∈S,CoPortEdgeRows4482.Ordered w := by
    intro w hw
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hw)
    exact eq ▸ (eval (xs.get i)).ordered
  have stop := CoActualTight4482.implicit_excludes (S:=S) (k:=k) (card.trans size) order e
    (markAt xs) (fun i => (eval (xs.get i)).correct) (anchors xs.length mask).toFinset core
    inc digits must (fun j small many => needed j (by rwa [card] at small) many) fuel cert
  rw [←real_set]
  exact ⟨card.trans size,stop⟩

theorem check_sound {xs : List Wire} {k mask fuel : Nat} (good : check xs k mask fuel=true) :
    (values xs).toFinset.card=6+k ∧ ¬Path join (cleanCut model label 6) k (values xs).toFinset := by
  apply checkWith_sound (fun i j => digit i j) _ good
  intro j small many
  apply CoGlobalShape4482.required_at _ _ _ _ _ (fun i q => digit i q) j small many
  · exact List.nodup_dedup _
  · intro i
    apply List.mem_dedup.mpr
    exact List.mem_ofFn.mpr ⟨i,rfl⟩

end CoJunctionLeafCheck4482

namespace CoJunctionGrids4482
open CoJunctionLeafCheck4482 CoPortRoots4482 CoBitBlock4482 CoBlockSlots4482 CoJunctionWire4482 CoJunctionTree4482
structure Grid (n : Nat) where
  inc : Fin n → BitVec (2^n)
  digits : ∀ i (j : Fin (2^n)),(inc i).getLsbD j.val=j.val.testBit i.val
  width : BitVec (2^n)
  enough : ∀ j : Fin (2^n), (members j).card+5≤n → width.getLsbD j.val=true
def axes7 : Fin 7→BitVec (2^7) := ![0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
def width7 : BitVec (2^7) := 0x100010117000101170117177f
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem digit7 (i : Fin 7) : ∀ j : Fin (2^7),
    (axes7 i).getLsbD j.val=j.val.testBit i.val := by fin_cases i <;> decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem wide7 : ∀ j : Fin (2^7), (members j).card+5≤7 → width7.getLsbD j.val=true := by decide +kernel
def axes8 : Fin 8→BitVec (2^8) := ![0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def width8 : BitVec (2^8) := 0x100010117000101170117177f000101170117177f0117177f177f7fff
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem digit8 (i : Fin 8) : ∀ j : Fin (2^8),
    (axes8 i).getLsbD j.val=j.val.testBit i.val := by fin_cases i <;> decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem wide8 : ∀ j : Fin (2^8), (members j).card+5≤8 → width8.getLsbD j.val=true := by decide +kernel
def axes9 : Fin 9→BitVec (2^9) := ![0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def width9 : BitVec (2^9) := 0x100010117000101170117177f000101170117177f0117177f177f7fff000101170117177f0117177f177f7fff0117177f177f7fff177f7fff7fffffff
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem digit9 (i : Fin 9) : ∀ j : Fin (2^9),
    (axes9 i).getLsbD j.val=j.val.testBit i.val := by fin_cases i <;> decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem wide9 : ∀ j : Fin (2^9), (members j).card+5≤9 → width9.getLsbD j.val=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def axes10 : Fin 10→BitVec (2^10) := ![0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def width10 : BitVec (2^10) := 0x100010117000101170117177f000101170117177f0117177f177f7fff000101170117177f0117177f177f7fff0117177f177f7fff177f7fff7fffffff000101170117177f0117177f177f7fff0117177f177f7fff177f7fff7fffffff0117177f177f7fff177f7fff7fffffff177f7fff7fffffff7fffffffffffffff
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem digit10 (i : Fin 10) : ∀ j : Fin (2^10),
    (axes10 i).getLsbD j.val=j.val.testBit i.val := by fin_cases i <;> decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem wide10 : ∀ j : Fin (2^10), (members j).card+5≤10 → width10.getLsbD j.val=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def axes11 : Fin 11→BitVec (2^11) := ![0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def width11 : BitVec (2^11) := 0x100010117000101170117177f000101170117177f0117177f177f7fff000101170117177f0117177f177f7fff0117177f177f7fff177f7fff7fffffff000101170117177f0117177f177f7fff0117177f177f7fff177f7fff7fffffff0117177f177f7fff177f7fff7fffffff177f7fff7fffffff7fffffffffffffff000101170117177f0117177f177f7fff0117177f177f7fff177f7fff7fffffff0117177f177f7fff177f7fff7fffffff177f7fff7fffffff7fffffffffffffff0117177f177f7fff177f7fff7fffffff177f7fff7fffffff7fffffffffffffff177f7fff7fffffff7fffffffffffffff7fffffffffffffffffffffffffffffff
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem digit11 (i : Fin 11) : ∀ j : Fin (2^11),
    (axes11 i).getLsbD j.val=j.val.testBit i.val := by fin_cases i <;> decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem wide11 : ∀ j : Fin (2^11), (members j).card+5≤11 → width11.getLsbD j.val=true := by decide +kernel
def grid : (n : Nat) → Grid n
  | 7 => ⟨axes7,digit7,width7,wide7⟩
  | 8 => ⟨axes8,digit8,width8,wide8⟩
  | 9 => ⟨axes9,digit9,width9,wide9⟩
  | 10 => ⟨axes10,digit10,width10,wide10⟩
  | 11 => ⟨axes11,digit11,width11,wide11⟩
  | n => ⟨axis,digit,BitVec.allOnes _,by intro j _; simp only [BitVec.getLsbD_allOnes,j.isLt,decide_true]⟩
def checked (xs : List Wire) (k core fuel : Nat) : Bool :=
  let G := grid xs.length
  checkWith xs k core fuel G.inc (CoAnchorMask4482.mask G.width G.inc (anchors xs.length core))
theorem sound {xs : List Wire} {k core fuel : Nat} (h : checked xs k core fuel=true) :
    (values xs).toFinset.card=6+k ∧ ¬ CoPortTrace4482.Path join (CoPortCut4482.cleanCut model label 6) k (values xs).toFinset := by
  let G := grid xs.length
  apply checkWith_sound G.digits _ h
  intro j small many
  exact CoAnchorMask4482.needed G.width G.inc (anchors xs.length core) G.digits j (G.enough j small) many
end CoJunctionGrids4482

namespace CoPortRoots4482
open CoPortBank4482 CoPortCut4482 CoPortTrace4482 PEqualNP.CircuitLowerBounds

def head : Gate := ⟨.or,[0,2]⟩
def circuit (gs : List Gate) : Circuit := ⟨head::gs,0⟩

private theorem init_values (r : R) :
    init.map (fun w => cell w r) = List.ofFn (row r)++[row r 0 || row r 2] := by
  simp [init,raws,seed,cell,row,List.map_ofFn,BitVec.getLsbD_or]

private theorem actual (gs : List Gate) (r : R)
    (valid : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    (history model init gs).map (fun w => cell w r) =
      (circuit gs).wires (List.ofFn (row r)) := by
  change (history model init gs).map (fun w => model.val w r) = _
  rw [correct model gs init r valid]
  change gs.foldl _ (init.map (fun w => cell w r)) = _
  rw [init_values]
  simp [circuit,head,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD]

theorem roots_of_collision_free (gs : List Gate)
    (valid : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (O : Finset Nat) (cap : O.card≤6)
    (nodupLabel : ¬∃ x y, graph x≠graph y ∧ ∀ i∈O,
      ((circuit gs).wires (List.ofFn x)).getD i false = ((circuit gs).wires (List.ofFn y)).getD i false) :
    ∃ k≤gs.length, Path join (cleanCut model label 6) k raws.toFinset ∨
      Path join (cleanCut model label 6) k init.toFinset := by
  classical
  have start : Covers roots init := fun _ h =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (List.mem_toFinset.mpr h))
  have z0 : model.zero∈roots := Finset.mem_insert_self _ _
  have z1 : model.one∈roots := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  obtain ⟨T,b,cov⟩ := bank model gs z0 z1 start (Bank.initial (join:=join) (root:=roots))
  let read := fun i => (history model init gs).getD i 0
  have represents (i) (r) :
      model.val (read i) r = ((circuit gs).wires (List.ofFn (row r))).getD i false := by
    rw [←actual gs r valid]
    exact (read_values model (history model init gs) r i).symm
  have sep (r s : R) (different : label r ≠ label s) :
      ∃ i∈O,model.val (read i) r ≠ model.val (read i) s := by
    by_contra! same
    apply nodupLabel
    exact ⟨row r,row s,different,fun i hi => by rw [←represents,←represents]; exact same i hi⟩
  have idem : ∀ d a,join d a a=a := by intro d a; cases d <;> simp [join]
  obtain ⟨j,hj,A,sub,path⟩ := observation label 6 b idem read O cap
    (fun i _ => read_mem model cov (b.keeps z0) i) sep
  refine ⟨j,by simpa using hj,?_⟩
  rcases only_roots sub path with rfl|rfl
  · exact Or.inl path
  · exact Or.inr path

end CoPortRoots4482

namespace CoPortRoots4482
open CoPortTrace4482 CoPortCut4482 PEqualNP.CircuitLowerBounds

theorem conditional
    (excluded : ∀ k ≤ 7, ¬ Path join (cleanCut model label 6) k raws.toFinset ∧
      ¬ Path join (cleanCut model label 6) k init.toFinset) : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : List PEqualNP.CircuitLowerBounds.Gate),   x2.length = (7 : ℕ) →     (∀ (x4 : ℕ) (x5 : x4 < x2.length), (x2[x4].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2[x4].op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x2[x4].inputs.length ≤ (2 : ℕ) ∧ ∀ x6 ∈ x2[x4].inputs, x6 < (10 : ℕ) + x4 ∨ x6 = (17 : ℕ)) →       have x5 : PEqualNP.CircuitLowerBounds.Circuit := { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (2 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };       ∀ x6 ⊆ (Finset.range (17 : ℕ)).erase (9 : ℕ), x6.card ≤ (6 : ℕ) → (∃ x9 ∈ x6, (10 : ℕ) ≤ x9) → ∃ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ) → Bool), x1 x10 ≠ x1 x11 ∧ ∀ x12 ∈ x6, (x5.wires (List.ofFn x10)).getD x12 Bool.false = (x5.wires (List.ofFn x11)).getD x12 Bool.false := by
  dsimp only
  intro gs len valid O _ cap _
  by_contra absent
  have legal : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
    intro g hg
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hg
    exact ⟨(valid i hi).1,(valid i hi).2.1⟩
  obtain ⟨k,hk,p⟩ := roots_of_collision_free gs legal O cap absent
  obtain ⟨a,b⟩ := excluded k (by omega)
  exact p.elim a b

end CoPortRoots4482

namespace CoJunctionTarget4482
open CoJunctionLogical4482 CoPortRoots4482 CoPortFrontier4482 CoPortTrace4482 CoPortCut4482

structure Certificate (I : Type) (rootWords : Finset W) where
  table : I → Record
  root : I
  ceiling : 7 ≤ (table root).budget
  starting : (stateWords (table root)).toFinset=rootWords
  authenticAt : ∀ s, authentic (table s).bank
  above : ∀ s,6 < (stateWords (table s)).toFinset.card
  classified : ∀ s, ((stateWords (table s)).toFinset.card=6+(table s).budget ∧
      ¬Path join (cleanCut model label 6) (table s).budget (stateWords (table s)).toFinset)
    ∨ Routed table (table s)

theorem exclude {I : Type} {S : Finset W} (c : Certificate I S)
    {k : Nat} (hk : k ≤ 7) : ¬Path join (cleanCut model label 6) k S := by
  intro path
  apply closes c.table c.authenticAt c.above c.classified 7 c.root c.ceiling
  exact ⟨k,hk,c.starting.symm ▸ path⟩

theorem both {I J : Type} (ordinary : Certificate I raws.toFinset)
    (preset : Certificate J init.toFinset) :
    ∀ k ≤ 7, ¬ Path join (cleanCut model label 6) k raws.toFinset ∧
      ¬ Path join (cleanCut model label 6) k init.toFinset := by
  intro k hk
  exact ⟨exclude ordinary hk,exclude preset hk⟩

end CoJunctionTarget4482

namespace CoJunctionComplete4482
open CoPortRoots4482 CoPortFrontier4482 CoJunctionLogical4482 CoJunctionFixed4482
open CoJunctionActual4482 CoJunctionTarget4482

def rowCheck (h : Graph) [NeZero h.size] (hints : Column) (seeded : Bool) (depth : Nat)
    (i : Fin h.size) : Bool :=
  let r := recordAt h seeded depth i
  let xs := CoJunctionFixedModel4482.build h seeded depth i.val
  let leaf := leafCode h i.val
  let cue := field hints (leaf-1)
  decide (6<(stateWords r).toFinset.card) &&
    if leaf=0 then internal h seeded depth i
    else CoJunctionGrids4482.checked xs r.budget (cue/64) (cue % 64)

def certified {h : Graph} [NeZero h.size] {hints : Column} {seeded : Bool} {depth : Nat}
    (cap : 7≤budget h 0)
    (all : ∀ i : Fin h.size,rowCheck h hints seeded depth i=true) :
    Certificate (Fin h.size) (if seeded then init.toFinset else raws.toFinset) where
  table := recordAt h seeded depth
  root := 0
  ceiling := cap
  starting := CoJunctionFixedModel4482.root_values h seeded depth
  authenticAt := fun i => CoJunctionFixedModel4482.table_real h seeded depth i.val
  above := fun i => of_decide_eq_true (Bool.and_eq_true_iff.mp (all i)).1
  classified := by
    intro i
    have localCheck := (Bool.and_eq_true_iff.mp (all i)).2
    by_cases stop : leafCode h i.val=0
    · exact Or.inr (internal_sound (by simpa only [if_pos stop] using localCheck))
    · have leaf := CoJunctionGrids4482.sound (by
        simpa only [if_neg stop] using localCheck)
      apply Or.inl
      change (words (CoJunctionFixedModel4482.data _)).toFinset.card = _ ∧
        ¬CoPortTrace4482.Path join (CoPortCut4482.cleanCut model label 6) _
          (words (CoJunctionFixedModel4482.data _)).toFinset
      simpa only [CoJunctionFixedModel4482.data_values] using leaf

def slice {n : Nat} (test : Fin n→Bool) (start count : Nat) :=
  (List.range count).all (fun d => if h : start+d<n then test ⟨start+d,h⟩ else true)

def Holds {n : Nat} (test : Fin n→Bool) (lo hi : Nat) :=
  ∀ i : Fin n, lo≤i.val → i.val<hi → test i=true

theorem slice_sound {n a k : Nat} {f : Fin n→Bool} (ok : slice f a k=true) :
    Holds f a (a+k) := by
  intro i lo hi
  have lt : i.val-a<k := by omega
  have eq : a+(i.val-a)=i.val := by omega
  have h := List.all_eq_true.mp ok (i.val-a) (List.mem_range.mpr lt)
  simpa only [eq,i.isLt,dif_pos] using h

theorem join_blocks {n a b c : Nat} {f : Fin n→Bool}
    (left : Holds f a b) (right : Holds f b c) : Holds f a c := by
  intro i lo hi
  by_cases before : i.val<b
  · exact left i lo before
  · exact right i (by omega) hi

theorem all_rows {n : Nat} {f : Fin n→Bool} (j : Holds f 0 n) (i : Fin n) : f i=true :=
  j i (Nat.zero_le _) i.isLt

end CoJunctionComplete4482

namespace CoJunctionArchive0
open CoJunctionFixed4482
def rows : Column := ⟨15,#[0x24ba49549269245247a48d49169225243a4854906920523fa47d48f691e523ba47548e691c5237a46d48d691a5000a00148ce8005000a00149868005260a0014002800525fa001497a8005000a00149668005258a0014002800524fa001493a8006000c00180030006000c00180030006000c00180030007,0x310a00140029855000a60f40029825000a5ff400297e52fba5f5400297b5000a5e740028005318a0014c5e8005316a0014c56800530fa0014c3a8005303a0014c0a978d2f0a5df4bba80052eda5d94bae97552e9a5d14b9e80052e6a5cb497692e525ba4b5495e92b5255a4a9494e9295251a4a149369265,0x465a8c9518e8005462a8c34f7e9ef53dba7b54f669ec53d7a7ad4f4e9e953d1a7a14f3e9e753cda7994f269e453c7a78d4f169e253c3a7854f069e053bfa77d4ef69de53bba7754ee69dc5000a0014ede80053e3a0014f8a80053e1a0014f8280053dda0014f7280053d5a7a940029e5d3caa6294c4e8005,0x52aaa5354a28005000aa4f40028005000aa7b4002a9e5000aa734002a9c5000aa6b54d28005487a909520e8005480a8ff51faa3dd47aa8f351e28005000a8e94002a46d000a9194002a45d000a9154002a435000a90b51f6800547ca8e351c2a37d46ea00151ae8005473a00151caa34d000a8d1519ea335,0x810a0014002800582ea00160b68005000a00160a2c13d000a0014002c115821a0014002800581ab0334002ae255c1ab814002ae45000ab8f4002ae1d000a0014002ae15000ab7956ee80055b8a00156d6adfd000ab7d56d2ad9d000ab6556c6a9dd53aaa6f54daa99d532aa6354c2a97d52eaa5b54b2a95d,0x972a00165b6cb6588bb1154002c46d000b1196226c445885b109621e8005886b1074002800587db1054002c40d87cb0f761e2c3bd000b0f54002c3cd000b0eb61d2c39d872b05960aec155829b04d6096c125000b0476082c0fd81eb03b4002c0e581bb031605ec0b5815b029604ec095811a00140028005,0xa15a00168b28005a2bb44d4002d12d000b4496842d095000b4294002d09d989b311661ecc25983b30165fecbf597db2f965eecbd5977b2ed65d6cba5971b2e165becb7596bb2d565a6cb45967b2cd40028005000b2cb4002cc6d98ca001662e800598aa001661acc2d000b30566068005979b2f14002cb9d,0x1b0835f00020d3c1ae835b00020d341ac835700020d2c1aa83530002d4cd000b5316a5ed4b5000b52b6a528005a93b4ef69da8005000b4eb4002d3cd000b4f14002d3a5a73a00169cad38d000b441687ed0e5000b4374002d155000b453688e8005a22b4314002d0bd000b43368a2d13d000b43d6876d0b5,0x48808f014a028c04c809700020abc15a800105a60b8416f800105b60bc4177800105aa0b94171800105b20bb4175800105ba0bd4179800105ae0ba4173839d07360e341c5839507260e241c38399072e0e441c782bd06f20ddc1b4836706e20dbc1b2836306ea0dcc1b6836b01520dec062838100020d44,0x86810b022a044c0828103018602e405b80bd017603c407780e501c603a407380b1015e037406d80d1019e035406980ad015603240638119022e04240838111021e030405f80ed01d6036406b810101fe03d407980f901ee02d405980e101be033406580fd01f6029c04e809b0142027c000808d012a024c,0x82ff061a0c2c184830700020c0418a831300020c1418e831b06220c3c1f383eb07d20fbc1f683f307e20f941f183e1078a0f0c1e483c7079a0f2c1e883cf07820efc09c83d302aa0f641ef83dd00020ea41de83bb00020e9c1dc83b700020e941da83b300020e8c1d8800107420ebc1d68001073e0eac,0xce819b032a064c0ba817302c2057c0d481a70342067c0be817b02d2059c0cc81970322063c0c4818702e205bc0ae815b030a060c0c6818b026e04c409781250246048408f812d025604d40998129024e054c0a6814b028204fc09e813b0292051c0a8814f028a050c08e800105620aec000830306320c5c,0x191833506660cf419d8331065e110c220843f087a10ec21c841f083a106c20c8417082a104c2088437086a10cc218842f085a07b421381d108420afc00083ff081e00041fe840d081600041fd8409080e00041fc840500020fdc201800107ea10040d281a3030205fc0bc817702da05ac0b2816302b2055c,0xe182250446090411f8239046e07340e58231045e08241038219042e084410781bd037608341058215042607d40f98205040607f40fd81b9036e07e40fb820103fe07c40f781dd03b607ac0f281e3000206d40f081df03d2079c0ec81d703aa074c00082b3056e0cb41958001064a0ce419b8329064e0004,0x134826704ca098c12e825b04be096412b825504a60944127824d04960924123824500020ae41a48347068a0d0c1a0833f08ca117c231846108a61144130845508ba116c22c80010892113c0008447089a0004222844b0452089c110821f047a08ec0e081bf039e07240e3821d043608d4119822d04560714,0x298051008e01140218041007e00f401d8039006e00d4019803100fe01f403b807500ce0194027804d00f601e4039807100c60184025804905320a5c15482a7053a0a6c14a8293054a0a8c15682ab05420a7c148828f051a0a2c142828305120a1c140827f04fa09ec13a827304f209dc138826f04da09ac,0x2af855d0ab6153c2a6854b0a92151c2a285430a821484292853f0a7a14bc29685370a6a14ac294853b0a7214cc298851f0a1e000428d850d0a2e146400085130a12141c28885150a3a142c273800109c2135c26984e909aa139400084e309ba136426f84db00de01b4035806900be017402d805900ae0154,0x30886130c16183430086030bf617f42f885ef0be617a42f585e50b92171c2e285c30b8216fc2dd85b90b6e16d42d985b10b5e16b42d585890b36165c2d485a70b4a168c2d0859f0b3a16642c885870b1616142c185810afe15f42bd85790aee00042b885750ae615442ab85610aca158c2b485670ada15ac,0x39387230e421c7c38d86b50e0a000438087150e26000437f87110e1e000437e870d0e16000437d870900021be438380010dee1c0c37086df0dca1b8c37486e70dda1bac36e86db0dae1acc36786d10d9a1b4c36a86d90d961b2436386c50d861b0435f86bd0d761ae400086b10d6e188c312861b0c2e1864,0x31f863d0c761944327868f0d1a1a1c342867b0cf2199c332864d0c961aac354869b0d321a8c35086970d2a1a9c352869f0d3a1abc35687690eda1d843b287670ed61d7c3ad87630eb21d5c3a887410eaa1d4c3a1874f0e9a1d143a587490e7e1cf439d87390e6e1cd439987310e5e1cb439587190e2e1ca4,0x41780011036209441187f7100e000440287f510021fe440187ff00021ff43f987f10ff61f7c3f387e90fd600043f287dd0fb21f843ed80010fc61f5c3e987d50d061a0433b86750ce619c4337866d0cc6198432f865d0cb6196432b86550ca61a4c348868b0d1219fc33e866b0cd2192432386450c861904,0x4498891111e222c4448887110a220c440887f10fa21cc43d887910ea2154430887110de21b4435886910ce2194431885d10a6216c42b8839107a21144218001106a21244238001106e21344258851109e210441f883b11b621dc46c88d5102e206440a8001103a20a44138001103e20b44158001104220c4,0x5128a2f145a28ac5148a271446288450f8a19143600044ea80011422285c50a8001141e284c5068a0b1412281c5028a03140227fc4fe89fb13f227dc4f989f113de27b44f589d313ea24444898903120a23bc47588ed118222fc45a88bb117a22dc45c88b11166229c45788ad000222ac45288a9112e2254,0x4da89b31342267c4cc8997133a266c4c8898f1352269c4d889af135a26ac4ca8993134a268c4c6898b12e225bc4c3898112fe25b44b5897912ee25d44c2898312fa25ec00089d1000227644f489e713ca278c4ee89db13c2277c5268a4b149228cc5188a47148a290c5208a3f131228e451e8a37146a0004,0x5808b0f161a2c2c5848b17162a2c4c5888b1b16322c1c5828af115d600045778ae915ce00045768ae515c625844af895512a625a44b3895d0002256c4a48947128a250c4a0893f127a24ec49c893712a2253c49a896512c625644ab894d1296273c4e489c7138226fc4e289c3139a272c4de89bb137226dc,0x5ac8b5716a62d445a78b4d16962d1c5a28b4316822b2c5648001159e2b345608abf157a2ae455b8ab500022b1c5628ab3155a2aac0008ab1154e2a945518aa1153e2bfc57e8af715f62be457a8af316662cc40008b35167e2cf4596800116762cac59b8aaf16522dec5618b7515762dcc5b78b2f16da2c0c,0x7488e3500023a0c74b8e9500023a2c7528ea300023a347548ea700023a1474e8e9b00023a3c7568eab00023a247508e9f1e1a3dac7898f7f1efa3dec7bc8f771eea3dcc7b88f6f1eda3da47b38f631ec23d7c7ae8f5b1eb23d5c7aa8f531ea23d3c7a68f4b1e8e3d945c58b8d00022d545ae8b6116be2d6c,0x6478c8d191632240008c5718aa313c6248c47188a310c61a8c33000230f46518ca11936326464b8c9518b631646438c85188230fc65d8cb9196632c46558ca918ce31940008c93192231346258c9f193a320c6408c7b18f231dc63a8c5318a231bc0008c6d187230dc6398c7118fe31f47498e991d0e0004,0x6658cc91d923b5c76380011da238dc0008ecb1dc63b840008ecd1dce3b9476a8ed300023b1476d8ed900023b3c7758ee91dbe3b747d78fad1f563ea47d38fa51f463e847cf8f951f263e447c78f8d1f163e247c38f851f063e047ce8f9b1f323e5c65b8cb5195e32b46538ca518d631a46318c6118be3174,0x6a08d3f1a6234bc67a8cf319d2339c6768ceb1a2a344c68c8d1719c2337c6868d0b1a0233fc6828d0319ba336c67c8cf71a8a350c69a8d331a7a34ec6788cef1a3a346c6848d071a5a34ac6908d1f1a4a348c6728ce31a22343c67e8cfb1a52349c66c8ccf199a334c6688cbf197a331c6618cc119ae3354,0x6c88d871b0a00046c18d811b1e36346c58d891ac600046ae8d611abe35646ab8d7f1afa35dc6ba8d6b1ad2359c6b28d731ae235ec6bc8d6f1ada35546a98ef71dea000477d8e3900023be47838f051e063c0477f8efd1faa3f4c7268fcf1e223f447e38fc500023ef47df8fcd1f863f047e58fc91a7234dc,0x7918f2100023c647988f2f1e3e3c747948f271e6a3ccc7968f2b201a407480d9007201640247f98ff11c36403c80290031e2a407c7fb8ff52032405c80a8dc31ff240047ff8ffd00023f847f780011fbe3fb47f580011fba3fa40008fdb1fce00047ec8fe500023f5c7f18d9f1b3a366c6cc8d971b2a364c,0x6f38de51c32384c7088dcf1b9a378c6f08e0b1c12380c7008dcb1b9237ec6fc8df31be238cc7188e2b1c52376c6ec80011c2e38547038e051bd637a47138e251c3e38746e98dd11c1e38346ff8dfd1c4638846d58da91b8236ec6dc8da71b4a36cc6d78dad1b7e36f46db8db51e163c9478480011e36391c,0x5fd8bf9180630045f78bed17ee2fd45f18be117be2f745ed8beb17d22f645e78bcd17962f245e38bc517862f5c5ea8bc1177e2ffc5fe8bf317e22f9c5f28bd317a23d247a28f431e823cfc79e8f3b1e723cdc7208e3f1c9639247228e431c7a38ec6fb8df51bde37b47178e2d1b8e37146ef8ddd1bae3754,0x87090df21ba436c86c90d721aa431c86290d1219e430c86990cd217a430485790b3000242c485d90b9216a42dc88090ff21fa425484b90ab2152428c850909d2136429c852909f213243b483c907b21064204847908d20fe41f48459089212642448439085000241c4836907720e6000483a906f1f763c3c,0x929926124be497492d91e724b248f4926924b2482491492191e52492491c928924f247648d4919923f245e48e49189237245a48ac910921f243a486c9149227244a488c90c9213241a48449079215242e47ec8fc9207240a47fc8fe91f723ea482c9049203240200048f191b323d647bc8f891ed23e6438c,0x8e091bf237a46ec8dc91b7236a46c48d792bb25824b2495e92b9238a4b1495f92c7256e4ad496192a3254e4acc95892a1255a4a94949929f253a4a6c94c929525564aa4948800125124a3c946928b24f649fc943928525064a0493c927723d249bc93e927124ea49cc936926b24d2499c932926324ae4954,0x8b3916522c645bc8b6916122be45748ad9151229e45348ac9157229645248a39145228644e489b9135228244fc8999131225e44b48959129224e46848cf9199232e46348c5917f22fa45ac8b4915522a644f489d91e123be47748ed91d923ae47548e991d1239e47348e591c9238e46b48d591a9234e470c,0x9f793ed27ce4e049f4939f27e64fc49dd800127be4f74a1193b726b64d949a1934726824d149aa800126964d7c9ae800126a24db49b58001269a4d8c9b0800126924d649ab800126a64dc49b78001269e4da49b39195232646948d1919d233646248c391852322463c8bd917922ee45d48c1918122e645c4,0xa04940b2806501c9ff93fd274650049fa93f927f64efc9ec93d527a64f449e593cd27364f1c9e493c527864dcc9ba938b26fe4df49bd9379270e4e149c1937700024e449c7800127724ecc9de8001276a4ebca2193c127625074a089415271250649eb941f280a505c9d3941328364f849f193e527d64f3c,0xa3a947328ce5194a38946f28c65184a2f945d28b6523ca46949d2936525ca4a94932922537ca6d94d929ba535ca6894cf29aa534ca6594c5298e530ca6494cd298252fca5e94bb297252dca5a9499296652c4a5794ad295652a4a5394a529465284a4f943527264e549cb93a527324e749d093a9281e5034,0x406084c005803b0056014c0098043004600cc00d804b00062c0c585800316762ccc0018b1b16262cac5a1800316475252a46547ca9095112a3a546ca8c95172a265454a7b94f52a1e5434a8595092a0e5414a81950129fe53f4a7d94f929165224a43948528f651e4a41948128ee51fca3e946d28d651a4,0x408680ed011a02b3f767eccf959f333e767d0cf919bd337966f0cddd98e331b6634cc6595bb27c64f2c9f593b327a64eec9d593db27864c8c98d933326564cec98980bb0d861aec35586b30156026c05180930166320c0018c7b00d6016c041807b00c601cc045800317b62f8c5f5800317e6082c111821b,0x72c6e7edd01b9eb73e6e64dccdb98b54d6a9cd51980035456a96c001aa1b5496a90d511800354c6a8ed50580035426a7cd501a9fb5936b24d639ac8b5906b1ed529ab7356b6adad5b1ab4b5686ad4d241a473491691ed24da4b34956928c001a75b4996930d25da27b451689cd141a26b44c6832d019a04b,0x7606ebadd69bacb7586000dd6dbabb60e6c1ed835b0536096c16d81db0636086c06d811b0336026c0ad851b09b0006c22d85d80036106c2cd84980036156c30d725ae7b5cc6ba2d735ae535d06b9cd72db94b72b6e50c001b9537276e6ec001b9b37346e6adce1b9db73a6e72dcf1b98372e6e5ac001b97b,0x9957326e641cc7b992731ce651cc8b99d733ee679cce399b7330e665c493891711ce23dc483856706ae0c1c193833705ee0c5c1a36d16da0d771aeeb5de6f16da99b5436a56d4eda91b51b5d96bb6d769bbc37776ef2ddd9bedb7da6fb2df61bee35d36ba8d761aeb35d26baed755bae375f6ec2dd798003,0x492538ce755ceb39ed7334e65dccb3]⟩
def actions : Column := ⟨13,#[0x9c03f01f00c4460025012006c034013009012c49403b01d00b4458021110005c02c00f0070024010005c02a81407383981cace407083800af25642a81500a205001ba0d906a63401880c003e41e40ed07003201804e02600f887801a00c003801800600200080000,0x6a03402881040801b301902740381cf1270afc07c531118149404831b00d0e4c07ab3d01e20f003281900c2060022811008264031680b0053428a9224821c80e0256aab115007c42a014006803000eb87003010c08403501a01440a004102000cc06401d00e013c4,0x5602a00a805001ab8d006015c0ac053029010c08403501a0104a80033019009c04c01d00e013409802f0170064030011008012c09403b29d00b405801700b003c01c009c04b424092ac90242120056a2b01520a802a81500a205001a98d006060d00600202181080,0x5a02c00b805801f80f44780af25712b51580a905401540a805102800340180080ae056169814858604201a80d00825400d980c814e01d00e073d19e04e5670ac5462030418006d03601a40d004c0249920e5812845a02c10b805841e00900448204920395dc94e02,0x2e817015e4ae256a2b01520a801ba0d806a234018007c83c41d00e006001e20e206803001011c08c03501a00cd866032419007503a01cc0e407103804b09d86e895a02c24b805841e00ea4712ac05401554a805008e04601a80d009a14c01e86f005e02e00c80600,0xe006001a80c00424702310d506a03451a08cc064031018026c03509a04980f405e02e28c8062a305110080eec2744ad00b805a42c20fa47803845602a023811806a03401980c803a01c80e00fc07c031018006e03601a01e84f005e02e00c806005a02c00be05e0,0x4e03f1d8806c03519a0cc8062730391a4880ec07232b00a8052028059023811806e036029814808604201a80d005204102000cc064031018006c03403d01e006403003b01d00b705b02d416812589204821cace407083800fac7c03c11540a805001a88d006001da,0x9304956420af25702b5152057a2b51540a203741b50d4c6211d08e0465a30d0405e02e9d70eac05502a021810806b83551a810568204042000463220101c6c03401805902381189a60525690b0d3860425a10cd4068a3411480a165035162881040801b365980c80,0x18007003000c004001000001700b005524e126092cc851cf2e6072cb8415e6ae056caa50af25602a814406e03601a98c403e01e00ed06426a93187ad3c417a8b9046b2258ca0610228104c4c125790c395dc24ad75481f5cf2c5572880d5c6261d70cd015c029270,0xed470230d1408803729b150866a33419494a0b820400d980c864e02600e807067e03e05894c034a02404d8068b261920de80f075e52e2919488a32518288864071618a0dd80e845a52c250808042e31618780384121880c29410a7012b195047c03c01564a8c340,0x7082bc15c0ad054a1f58f2c57a2b01540a203761b00d4c6201da0c84e61fb4f9062cb0412a49163681a4045325790c395dc24ad75481f5cf2c5572880d5c6260d704d015c0292709304956420e707303969c20af35702b515207f33f01f58af25602a814403e41e0,0x505c102006cc064327013007403833f01f02c4a601a5012026c0340930c906f40783af297148ca4451928c144432038b0c506e845a52c250808042e31618780384121880c29410a7012b195047c03c01518a0c34018007003000c004001002e01600aa39c1cc0e5a,0x2bb1580aa05101a98c403b4190a4ac34a12cd5068a285a8b341582cc0599b2c944eca658d464e9251989c8d24271f48e906d232003149c24c12587383981cace105792b815a8a903fc9f80fac3741b00d4c3e41e00ed470230d1408803729b150c08433519a0ca4a,0x3a11c19f82f81620300d28a9013609a049824817a2bc15780b8a464a228c8c606221901c5862837623a11680b094222010b885841e00e104862030a48425c84e025411f10f005552a10d006001c00c0030010004000005c02c015492c4851ce0e6072b3840fac796,0x303110c80e2c3141b909c04a823e21e00a845021a00c0038018006002000801700aa1540a203531880768320d1450b33659289da4cb0fa47485201b50c80af25642a80dd06c83530f907903b51c08c4451620adc06c44322110d06524282e0830056603209380980,0x4801300900f447802f017008c44401900c004402000b00506b405800f007002401000500200ac05400d006001c00c003001012d49483b41d20b5458821510245d02c80f4072025010833019049c04c03f05f02c40601a5152024c1240bd15e0abc05c52325114646,0x3c91540a200d09ea4e558a8c103681a409a049312805424b121872b38415a8a903eb1e58aa05101a98c42c41610819c08e0269da3ad4ec67433914ab13a87d4e6019047aa16d0a684b294e8c06e097048ca4452123ec954c3a6cc06402701300fc07c0b101800940,0x99832c5e6073345826c5760fba99856c126cbb035ba2c0c60d1550b1480ca045016d39829310d684b3541a28a1635198aa9a07233704d51eacf105ea2e411ac45016817802a4560a2950620b501066cb24132c7503981c80e2042a1e809424a4e567082b515207d6,0x35193a884e5a41f50c801c46e093849824a52107383981cb4e105792b815a8a903f99f80fac3761b00d4c1e20e00684d46630f5a7882f517208d644b1940c2029a1f049555aa555189875c02935498aaf51720650308114c8265d11e887c43b40206983cc2f61033,0x1e00e004802030a00401c80e003e01e006803000e0060c0800009684a49db4e905a82c410b48122e816407a03900a8044183069024888915aa5101aa82680aa55006834519b26e13509284c4e4691d214806d32552a80d4c1a14d2a4ac34a12ed5068a285a0b49da,0x1a80c403e41e20ed066ac41610819c08e0269da3ad13a87d52329114848fa6320a8845828c0f6075a3a91d288522e9094a4652229091f643a71408804102000cc06402701300f8562530012809003601a049804807a03c0118088022010005802807603a01080800,0x9ca9b409a6260570534692b0d384b3541a28a164ed9a8cb48320a681c8e7a33957ed3e418a8c104ab134ccc02d113015807a015092c4849ce0e6072b38415e4ae056a2a40fa47922a814403a093037c96d0d605901e805415e4ae256a2a40af05602a814406e8360,0x7383981cace102a8074c1a0d5068a16907d23200fc07555e4ae256a2a401e20e10684d5262af5a7882f517208d444b1940c202d014d4b450a25d11c989446c0020adae0c21613b06181ccd2609a03d009415a85501aa8351b28921250a29c8d47b03d01e406d13d5,0x6412701300bc05c3a325114646303110c80eec47422d016128444021710b083c01c20524212e427012a08f887802a114086803000e003001000400000fc07a2af05702b51520550288074c3260d0048434a12cd1482c40599b0c9431391a484e3e91d214806d0320,0x42809424b121272b38415a8a902a814406a231006a0242c41610898448222096095a4a925288526e036013809804a024009804a02403b09d08b4358021010005c02c20f007002401000424f807801a00c000800003902d416205d02c809404201500883701b10cc0,0x82d2090f4105a8081d408c63e05703541a305a96e036013c49c04c03a21686b094049710b083d11e00e242127c03c00d5468018006002000800006a834419c45e02d48f446aad5068833c99c4cd864816907e23e01e89580a403556581cc206073059ca6c0e605b4,0x2f81780ba1270930494e424e73730394dc24af35702b655203701b00d4c6261f00f007403200f507003401214d03919b826a93187ab3c417a8b9446a22588a04131680a6a5a3298768ba656a2b1442da058b283d11c9894443456001046c28611368934459ba0d94,0x505b3019069c04c01d68e807067c0b1298069404809b00d024ea261bd01e0ebca5c5232911464a305110c80e2c3141bb01d12b4a584a1010125c62c30fa8780384121880c29410a720380958ca823e01e00a8c5061a00c806001c00c003001000400005340e466e0,0x4001000014d03901b80be05e02e839c1cc0e567092bc15c0ad05481f48f243761b00d4c6201f40f007403200d00484f4672afda7cd3151820916269924e6a53157a93c697a4b9a4692258c2e45220988902c4129050470230d1408803729b150c0845b519a0ca4a,0x8c34502200dca6c5430210cd466832929416cc064327013007403833f01f02c4a601a5012026c0340930c906f40783af297148ca4451928c144432038b0c506ec07422d296128404021718b0c3c01c2090c40614a085380958ca823e01e00a8c5061a007003000c0,0x7e03e0d894c034b025012026c0340930c906e844292100780384121880dc80e025632a08f807802a314186803000e006001800800200000e406e02f81780ba0af65712b515201d00c80340120cd86481b508545e01d4ab5552053029014403220d704d01540291c0,0x2e8494a424af05702b515207d23c90d446201d00c80340121495869c25942d459a0ac16602ccd964a276532cc6035193a4946627234909c7d23a42900da46412709304961ce0e6072b3840fe67e03e90dd06c03510f907803a00f10700352081003660320d380980,0x505c10600ac824e02600e847067e0be05880c034a2a404d826812609205e8af055e02e2919288a32318188d04432038b0c506ec47422d016128444021710b083c01c2090c406149084b909c04a823e21e00a845021a007003000c004001000014d23901b80be05e0,0x3903701b009c04c025012004c02403c15780b8a4602200880400141ba11684b004202010b805841e00e0040610a3e01e0038018006002000800003902d416203d01c8094042015008833419204e025091808403e01d04702311145882b701b110c88443501a0ca48,0xacc474232cd26610a58d754b246a851460ad0134e9138c8c65e01b017407a0af25712b515201d006852c2160bba76809424b121256a2a40fac7962a814406a60d08582d402a125890c3959c247d63cb1540a203501880768320d36693345a0c0f2a7193889c24560,0x64a276cd4262a2d20fa55c0320a0c416a02499b3a81c418c04632150f8074925572aaa40f2c5550c8835c0ab3d89cc3f69f3495648b1b40d204d324988924aee575480d5c1340579aa4c61eacf105ea2e511ac896228104c5a029a2fd9780ba4ad52880d543ae014,0x53028ad3c09a04b024851c08aa4302092730f9a6082458926652112395ca2035704d015e92ad14529285a8b301666ca764d464a331391a47485201b495406e83601a887681a93185ca235912c650308104c534ee07092b54faa1d700a534a92b0d284b294942d458,0x3833e05880c034a02400d806812601205e80f055c52301100640303110080e2837422d016128404021610780384120080c28010a7203821580a802a014086803000e0060018008002000125a12927683a490a08122e816407a039012808402a0110aa854622a1110,0x7091540a2035118887683340d404a4181c64e2270942c19ed4d03704b41da08122e805424e12609294849ce0e6072b38415e4ae056a2a40fe67e03e91e486e83601a98c403e41e00e806423811888a04421b80d808443501a0ca40500410200acc06402701300740,0x6932c91540d50a28c15d3a499627099807c03606a851460ad0124e91a849c24a1330118c7c05605a809424b0e567091f58f2c5502880d401a8e327113849964ca26493c9dc64e2270942c2062cf62e809424a521272b38415a8a903eb1e586a60d05a821424b0e56,0x5411f00f005422810d006001c00c003001000008684248cc06272f01690ac05204ca2c907d2aa01b0534a92ad5468a1a8e5a2b141ca0944a40061a6952621a509652928599c06e03509980c545e02d249555203100ea8157260b501e84961cac7d22a807401a1197,0x6302f815c0e6072aab815ae7e03ea8d803c00e006a81cc0c60592b99580aa62f41750b50ab20620388155c40d501f00d816a05502880d446201da06a2d40ba12589093959c247d23c90d446201d00c80350120dc06c03301900bc05c3a30110e606220101dc04ac0,0x5cb99482a25590e98da40a24a05701f806b40512348fa92c075a81032958c0ae01e941409424607302b80fc05600f00381cc0ae03f00d803c00e006bb46d4a06e0330396d5c055b1b00d5c0b21710a8ab80fc07d72ab8d803c01d303b81880b21570b8055dbc0ca5,0x1b00d660a04a12300d820a03a41b027808c6ce04fd27813b47703b01d689c64541f90f807a49da4bb25812ac8523ecb2488ca9da3ad13a87d43204ed25590a67d92501180fc496212887609407e03ec0d601b41f80eab2813407e02509180fc41e00710188aaa555,0x1b98da86a711053025810e68604299b5974e2e684da9418c06e05d51981ac0c605d517582a4ae03f015c0ac05521bd0d806a61e007b03881a0e6072cab815b27e00f007641c0060828128c8c63791b00d4ceb44fa27513587d43203ad138c7c032082812808c0379,0x2aa8354eb495a36d13a85a83ea19044414d4960429094cfa65538c8426d4a06e033011a20a0e605701f80ac01e007035817c07e02aa83548cd1105303f584d48603f01f881b405a88829812c08523f107801c406202aab80fc07d92ac87803a60e0233416894646a,0x26800af05002b815c8d0468]⟩
def parentRuns : Column := ⟨24,#[0x54d0c653a0c352c0bc51d0974f00964e20944d90924d70904cd08e4c908c4b908a4a308849108548408048207e48107d47f07b47d07947b07747907547707147406f47206d47106c46e06a46a06846206645406444806243c06043405e4260584170504090273e10263d30243ad0233a502239a02039101e34b01d33801c31f01a30b0182c60172af01629501427f01223901121e01020100e1f100c1e600b1d700a1af00917b00815a00712900610c0050ec0040b900308200204d00100c000,0x8f81848e51818d417e8c01798b81778af1708a716d8a616c8a416989816389716188915f88115388014d87f14285c14185314084b13e80513d7f113c7d913a7c613879e13779113678113373d13272313170b12e6c312d6a512c68712968512567d12367712167411f65c11e65511d64811b64611864311664011363210f6280fc60c0fb6030f95db0f85cf0f75c00f55b90f35b20f15ab0ef5980ec5960e85940e05930df5910dd58f0db58a0d95810d757b0d55700d35620d05510ca54e0c8,0xac154aac0546abd53eabb538aba531ab9528ab5522ab44b4ab34acab24a9ab14a6ab0487aac44caab41faa2416a9c3ada9b355a9734ba92346a91340a8f2c6a882bfa852b9a842b5a82243a7d239a73236a70232a6d22ea6a22aa69226a68222a661f1a651efa621eba5b1e8a4d1e4a341e3a2c1e1a281dfa271dda1c1daa0a1d7a091d3a011d19fd1cf9f41cc9e81c99dd1c79da1c39d31be9d01bc9c41b99b71b79b31b39b11b199219595219494419393619192a18e91b18c91518a907187,0xb87acdb869ddb859d6b839b6b829a6b819a2b7e99eb7799ab72996b708c8b6b8adb6a889b63826b61802b5e7fdb5d7bcb597b4b5779cb54799b50789b4b73ab44737b43733b3d72db376fbb346f1b2e6dbb296cbb1d6c0b146bdb0e6b9b086b5b046b1afe6adafa6a9af7672af5669ae9663ae3653ae164eadc630ad862cad5621ad25dbacd5d9acb5b4ac8585ac255a]⟩
def exitRuns : Column := ⟨25,#[0xc652b861a8bc2f143612ea070964e004a26bc24932e12098b08e4b9846259c2292a0110937085490040241c1f92020fa8fd07b47c83ca3cc1dd1de0ea8eb071473837a3801b51b20d88d506a46383422d41991520c889006244003021b81790c40b084c05041d013a0a4098fb80487c30233bd8111d80080e8003c72801d36f80e1b10068d4603068b01732180b18a0050c100245f00112d38081630038ad601855300b274805120c02482c0103b00071a38030b400144c40081f80030c60010498004178000048,0x1848810c0c3a45fa1a62f30bb1778568b8426c5b60fc2d907a16983b0b1c1905860c02bf04a15381c8a6c07050a00e282fba1407cf09f3e1c4f5e7c278f2013a77f89c3b9c4ddd3626ce7d13372b09938384c5be025cdd012d6c209635984a5a8424ad3d123696090b46847da1c23ccbe11d65188db1bc4618ce22cc6211362c887b10c3f18661f6be90f95ea87c2e343dd6f81eab5c0f35a7078acd43bd63a1d8b060e85810702bf037d5ec1baaf00db57086cab3c35d5761aaaa90d354c8682a043294ce190a5f,0x34ba071a35008d0280263f3fe31c9ff18c4ff8c527fc6233fe30e9ff1634ff8b0e7e457f3f22b99f795acfb8a567d65233eb28d9f5944cfaca1a7d65053eb2439f591ccf988da7b04653d522e9e91154f3c89a79c4453cd2019e50fecf287e67943eb3ca1f19e50f7cef87ae7583d139a1e49c18f1ccf478665a3bf3171dd9858ed4bcc75e5ba3a72d91d19618e7cad473254639328a1c793c0e1c98c6fa4a23792491b99198dbc8746ce4103632001958ea0ca463464e2f432316a18e8aa0c644f062a25c30f118,0x7bca98bda54b5e72a50f3351a789a8b39d542dcde9fee674fe72da7c394d3c9bee9e4de34ed6dba73365d385b029a8d7b4c86b9a6135ad2f1ac6970d5b4b26a9a57342d2a99ca952cd349e663a47329d20d93a900c6147a62ca39b10d1b576e8c8bb345d5c0a2d2da51696ca8a8b5d454585a2a2af512556a892a95448546a23aa1510d4fa886a71441531a2029450fd48a87697143a4b4a1d25850e52b28729534384a6a1ba43d0d913286084942f41fa1720b509103e83a75b41c39aa091cbd048e528246ab412,0xb40ab359d559ac9eacd649566b20ab3588d59ac36acd603566af4ab3578d59abb2acd5d1566acdab3548d596a22acb509565a73ab2d3855969b6acb4d15659ddab2ced559275aac936d5629aaab0cd3558668aac133d55d99aaaaccb554246aa9d19154e8adaa4c44d522212a8104d53f802a9ebfed4cdf66a62fad5317d2a98be7d4c5f32a62f93531]⟩
def arcs : Column := ⟨16,#[0x86007600a8009b00a1009500c200b200c000b000a200960021001100a7009300a500910041003100810071004500350087007700a9009a0066005600a30097002300130064005400aa0099008400740044003400a0009400430033002900190042003200a6009200a400900022001200800070006000500040003000200010,0x314030002f402e002d002c002b002a00290028002700260026402500180017001680154014401340240023002260210020001f001e201d001c401b401a4019401290110010600f400e400d401e901d401c001b001a0019001840174016301500140013001220114010a00f000e000d000ab00980085007500c800b800280018,0x270026002640250047404640434042404d404c40374036403f403e4039403840454044404d004c004b004a003d003c404900480047004600450044004100404043004200414040003f003e003d403c003b003a0039003800370036002b402a40334032402d402c402940284031003040350034402f002e40354034003300320,0x6f006e706d00373064406340628061806c606b006a006900684067406640654060405f405e605d606800670066006500640063006230613060005f005ea05da0524051405a4059905440534050b04f404e405810570056405c005b3055002fa05c405b805a00592058505740560055402f60540053005200510050704f004e0,0x920091008ca08ba08aa089a090408f008e008d00886087a0146086608c008b008a0089008830870014308630850084000e0083007d407c8079407880824081406d403780754074606f406eb07b407a508200810080007f00730072607e0049107d007c307b007a10770076107900783077407650750074a0734072a07100706,0xb700b600b500b400b300b200b100b0a076004050b1a0b000af00ae00ad00ac00ab00aa00a1a0a0709ba09aa09da09ca099a098a09f009ea05b003470a900a800a5a0a4a0a700a600a3a0a260a500a400a300a2004ea028a0a100a0009fa09e009d009c005ba034209b009a00990098009700960096a095004e0028009450930,0xbea0bda0c0a0bfa0bc20bba0baa0c320c200c1705c303530ce00cd40caa0c990cc00cb40c860a360ca00c940c800a3306000c700c640c54050204fa029a0c400a120c370c2a0c120c000bf005c603560be00bd00bc70bb00ba009700960096a0950050704f002900b7a0b6a0b900b800b3a0b2a076a04080aba0aaa0afa0aea,0xef30ee301430ed30ef00ee001400ed00eaa0e980ec00eb50e6a0e5a077b041b0dfa0de60e2a0e1b0ea00e950e800e700e600e500e400e36077104110e4a0e330e200e110e000ad10df00de30dd10dc00db50da50d5a0d4a0d3a0d2a0d940d800d700d6006460d1a0d060cf60d500d400d300d2006430d100d030cf30c470a17,0x106010531080107210231013051302a31082107010631050104010300cd00a84102010100ba30983070003a90ba2098210020ff210000ff0051202a20fe00fd00fc00fb00fb10fa00ba00980051002a00ef10ee101410ed10f900f800f760f620f520f420f920f820f740f600f500f400ef20ee201420ed20f300f200f100f00,0x6401140113911290bc40bb30993071903b90bc50bb209921112110211101100052202b210f510e010d00fc00fb00fb10fa00bc70bb00990052002b0106210511041103110c010b0070103a810421032106110521021101110a2109210a0109010221012051102a110030ff310010ff10ba109810fe10fd10cd10a8510431033,0x12701260116211560641114111381128125a124212321222125812401230122006421142113b112b1210120011f011e011d011c0052102b111131103111111010bc60bb1099110f410e110d10ce50a951183117a11a0119a11b0108a1163115706431143113a112a052302b311b2108811a31199118011790ce40a9411601154,0x10d00fd00bd009a0053002c0133013201312130208a212f213e013d013c613b213a2139213e213d213c413b013a0139012e312d012c212b201a212a213841370136113500f101340133213221310130008a012f012e112d212c012b001a012a011a211981181117812901280071803b81182117b11a1119b1161115512721262,0x3e81482147214a0149214d214c214b21582157215801570146214520782042115621552156015500de20aa11540153015200eb00b851510150014f014e01170103614d014c014b0078004231172103414a21490148014700cb00a64146014500de00aa3074003ea0bd209a21442143214401430053202c214201410140013f0,0x16f116e015410ec50b9516d0151a16c016ba118610460d5016a0169a168a16701667079304331184104416521649163014840cc40a74068016201614160415f915e015d40df30ab3075a03fa0be209b215c215b215c015b0054202d214201410140013f010f510e00fe00be009b0054002d014f214e21512150215a015900742,0x1870186013a01850184118300f501820181a180008e017f017e417d001a417c416c216b816d2151817b017a8075803f8163214861650164b0d5216a21698168817921782177617661790178017741764068216221616160616721665175217421750174015fb15e215d60791043117321723173017210df10ab1121017101701,0x1a301a201a101a000e100ae1172015510e900b6516b014ea19f019e01190105619d019c007c004631150101419b019a015d014540c900a44199019800e300b03072003ca0c1009e21970196019501940193019200590032215b0143011000ff00bf009c0056003001918190008a818f818e618d018c018b018a6189002021882,0x1ac706f30393111410041b50197915c414440c0409d419541944193419240c310c2309f305a903390e420b121b461a421b301990073203d206801b201b101b0015f915e01460116010200ca00a500581057003101af019c8166014b81ae01ad006e00388164014961ac01ab01aa01a901a801a701a601a501a4019a607a00441,0x15651d601d5907d8047816c614f61bf01afb12521d401d351d251d131d001cf61ce617941cd01cc41cb40d901ca01c961c861c781c601a151c501c431c391c201c101c0019f607b504551bf719d31be01aa10ea10b710d531bd01bc31bb3167314d314c30e250af5165714a71b4019ba11a6106606c01ba01b971b871b791b60,0xb21174115711da11d9113a11d810e550b2517a015971c451ada128610b61c401ad71dd31dc018c71db7081304c3126410941d541a79174415740e540b241c101a541da41d9413a41d840e730b43081904c90e720b421d501a721c141a50081204c2174015701da01d9013a01d80126010900e500b2007f004a01d701a381735,0x82904d90e820b521d661a8217901e901e801e701c321c241a60082204d217501580127010a00e600b30080004b01d551a78174515751e641e54081804c817a115961c441adb1c111a551e601e501e401e301e341e201c411ad61da51d9513a51d851e161e001df01de01dd21dc118c61db607f104a11d511a731c151a510e51,0x1ec11eb61ea61c581aeb1c381c211a651ed01e621e401e301e341e201c521ae6080104b11d671a8317911e911e811e711c331c251a610e610b31175115810e650b3517b715a71d101ec01eb71ea71c591aea129610c61c531ae7082304d3127410a41d6a1a8917941e941e841e74175415840e640b341c391c201a640e830b53,0x4005ea212000200c642117210820f720e220d720c020b720a620972080207720632057204a20372024201020001ff51fe01f901f801f7a1f6a1fd21fc01fb41fa01f591f401f361f261f9a1f8a1f701f601f541f4a1f331f201d6b1a8817951e951e851e751f101f001ef61ee6175515851ed41e68082804d817b615a61d11,0x250624f624e024d424c324b324aa249a2050248224762462245024402439242601162410240023f023e023d023c023b023a0239023802374236023502349233423292310230922f022e322d022c922b422a9229022802270226022502243223022202210220a21f021e421d821ca21b021a42190218621762160215021402133,0x28d328c028b428a02893288028761fe4286928502840283028222810280a1f2027f027e627d027c027ba27aa2030279627862776276a275b2740273327202716270026f026e026d626c026b126aa2693268026712660265b2643263326202617260a25fa25ea25da25ca25ba25a325972583257325602554254a253925202514,0x2c302c202c1a2c002bf02be02bd02bc4236023502bb62ba62b9a2b802b702b602b562b402b332b20226422542b1a2b0021e12af82aea2ad02ac92ab02aa22a962a802a7000600d030040113a21802a692a572a482a372a222a172a0029f729e629d729c029b729a32997298a2977296429502940293529202910290028fa28e0,0x300b2ff02fe32fd02fc62fb02fa02f902f862f702f612f5a2f432f302f212f102f012ef32ee32ed02ec72eba2eaa2e9a2e8a2e7a2e6a2e532e472e332e2329b02e142e0a2df92de02dd42dc62db62da02d942d832d732d6a2d5a29902d422d362d222d102d002cf62ce62cd02cc02cb02ca02c902c802c7001702c602c502c44,0x3350334421a2333633293315330932f632e932d432c932b62a8332a33299328321c032773269325700a016143249323400801b1032293210320231f031e031d828a431c031b031a6319031823170316431503149313031261fa43114310030f3283030e230d030ca1f6030b030a630903080307a306a3050304630363026301a,0x36a3369336843674366036593644363436243614360035f435e335d335c935b935a2359232403582357435603555354201d2353035203510350034f034e034d034c034b034a034942bf02be034883474346034503446343022e322d034263416340633f033e033d02b962b8433c333b022a2229433aa33902ae2338533723366,0x39703960395828e439a23990398431943949393039261f6639a939943980319039743964395328e039423934392a1f6a3910390838f538e538d038c838b838a8322038963888387b386138553840383238203810380237f637e137d137c037b337a537913781377137613751374537353720371a370936fa36e636d636c336b7,0x3b103b003af03ae002303ad03ac03ac42c302c203a983a84346034503ab43aa4232923103a763a64346434543ab03aa02c342c243a933a80232223143a7a3a602ac33a4533773a5733743a542ac03a463a193a053a3a3a273a393a243a1a3a06216339d339c939b300a31b9739fa39e700a01b9439f939e4216039d039ca39b0,0x3c853d343d293bd83bc83c543c463bf83beb3cb13ca53d303d223d103d003c323c263cf13ce13cd03cc33cb53ca13c713c613c913c813c753c653c503c4a3c393c2a3c163c063bf33be73bd33bc33b243b1439f43b993b443b343b043af43b803b743bb93ba93b693b593bb23ba239f03b923b843b703b623b523b403b303b20,0x3f233ed43ec43f103f003ef43ee43eb43ea43ef03ee03ed03ec03eb03ea02c603e543e443ad03e903e8034b03e743e6423903e343e2434b43e703e602c643e503e4023943e303e203e143e003df03de03dd43dc03db43da23d903d803d703d603d503d402c503ac034a0243723802126355b349032022c4023703cd43cc83c95,0x413a41ba417041aa41904180012020502030417a416641564146413341204110410040f240e240d240c940b340a3403440243ff43fe4409440843f343f283fb43fa43f543f444014400440904080407040603f903f844050404140304020401040003fd03fc43ff03fe03fd43fc03fb03fa03f943f803f703f603f503f403f30,0x448044704462431244564440443444204416440243f043e0088300500ef3003043d042b043c443b5438a437a43a4439043664356438043704360435340f040e04340433043284318430642f042e442d042c642b642a042904283427001222480010a00300850001012e042604250424342334223421a420a41f141e141d141c6,0x45d046d0442346ca429a46b418a4009946b018a00092450246a8469646864670466443a0465644d046434380463a46204613460045f4444845e645d045c445b045a642d6459043e3458042fa42424570423212e112c045620094455017e0007045424538452a4510450944f043c044e644d044c044b044a04360449a41914107,0x4542482040504813452a4800403047f1450947e0462441a7401047d344d047c03ff047b143c047a03fd0479a438a47803fb0477047664366475040a740ab3f704747438047304600420b40c13f503f33436047203f3045234705469347164690471545204706438346f34121438046f0412246d4442846e445d446c6429646e0,0x28a64a964a804a7328334a614a504a401f604a314a284a1a4a0049f449e049d649c649b049a00060062348b0499a4980002011394975496549554943493749244914490548da48ca48f448e048b648a648d048c048b348a3002905ea489b488b48914881485a48714860486a002005e04850484046704830421b421740704051,0x4d064d514d414d314a104d274d1900a01c944d0448f04cf04ce94cd54b554cca4ada4cb628e64cc04ad04cb328e34ca01fa04c924c854c724c674c504c4449f24c364c2a4c1a49b34c034bfa00a3169a4be748d04bd44bca00801bc04bb04ba24b904b804b704b624b504b404b304b2a4b104b024af04ae44ad04ac34ab04aa6,0x4f004ef24eea4ed04ec04eb04eaa4e924e804e704e604e504e404e3049864ba2486000420db54c9a4e2a4c984e2849d24df64d504e1049114e0100400db749d04df44db84de74de54da74dd04dc54dba4da54d974b574d954b554d821fe24d904b504d851fe54d801fe04a124d254c564d764c544d7400a21c964d1b4d6b4d69,0x515850ea50da512a511a51b051a051905180517051605140513a47b05155514a513051205110510050f150e050d050c050b0508a507a50a05090506a505a508050705060505050405030500a4ffa502050104fea4fd650004ff04fe04fd34fc04fb04fa04f904f6a4f5a4f804f704f4a4f364f604f504f404f3348714f204f10,0x12546854505440543054245410540053f053e253d253ca53ba012b279201040010133053a053904120538353735363535a534a4190533a52a0532a5312530252f252e340c352d051f30180299029b052c052b0410052a0529052845274526452525242523252225212520251f940a951e351ba51aa51d051c0517a516a47ba,0x527056205610560855f255e055d055c655b055a2559055845570556255525540553001842e1001630050552053b00ef000104380551055094122534854f45000413b436054e041044fe34111410752494fe04160415054b254d054c04162415254b053e053d053c853b854a054905486547254a2549254845470012927900106,0x584058304173582841715815580557fa569a57e655b657f0569057e355b357ca181a009a57d0543457c01810009057b157a5579357865770576445005756574b44d35733438057245509571052b7570056f356e156d556ca56b056a4569056865576567355335381566053711332131056510097564054745630191000705280,0x59505358535551905101454059405230523a5100593344d359205338525a50e043c5590557b7591757b5591557b0591043c759075293529143c05900529458f258f00945003258e656d258e456d058b6555658d0580058c553f10947003058b4555445225875577658a6577458a4586857b05891588145205877586a43a05850,0x5b775b6a5a305b745b69008017005b505b485b345b355ae05ad05ac128315b205b105b065af25b225b125b045af05ae35ad35ac228325ae25ad25ac328335ae15ad15ac028305ab45aa55a9a5a805a745a605a545a465a305a20004306235a105a0a59f159e159d159c359b159a000200d005990598557b4597051d059605793,0x5d335d235d105d0000a11d355cf25ce65b945cd45a925c865c585c455cc85cb65ca85c945c785c665a715c315c295c115a935c875c795c6700a01d345c595c445a705c305c285c105ba128a15c005bf05be65bd05bb228e25bc05af05bb328e35ba028a05a315b755b925b865b905b845a325b765b685b6b008117015b515a33,0x5dc15c515e735e655e515df15de15e215e115ef55ee55fd05fc75fb95faa5f965f865f735f675e435e335f545f445f305f295f145f045ef45ee45ed05ec45e935e835eb95ea95e925e825c505e725e645e505e425e325e205e105e000f805df05de05dd05dc05db05da05da15d115d015d905d805d745d605d325d225d505d40,0x61706160615061404760613960e160d15db0612261125db26120611060e260d25b48610060f060e360d360e060d060c06072606260b260a260b060a0605260426090608060706060605060405da05da259a25b3459a05f315f285f155f05603060285eb85ea85fd15fc65fb85fab5ed15ec5601060025ff05fe05f725f665dd1,0x630062f062e062da62d052ba62c462b462a462925256525352b061d261c161b161a1628062704761613861b261a261d161c261716161626262526260625061726162615161416242623262406230615261426220621062006191618561b361a361d061c361f061e6617361636153614361f261e461d361c061b061a061906184,0x64d364c263ba642064f464e164d064c163b9630564b062f564a01385136064950070647a45406480647051e061fa61f051e1450964606450644961b044d06430642052b46414419151f262d5617064005220521063f063e863d263c663b063a4639008860012638063706361635001822d40016a003063446330138063206310,0x65e065d06591658865c265b265c065b06592658b657065a065a2657352c665646593658a657265906589657152c452c56565621060c060c152c7642164f56552654265506540642264f664e064c064d163b865306520651a6502653265226518650064e364c364d263bb630464b162f464a11384136164940071642364f764e2,0x667867206712670267226710670066936682667b65e165d16653664366516641660165f16634662164a166b566a5645366ca66e066da647066fa66926683667a65e365d3647266f866e366d9645066c966b466a4669166806679660365f347796669660265f2665266426650664065e265d26635662064a011e06610660065f0,0x686067406280452167f5677668566846683668206814680a450167e152a3452067f4450067e052a26791637867da67c067a2639b67b0650067811841009167a3639a6790637967801840009044d167586772676a6770676844d2675b44d3675a44d0675966e266d8645166c86740673047786668645266cb66e166db66906681,0x6bf06be06bd06bc06bb36ba26b936b806b736b626b536b406b396b206b106b006af36ae36ad06ac06ab06aa06a956a806a706a606a506a436a306a246a186a0669f069e469d469c469b600a0066069a069936980697a696169586941693969216914690b68f6425168e468d168c368b168aa689000201b104261688068706828,0x6fd06fc06fba6fa06f9642606f816f7a6f636f506f416f306f216f1a6f0312d36ef06ee76eda6eca6eba6eaa6e9a6e8a6e736e676e536e436e306e296e1a6e096df06de96dd66dc66dba6da06d946d836d736d6a6d5a6d406d326d266d126d006cf06ce66cd66cc06cb06ca06c906c806c706c606c506c406c306c236c106c00,0x6bd06bc072f272e272d672c072b372a072947280727072606ad26ac27250724072317225721a720a71f471e06a2671d600a30d3071c371b371a271957182717a7162715a714271365392712771127103698070f470e270d900401bc053a270c070b070a670907080707a706a7050704b70367026701a700b425045636ff06fe3,0x76da76c376b076a1769076817673766376507647763a762a761a760a75fa75ea75d375c775b375a375907584757a756975507544753675267510750474f374e374da74ca53a074b274a67492748074707466745674401320743074207410740073f073e073d073c073b073a07390738073707360735673427330732073107300,0x6b027930792078d269a178e8791a79027918790071c278cb008011f0662011d078f40060170169a378ea78d071c078c97855784878b778a278b578a0783778266315789078807870632578617857784a783578247810780677f077e077da77ca77b077a677967786777a776b5390565377507746773077207710770676f076e1,0x7a4a7a3a7ac37ab77a837a7363207b547b2a7b197b427b3013747b067af67b207b147b037af37a0a79fa7ae07ad27ac67ab27aa07a907a867a767a607a507a407a307a207a107a0079f079d279e079d079c079b079a072d672c079527942799479807976796279967982797479606b106b007932792272d472c2795079406b12,0x7da07d907d807d784b127d607d507d467d307d237d107d0231927cf47ce07cd15af07cc27cb07ca04ad07c917c807c7431507c6a7c566310663064907c2a7c1a7c0a7bf67b767b667bca7bba7bab7c607c537c407c337c207c107be07bd67c007bf37bea7bd37bc07bb07ba17b907b817b737b637aea7ad77a6a7a5a7aaa7a9a,0x80708060805280408030802080108000737073607ff27fe27fd07fc07fb47fa06b936b807f927f82799479807f717f60733273227f507f406b516b427f307f2079127f157f037ef600c01cc471f07ee67ed97ec57eb97ea67e997e847e797e667e5072137e437e397e236a007e177e097df700a01e847de97dd469e07dc07db9,0x8448843084268418840b83f183e57e9083d283c083b083a2839683818371836083538345833183218311830182f182e582d582c082ba82a9829a82868276826882538247823382238214820481f081e981d481c481b481a4819081848173816381598149813281227de08112810480f080e280d280c013d080b080a080908080,0x73a2860085f06c0285e085d0571285c057108572856285b285a285b085a0855285428590858085708560855085407390801080126f196bf0689279b073926f1b6bf2689084f284e2853285228530852084d284c28510850184f084e084d084c07380800080026be07b4979a078f573826be284b084a884958485847084688458,0x865886c286b686e086d28722871287d287c287d087c08682867247d2870187b287a287b087a05932866187908780598087758760875a87408730644086f68720871047d08703644286f486e286d086c086b486a0869486808670593086634790865a73a0860285f28020864286328022864086306c0085e285d279c086208610,0x62d3550088428832882241b553356cb06c206a428041804373c36cb26a406c2273c178907880881173c0804080426cb36c236a4178918810788111f064a064a173c26cb16c216a43588088004182571052d273b0826880307e5680506db96c106a527bc679d078d373d24b906fbb6c326a30874287328762875887f087e04792,0x8a8089d057938a70876a876057708a608a5a87408a408a308a288a1208ca00928a0489f089e689d689c089b089a388c3191a0030899089004670898086c486c08840883089708960895889488936892201e2358001c400908916890688f088e088d088c088ba88a017e40010582101e03240322088968886887688605740885a,0x8c558c408c358c278c1457918c088bf08be646948bd667708bc18bb357708baa46708b9488698b808b718aa58b668b53187400b08b4289f68b3389b38b2389278b101da400948b0088e0885285c188508af062c062b08ae08a9289428ad08ac08ab68aa28ad28ac28ab48aa08a8289d20f30007013847b50136100508a908940,0x8f7a8f6200a412308e128f5b8f408f308f2000601d318f138f0a8ef08ee48ed58ec58eb08ea68e958e818e778e658e588e488e3a8e2a00a40d708e168e068df08de08dd38dc300401c9a8ce08db48da78d978d808d778d6a8d578d448d388d268d108d048cf48ce68cd6008006608cc08cb38ca08c9a8c8b8c708c6200201614,0x91e4911091d091c991784ad89166319691b07d3091a4919091815bd0917a4ada916431948f14915800a606a09034914491369126911091008dd090f38caa90ea90d000201b9990c290b590a590979084907290659052904600c0177490329026901890048ffb8f418fe18e308fda8d008fc48fb98fa000801e808f908d418f88,0x94504b9890d68fa08f218c749440943894209410940093fb93e093d093c093b193a0939a9380937493158c698e529368907a935a928493408ef6933600800d308cc3932393120040169a9130930492f792e092d792ca92b78f7292a500c21cf6905492949282927692699256924992398df3922392138d23920791f900a01eb4,0x47f097f197e097d397c097b097a0979197809771976097558a50974a973097209710970696f096e7481096d3641096c496b096a99690968454f0967496609654964096339620961a960095f895e095d095c095b295a0959095809570956095508c879540953495209512950094f294e094d294c094b094a09490948094709460,0x9b1088039b009af09ae09ad2889088809ac041f041e09ab09aa09a909a829a729a609a509a469a309a229a109a0499f099e399d099c299b201e9389001c0007099a4999099839970996299509940993012e16f8012c0001099209918990098f898e098d0474098c898b098a69890988098709865985098409830982098109806,0x9c909c869c7608c000709c639973133274b0131000309c509b809b609b509c409c309c2899389c169c0202423b900224009018a600129bf09be09bd19bc19bba9baa9b949b845864024039f039f49b7455009b069b7058609b0a55049b699b599b49534142019b629b529b424205534546709b30886288699b269664966041c7,0x9e109e009df09bc0181a00309de499b458610f905c505c5157409b168bb08bb19dd39dc39db353249b17574141a458609dd29dc29db241a5532513e07de07e9088609da29d929d829b248bb068009d779d159b709d629d529d424215535557909d309d249d219d169871987452e29d00531053009cf09ce29cd29cc69cb09ca4,0xa0176820a00646959ff19b7346909ff49b7957709fe09fd09fc19c959fb79f1718e900b09fa29f969f819be19f701dd300979f609a399f509e009d209da09d909f409f319cb89f269f1213e283d013c400b09f029c069ef19ee19ed19ec09eb39e479ea099f49e901da000709e809e709e689cd89e569e42090400909e369e26,0xa233a18aa1eaa221a209a214a1fba204a1f1a1dba180a1e0a1d1a1c2a1b8a1a2a19600a41774a182a176a16000801cc0a150a141a130a12aa110a104a0f5a0e0a0d0a0c5a0b597e86822a0a097e49dd09dc0a090a080a0789a78a0669f920f925e700f740090a0529e22a0409ed018410050a0309ba0a0209c7057759fe58bf7,0xa3604840a350a301a2f5a340a332a321a316a2e1a2d1a161a320a317a300a2f4a2e0a2d0a160a1a5a2b500c21ef600c01ef4a1a6a2b6a2a8a2c6a2c4a2aba251a291a1a7a2b7a2aaa1a4a2b4a2a9a250a290a2857d35a2867d36a2817d31a2877d37a2847d34a2807d30a272a26500aa1cf6a254a244a136a23600a01cf3a133,0xa3e5a4d0a4c0a3d8a3c8a491a486a471a466a3b5a3a5a4b0a4a0a441a4364841a351a411a403a3f1a3e1a371a361a3b1a3a1a375a365a490a487a470a4676876a456a440a437a3d3a3c3a394a384a414a409a3f4a3e4a374a364a3b4a3a45963a423a3d9a3c95962a422a410a402a3f0a3e0a3d2a3c2a3b0a3a0a390a380a370,0x8bf0a660a652a650a641a5651e1600b21e1400b0a642a566a631a601a643a567a640a564a630a600a622a620a5d8a50818e6009218e40090a5c6a546a610a600a5f1a5e0a5daa50aa5c4a5449d709d609d50a5b0a5a0a598a582a576a56213e2811013c40090a552a54218700070a531a520a510a500a4f4a4e0a415a408a3f5,0xa902a901a8f0a887a8e0a8d7a733a7d0a8c7a8b0a846a8a0a893a764a887a872a869a857a840a834a837a820a815a800a7f0a7e0a733a7d0a7c5a705a7b0a7a7a6d7a790a785a770a760a681a750a745a733a723a719a703a6f0a6e3a6d4a6caa6b4a6a9a692a681a671a6758bf5a6658bf6a6668bf1a6618bf7a6678bf4a664,0xaba1ab90ab80ab70ab6aab51ab49ab3aab20ab1aaaeaab00aaf5aae0aadaaad0aac28c89aab0aaa1aa90aa80aa70aa60aa50a9b0aa40aa30aa20aa10aa00a9f0a9e0a9d0a8104871a8f0a960a705a7b0a9cba964a8f4a701a7b4a9c7a9bba9a0a990a980a887a8e0a97ba960a6d7a790a95ba917a940a937a8b4a774a929a911,0xaac3ae1aae0aadfaadeaadd0adc0adb3adcaadb6ad94ada3ad99ad72ad80ad70ad60ad625b48ad40ad50ad52ad43ad42ad41ad20ad22ad38ad20acd8ad10ad08acebacf8aceaacd8acc4acc5ac95acb0aca0ac91ac94ac90ac72ac81ac70ac40ac60ac62ac30ac00ac50ac42ac32ac25ac15ac07abf2abe4abe1abd9abc3abb9,0xb0cab0b6b0aab090b08ab073b060b050b040b030b020b019b000aff9afe0afd1afc0afb0afa0af8aaf94af80ae30af50af70af49af33af62ae94af48af63af32af51ae95af50af4aaf30af2aaf10af00aefaae8aaee3ae6aaed4aec2aeb0aea2ae43add0ae90ae83ae7aae63ae9aae86ae70ae66ae44ae52ae49ae32ae24ae25,0xb162b446b43ab423b41ab403b3fab3e3b3d0b3c0b3b0b3a3b390b383b320b376b367b356b2d0b34bb330b320b310b30ab2f0b2e0b2e0b2d0b2cab2b6b2a2add0b290b280b270b260b252b24ab230b223b210b206b1f2b1e0b119b1d0b1c9b0d9b1b0b1a9b190b019b180b179b160b150b140b133b123b119b100b0f3b0eab0da,0x8c87b630b620b4b0b610b0d9b1b0b605b570b401b4a2b5f5b192b5e4b5e6b5d0b5c0b5b6b5aab585ada0b595b590b580b3aab470b568b570b572b019b180b558b3a8b472b56ab01bb182b55ab540b530b520b512b4e0b500b502b249b4d0b4c7b4f0b4e2b24bb4d2b4c5b4b0b403b4a0b499b119b1d0b489b3aab470b463b450,0xb870b867b850b847b837b828b818b805b7f5b7eaac33b7dab7cab7bab7a4b79ab780b770b76ab750b742b733b723b713b700b6fbb6e0b6d0b6c0b6b8b6a0b690b680b670b660b650b640b340]⟩
def graph : Graph := ⟨2952,12,13,240,300,rows,actions,parentRuns,exitRuns,arcs⟩
end CoJunctionArchive0

namespace CoWholeRoot0
open CoJunctionComplete4482 CoJunctionFixed4482 CoPortRoots4482
abbrev gr := CoJunctionArchive0.graph
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private instance : NeZero gr.size := ⟨by decide +kernel⟩
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def hints : Column := ⟨17,#[0xff087f847eae9f961fcb9cf78eeb0f3963bcc87f7877aecbd72dea9e768f6b2f99d3dcc8f76cfd361fe21eeb93f6cbbaaf1dd3aeb9f37cfabafc9d3ece19f787dae9edc1f6c19f80bdaae79c376bbcb84edb2f8e63f4c8fe706fb43f5e1fcf0fe587f2c3f9c17ee0fb6c7f2c3f961fcb0fe587bb43ee11eed0fe807f2c3f961fcb0fe587f2c3f96,0xff29ee68fcc07e9b27ed9de60e7ba5f960ff21af64e7ba5f9627ee96f603fc25bd671ee17e643fc47d9a3f301fa689fba5f9a33f117e58f9c47d9e39ef9de603fb87f1c3cef9ee659bbc5f9839ef9de61f8bc7d9e71ed17e59cbd27d9d0ff01f674f9c47d9d63ef97e60e7b85f96772f1fa75c7b4779a74f19ee71fc407e9a1fcb87f703fbc1fdb,0xfee8bf5c9fb25f9827ef16f649fb65bd627ef97e643fba6f9b33ee1fa78e7be779833f017e5cf3ba7b9a27f097e603fc67da07cb19ee68e7b85f9839ef9de60f9c87d9e67af17e59f8be7e990ff09ee69f1c07d9e39ee17e58e7b85f963f319fa659eae77987e2f1f679fc407e9a0ff19ee743fbe2fd927f017e603fc26bd839ee1de649fba5bd8,0x3e711f678e7c0779871ee17e64f3b87b9a3f2f9fa683fc45f963cf09ee70e7ba5f9871ed1de68f9c87d9d766f1f675dcbc7e9d0fed9fc6cf9c87d9d39ee17e61e6b65f963f319fa65f2c67b9a7e2f1f675fc3e7e9a1fcc07f7c3fc21fe10fef9ee643fb86bda33ef17e603fbe6bdb39f01de683fbc5bd70ff11be6cfcc07e9c39ef9de60e7bc5f96,0x39ee97e58e7be77980fef9de64f9c47d9e39ee97e5cf3be7b9a39ef17e58fcbe7e9b0ff117e70f9c47d9e39ee17e59dcbe7e9b39ef9de60f3c27b9a7e2f1f679fc407e9a0ff297e583fc65bd939ee97e603fc25bd639ee9de649fba5bd80ff097e64fcbe7e9b39ef1de60e7bc5f960ff09de64fcc07e9a39ee97e60e7ba5f963e711f6743fcc5f96,0x3f4d1fa687f381fda1fce0fe70fb403f9863ec8fe60e7b03f987e4f8fe61c7b03f9874f08fe60fd347e9a3f4d1fa68fd347e9a0fec8fe703fb01fd71f6c0fe703fae3f9c1f6c1ee74fe467f1f3f8f9fc7cfe3e7f1f3f8f9fc7ce7b83f571bec8fd5c6fba77583ecf8fd5cef363f573d6f8fd5c7bbc7e9b0fef16f649fb65bd60ff117e68fcbe7e9a,0x3f8e1f388fb3a7d9d0ff19ee743fbe77980ff097e5c3fca7b9a0ff217e5c3fc47d9a3ed08fe60e7b03f9839ec0fe60fd423f981fcc0fe607f303f9839ec0fe60fb423f987e4f8fe60fb403f9839ec0fe61e6b03f983f508fe61f33c3f987e4f8fe64fd347e9a0fed0df5df33c3f9839ec0fe60e7b03f983f508fe619eae3f987e4f8fe64fd347e9a,0x3f508fe607f303f981fcc0fe607f307b603f4d19f84bbac73e21eec1f678e7ba75d837cc87f74df327da03ed01e780f7347b9a0fef9ee643fb85f970fef97e583fc46f9b0fee9de64fd423f9839ec0fe60e7b03f983f509cf607f307ea11fcc0fe607f303f981fcc0fe60f3c67d9e39ef1db60e7bc5ed63ced9ee68e7c03ed83eae9fa68fcbe7f1c,0x7e8d4fa89fc3be69b7f0efe289fc39e69e7f0dfca8dfc3bf89e7f0eff080b7ac1fde2dec97e58ef301fdf3bcc97e70bf381fe22fcd1cf60fb427ea11fcc0fe607f305f9627f096f589fb65bd62fcb1de603fc277992fcb07f98bf2c73dc2fcb17e58e7be7f1b3f8d87f94bf2c1fe32dec87f84b7ac1fe12fcc9f684e7b03f9839ec0fe60fd427da1,0xfed8fe5c3fb61fd90fec8fe607f303f971fcc0fe607f303f980ff107f8c3fc23f603f8e87f8c7bba37e71df68bf807bd61fe80feb8fe5c7eb43f971fcb8fe5c7f2f3e997e8d79a61fa353e9cbb4ce7a776d2ff2a17e8d1fa7df5353ea5bd4ce7a8b752fe6a0f54bfe279fa35cea47e4d4fa72f933cea0de4bf3a8fb937e69df64cfca97e939f2a6,0x17ee8ef605fb83bd91fcc8df6ce7b07da01bee07f647dc43f981bec8fe606fb23f981eed0df647f303ede1f6f8fb647dc47b9a1eee0bf707f302fde1eec8df707bb23bdc1fcd0f78c7f3037d91fcc0df647f303de31fcc0df687f303ee21fcc1f3887f347d9e1f6d87f783fc237dc1bf70bf8c3fd07f1d0fee87f7c6fb43f9d3bcd87f943fbc1fda,0xff01f6847daefc61f4d07398f733eecda6f2f3f187e346f4da1bed17e787daff6277ad2dba89be43ee1d7e90fe19bccc7ec9bf3503f487f43efd211dec8fe60fb3e37db1def8f77c7dc83edf1fcc07f6c77b01fdc1dec8fe647f363f991dee0df687db037db1f6c0f789e3b877971eef0fb74fcbc5f961faf1db80ef303eda1f6c9af685fb83f9e,0x17ec9cf74edb4f3973bcd07f7c77b49bd71ded13f74b7b279dd3d6e3e678fd307e9a33f00f7689fbe5dd972f39f671e3c075d93e6f1f96dfc387e9c0ff20fd689fb45f5979ae1dd69f2c67d9c0feb0fe583fb41fdf3f343f17ddcbcfc5f9f31dd979adaef658db2d3d985e7463ed81f6c1e783674c5ed60fef97e707db2f8e2f1d13e989f3483ed9,0x1fcc0fe607f303f981fcc0fe603fb61fdb0feb87f707bbe3f981bef17b586fbe3ed81df11f6786fbc76d83f4d1f6783fc63bd90fef87f8c3fba3bde1fcc0df687db237dd3b6c0f778fb3c37e11bf09fc74f7447f233f8f0fb80fd381fe11fcc8df74eeb41fe01fad0ef747eb637dc1fad0ef70fd3c1fdf1f6d07f747f344fdd2f6c93f68bf321fe0,0x7d8f79685fc3abf257f0ebbc89fc36f7267f0efe48c7bb277983aec07f80fd361fdf3dcd07f807f303de41bed8fb84e7be3f9a2deb17e583fc277980fee0fe603fb677980fef0f7886fb23ee51f6f8df807f301fda2deb07f6c77b05f963bcc07f707f301fdb2fcb07f70fb407f1b0fef07f8cf9c63f9839ec0fe60e7b03f983f509fa847f367e5e,0x17f597bb07ec03fa01ef587f886fbc37db4df707f6c3fb01fe30ff207f8c7ec03f6073b407f8477b8e5ee4bef8bf6dcdeae3e40fec87f605fac1fd80fed1f67df63cbda57d8f1f68dbb3be59b7d8f1f691eb3d3d9ebacd6767f6b37f1a17b4d7368af3359da6dccdf36a3b339e5a1f4cdfe27df63c7da67d4f676737537e59ef54dfc697e53c7da6,0xfee0ef60bf2e7b9a2fce87f8c7f381fe01bf08fe606fbc3dd817ed8f76077c473e03bcc1f38c7dba3ddd1eef8f7643fb86bda1f6f8fe60e7b03f9839ec8fe607bbe3f983aed8fe607f343ddc1eed1ee68f7341fdc3cee8fe61e3b43f9839ec0fe60fb3a3f983f8e1fc70fe387f1c3bcf9de68fe3c3ddc0fee07f6c3fb81fd90fec07f806fb837e5,0xba6e6739f69bcf4e379d27569767499cedc7d2ba779e3b2f965f1d1be38b9d40fc79e5d26738f8f3ef55973b063e7df1b87cee767117e857b4cfb22f2cf7a67deb44fb271ded1ee7c6fb437d91f6f0f7807db63f9c1dec97e703fc67f1a0ff10fe745fc21fdb1fcd0fe587f343f9a0fed8df7c7f3037d91df18f7647bc43ddb17ef0fe603fb63bda,0x39ee17e58fcbe7e9b39ef9de61b3ca7b9a3e711f678fcbe7e9a27f19775d1fb65f9747ee0bf64e7be75d879cb9de609fb25bd73ced9ed6dfc387e9b73cf9ee6c9fbe3f5927ed17d5ccfcc7d9d79af1dd60fd341fd81dec07f707bb01fd80fec0fe603fae3bd81eeb8bf587bae7ce91fd12f389f1c43dd80fef9de99d9c6f8e53e7517e996bb2f4da,0x1ef01f6786fba76d81eef1fa68fe3a1fe00ff107f807bb41fdd39ec0fe60ebb63f981f700fe60f5ba3f983dcd0fd7cdebc7f212fb00fd7c7db87e9a0ff08fd647bb83f9a1bef1dd603fc05bd60fef16f589fb65bd60ff117e58e7be77983cf01ee68e7b85f960fee1de60f3c07b9a39ee97e58f9c47d9e39ee17e58fcc47e9b0ff097e58f9c67d9e,0x1dec0f75c6faf9b9b7b8d4ee8ab737e3997b8d66e836737f4a17b8d72e91ed359ba3bb4de6e7f6d37e39ef34d66e95fc3aef227f0dfcc909fb65bd62deb07f7877b05f960ff10fe60ef305f962fcb07f747f321fe02deb1cf607f3037d91f708fb7c7f301fda1dec17e58f7347f191bf09cf607f307e5e1fcc0fe6077c27b9a1bee0fb606fbe3ed9,0x1f6e87f7c6fb037d93ed03c781e3c02fdb17ed93f587ebc1fdc17ed8f7946fb63be50fec07f605faa3bd81eeb8df5c5fae3dd70fecb2f54b7ac1fe017ec3cd68bf30e3e13dce13f887f2ecbd83bccb7378fb3a7e9b79cc9de5c9fc05f963aef1ee60f9c67d9d7b2d1fa647eb83bd71fae8bf687f2e3dde1fcd8f75c77ae3bd71dea8ef5c7bb22fd5,0xd8f1bc771bb5aeadcccf7e3e9077b0a7dae3d13c7647ebc5f9b5dd53dc93c73de3a00ff00ef60e7b01fe01fcf1f6883fbe2fd91dec0df6477c23bd91df10ef703fbe3bd81fce9af7477b07b5d79ccbce64e7ae5bd72beb1cf70bf2c73d727eb07f5c3fbc1fde0fed87f703fae3be11fcc0df687f3037dd1fcc0f7887f3037d91fcc1bb747f3037d7,0x2deb33e58bf2c1fe017ec1cf74ebb4f99d3dcc93f6cbbac73db3b6dbf270fb387d9d4f6c9de609fbe5ed63f4d1cf7ceeb4fe1b3f4d9ee649fba3f5867ac9de64cfca7d9e3ece9fa6c7dc837db1fcb8fe707ebe3f971eec0fe703fac3f971fcb8fe5c7f2e37da1f6f0f7707f2e3f971fcb8fe5c7f2e3f975cf33c78077b0d9e3acf23a783c3c1b1e8,0x3dcebd968fd3273db2fcb32f78bf2c7ce33ecebc76cef2e1fdd3ecdbb378fb3a73e03bcb93f78bf3479e23dce38f64df2cee5a3f4c1fc6cf9c47d9e33ee97e5d97be5f973f2f9fa69e734779878f01ee61c7c27d9e1fae0fd747f363f971fcb8fe5c7f2e3f971fcb9fa603fbe1fdc1dec07f6c7f2c1fde0fef87f88fd2e1fdb0fef07f703fb64fe1,0x33f217e58f9c67d9e78ee9de603fbe6f9e3cf01ee709fba5f9839ef9de60f9c47d9e71ed17e58cfc27e9e3ed01f388fb3ccbde2fcb9cf70bf2e7e603f4d3ce6cef30f1e03dcdb7968fd381fe33dce87f7cb7ae73de2fcc07f785fae4fd93bcd13f70b7ae1fe23ecf1f988fd3673df3bcc93f84bf2e73dc37cb07f74b7aecbd52deb1cf78bf2c1fe5,0x37cb87f90df3879e33dcd9cf7cbf3073e03bcc37378fb3ccf5e2fcb1f98cfd387b9a39ed97e5d9eae77985e6d9f671bcb47e990fee87f685faa1fdc0fee07f743fc85f9b0fef8bf609fc25f970fef9af68e7c0779927ee16f5c3fc87b9c3f309fa6c9fb2779839ee97e58e7b86f9665eb16f5c3fbc5bd639ef17e583fc07b9a3f2f9fa689fba5f98,0x2fcb1f38cfb3c73df3bcc07f7cbf2e7ce23ecf1cf7cef3079e03dcd1cf70bf2c7e5f3f4d07f78ef3279e03dcd1cf70bf2c7ce23ecf3cd70bf2c7ce33ecf1f97cfd341fe12fcc3d37cfb3c73dc2fcb1f980fd34f39b3bcc3c780f7367ce23ecf3d970fd341fde0fef87f88d7b41fde2dec13f6cb7ac2fdb37cd19f88fd3c73e03bcd19f88bf30cde1,0x1fcb87f643fae1fd91fcb87f783fae1fd81fcb87f786fac1fda1bea8fe5c3faa1fd60fec8fe687bae1fd917ec8fe5c7f341fd90fec0f75cdeb837db3dcb9ee60ebba3ed80fec8ef60ebbe3f583dcc1ee60f7301fe33bcf07f88b7ae73dc2fcb07f90bf307e5f3f4d1cf7cef301fde2debbc774df2c4fdb2deb1cf78bf2c1fe42fcc1f97cfd3473de,0x1fccbd96c7f327f1b3bcc1ee5c7f341fd817ea87f603fb07ce31fccb2f587f3273da1fcc9f9787f32f3991fcc9ee5decb63f993f8d9de60ef3077981fcc8fe68ef303f971f6e07f603fb63dd70fec0fd605faa1fd80fec0bf64f9c63f9935ec8fe6597aa3f993f2f0fe65e7323f983dcbb8f5c7f323f993f8d9de60ef3077983bcc0fe68ef307798,0x3dcd1e78cf73473e31f6c1cf88edb07ce23ecf1e788fb3c7da13e719fa68fe361fe33dce87f7cbf301fde3bcc07f84fb3c5f960ff29ee743fba7d9b3f8d1fc80bebc3f5879cf0fe60faba3f971f6e9fa65e9be3f9a39ed8fe68fcbc3f9a79cc8fe68f72e7ce31fcc3d96c7f307f1b3bcc07f6877be3f623bcf3ce607ec83f9a1fcd1cf607f32f4df,0x3bcc07f78ef325f982fcc07f8cef3c1fe22deb9f684e7b03f983f2f1ee84f9c67ea11fcc0fe607f303f981fcc0fe60d7c65bd637cc9f678f7342fdb2fcc07f88bf2e1fe437ce1de5cfe387b971eec8fe5c7f2e3f971fcb99f94fb3c73e03aec19f90bbac7b9a3dae9fa68df321fdf37cd1f6803fc85f9b0fef9de683fbe5f980ff29ee70bf341fe0,0x1fcc0fb907f303f9917ec07f807ec83bdb3f8d87f68ebc01fda1fcb0fd647f2c3f961fcb0fe5b2f2cef189bced5e5f2f2ce798f1cebbc632f41ab96f1cf3ae5fd33eef189bcf5b65f2f41ad96f2d0bb663d936ef18cbcfdba5f2f33ae96f34ebba632f3afe1bf38d9de609fbc5bd62fcb07f90bf304fdb2deb96f5cbf2c1fe42fcc17e583fbe5f97,0x1bec0df603fbb1f9ff0ef17e61c7c29f98c9f347e746fb1e1df4fccece8dde443f9c0fef8ef607f305f980ff18fe60bf3037df0fed0ef606fbc37d92deb0bf686fba37df1bef8df8877b273db1fcc0fb807bb875d93dcd0fe703fb03de21fcc0df687f3037d91fcc0ef887dbe3f981f6f0fb6c3fba3bdb1fcc0df707f3037d91fcc0f7887f303de1,0x2dedbce64ef323bdf2fcb87f7c77b067e22fcc13f7cbbb6b9e13dcc9fa713bc05f9633ee1f66ce7bc779827ef97b6cf9be7d9b0ff01f678ef2c67e13dcc9cf84bf307e9927ed1fc6dfc347e963dcc07f78bf2c7d9d79af17e54f3b87d9a3e709fa5c3fb03f970ff007f803fbcb3e64decccf9e37beb3e671f038f81d73993e8d3d078781c7c03fa1,0x3ecf0df70edb03bdf1fcc0f76c7f307f1d17ee1de605fc82fdc3f911ee807bba7f230ff10fe6c3fc43f9a17ed1fa706fbe77991def9ee647bb83f981f6e9fa68f7421fd81fcc07f6477b21fda1fcb87f687f307ba00fed1fa603fb27d970fed0bf603fc8779f1fcc9f6603fcc2fd84eee8fe603fb25f9727ef95f69cf347e9b3f4d87f74ef344fe1,0x1f6c9db603fc23f981fcc1f6783fc67f1d0fef07f606fc25f960fee0ef606fbe5f961fcc8fe60bf2c1fe13f8d87f803fae1fe31ded9fa685fba5bd61df19f6786fbc73d81fce8fe64fb3c1fe31faf07f7c3fb81fd70ff287f746fc27d9e1bef0f76477c87b9a1bef9d76077be3f983f4d07f787bba1fe40feb87f8c3fc23be03dcd0df6c7db03ddf,0x2fce2de5e3f3737974fcf2de5f1f3f37a45f8bc7e96772e9f9b5dcbaee997e2e9fa15ecbe9e835b2fbc97774cc7e6e7d2fa797d74b9fca1fc3b9f1e1eec1de60fd341fdd3aec07f7c7f303f983dcd07f847bbe2fdb2fcb0ef603fb677980fee16f583fbc5f960ff18fe687f325f960fef0fe603fc01fdc1bee1ee847bc43ee51fcc0f778fd3437df,0x1fcc0df647f303ee21fcc0fb707db62fd979cc8fe60e7b83f983e6f8fe60fd3473db1fcc1f38c7f307f1b7f0d8fe60fe387f1b3f8d9fc6cfe367f1b3f8d8fe6cf3b63f9c3f4e07f687bb22fd50fec07f6c3fb21fd90fed07f643fb82fdb0fed8df683fb43f980feb87f643fac5f9776ccc7e5d7e2e5f9f2fcfa7e5f1f347f194fd12be5f4f2ebf17,0x1bf087f646fc037df1bee0df8477c476e01fcc0df787f3037db1ef20ef8c7bbe37d817ef0fd8c3fb01fdb1bef0fe603fbe3bd81bf08fe61e6bc77981bf107f646fba3bd917ed0bf605fbe1fe51beca7b947ec22fde0ff587f683fb81fd92f6b8fe606fb63f981eed0fe606fb23f981f6f8f7687bb62fd91fb187f683fb63ddf1fcc0df647f303bdb,0x1fcbb8f94bf2c1fdf3bcb9ee609fba5f9979ce1de58fb381fe32fcb1f988fd3479e23dcb9f38cfb387e9a71f179684e7c29be139f138f8dc7bc9fa171f0acf7137c0d5dc99f0c6f8567b8e3dc39f1a7e686fb073e269f1a7e81a7cb93e471eef9a772ec4d7573bb10df7077b47ce21bee0fb8c7bc83bdf1f6e0ef647f303f9c2fcf0df747f302fda,0x1fcc0f77c7f3076e31fcc0bf6477b25bde59eb9cf81c7b393d6c5f317e67573cb7971dec07f687f345f960ff08df943fc03bd917ef9ee68fd347d9e0ff20fe683fc81fdf0ff08df80fb3c1fe51dec0df7c7f3037e13dcd0df807f3037de3f4d07f883fae7b980ff087f7c6fbe3f973daf8df6c7f3037dd3bca87f7477b21fe117eb87f6c77ae4fde,0x4fe11df016f911fc83fa047f0a7e747f342fd81bf10df746fb23f981df10fe607dc03ddf17ec0f7847f3037de1fcc0fb8c7f303bdf]⟩
def test := rowCheck gr hints false 7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b0_128 : Holds test 0 128 := slice_sound (a:=0) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b128_256 : Holds test 128 256 := slice_sound (a:=128) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b256_384 : Holds test 256 384 := slice_sound (a:=256) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b384_512 : Holds test 384 512 := slice_sound (a:=384) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b512_640 : Holds test 512 640 := slice_sound (a:=512) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b640_768 : Holds test 640 768 := slice_sound (a:=640) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b768_896 : Holds test 768 896 := slice_sound (a:=768) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b896_1024 : Holds test 896 1024 := slice_sound (a:=896) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1024_1152 : Holds test 1024 1152 := slice_sound (a:=1024) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1152_1280 : Holds test 1152 1280 := slice_sound (a:=1152) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1280_1408 : Holds test 1280 1408 := slice_sound (a:=1280) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1408_1536 : Holds test 1408 1536 := slice_sound (a:=1408) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1536_1664 : Holds test 1536 1664 := slice_sound (a:=1536) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1664_1792 : Holds test 1664 1792 := slice_sound (a:=1664) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1792_1920 : Holds test 1792 1920 := slice_sound (a:=1792) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1920_2048 : Holds test 1920 2048 := slice_sound (a:=1920) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2048_2176 : Holds test 2048 2176 := slice_sound (a:=2048) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2176_2304 : Holds test 2176 2304 := slice_sound (a:=2176) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2304_2432 : Holds test 2304 2432 := slice_sound (a:=2304) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2432_2560 : Holds test 2432 2560 := slice_sound (a:=2432) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2560_2688 : Holds test 2560 2688 := slice_sound (a:=2560) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2688_2816 : Holds test 2688 2816 := slice_sound (a:=2688) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2816_2944 : Holds test 2816 2944 := slice_sound (a:=2816) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2944_2952 : Holds test 2944 2952 := slice_sound (a:=2944) (k:=8) (by decide +kernel)
theorem u0_256 : Holds test 0 256 := join_blocks b0_128 b128_256
theorem u256_512 : Holds test 256 512 := join_blocks b256_384 b384_512
theorem u512_768 : Holds test 512 768 := join_blocks b512_640 b640_768
theorem u768_1024 : Holds test 768 1024 := join_blocks b768_896 b896_1024
theorem u1024_1280 : Holds test 1024 1280 := join_blocks b1024_1152 b1152_1280
theorem u1280_1536 : Holds test 1280 1536 := join_blocks b1280_1408 b1408_1536
theorem u1536_1792 : Holds test 1536 1792 := join_blocks b1536_1664 b1664_1792
theorem u1792_2048 : Holds test 1792 2048 := join_blocks b1792_1920 b1920_2048
theorem u2048_2304 : Holds test 2048 2304 := join_blocks b2048_2176 b2176_2304
theorem u2304_2560 : Holds test 2304 2560 := join_blocks b2304_2432 b2432_2560
theorem u2560_2816 : Holds test 2560 2816 := join_blocks b2560_2688 b2688_2816
theorem u2816_2952 : Holds test 2816 2952 := join_blocks b2816_2944 b2944_2952
theorem u0_512 : Holds test 0 512 := join_blocks u0_256 u256_512
theorem u512_1024 : Holds test 512 1024 := join_blocks u512_768 u768_1024
theorem u1024_1536 : Holds test 1024 1536 := join_blocks u1024_1280 u1280_1536
theorem u1536_2048 : Holds test 1536 2048 := join_blocks u1536_1792 u1792_2048
theorem u2048_2560 : Holds test 2048 2560 := join_blocks u2048_2304 u2304_2560
theorem u2560_2952 : Holds test 2560 2952 := join_blocks u2560_2816 u2816_2952
theorem u0_1024 : Holds test 0 1024 := join_blocks u0_512 u512_1024
theorem u1024_2048 : Holds test 1024 2048 := join_blocks u1024_1536 u1536_2048
theorem u2048_2952 : Holds test 2048 2952 := join_blocks u2048_2560 u2560_2952
theorem u0_2048 : Holds test 0 2048 := join_blocks u0_1024 u1024_2048
theorem u0_2952 : Holds test 0 2952 := join_blocks u0_2048 u2048_2952
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def result : CoJunctionTarget4482.Certificate (Fin gr.size) raws.toFinset :=
  certified (hints:=hints) (seeded:=false) (depth:=7) (by decide +kernel) (all_rows u0_2952)
end CoWholeRoot0

namespace CoJunctionArchive1
open CoJunctionFixed4482
def rows : Column := ⟨17,#[0x300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0006000300018000c0007,0x63fab1fb58fcac7dd63ea8001470fac7cd5faaaef5552daa1455bbeabaf5297a8ac55476a82f5287a8a3d25ba972d4f1ca748d159ab19758caa00051c3ab1934000ac69d6322800158d2a0005639a800158d1a0005638e800158d0ac7156386800158cfa00056376800158cea00056366800158cda0005635a800158ccac6ad635280018000c0006,0x160e8001457ca2bdd16028aff457aa2bcd160a8b034000a2bf515f68af14000a000500028b0b4000abf5d5deeaa5d5429ab7855762a5315159aa8f55062a5115148a4b7d0002b23f591eac8ed6472b237591aac8cd6462b22f5916ac8ad645280015912a00056446b2274000a00053c7680014e92ac885159eb20b5904ac81d640ab2035900ac7fd,0x16628b5745aaa2c6d1632800145a4a2cad1652800145a0a00051622800145a2a2ddd16ea8b3f459ea2d8d16c280014593a2c9500028b6f45b6a2d4d16a28b7345b8a2ced1672800145afa2d7516468b2145b5a2da5169e8b4d4000a000516f28aed4575a000500028ad74572a2b8d00028ad14574a2b9d00028001456ea0005000280014577a2c25,0x1c928ec34760a3a2d1d128eaf4756a00051ce68e714000a3aed1d728e9f474ea00051c7e8e3d57ecabbe55bc6abb3551faa0cd4a26a2934f1ea749d64aeb2555929ac945649eb24d5925ac925648eb2455921ac9050002b27f593eac9ed0002b26d4000ac97d00028001459aa000516b280014596a0005163a80014586a0005162a800145b2a0005,0x1cfa8ea34750a399d1cca8e97474aa39dd1cea8e8f4746a397d1cba8e934748a3afd1d7a8e874742a3aad1d528e6f4736a3add1d6a8e9b474ca38dd1c6a8e274712a38bd1c5a8e234710a38cd1c628e2b4714a38ed1c728001472ba00051caa80014723a00051c8a80014727a00051c9a80014721a00051c8280014729a00051ca280014725a0005,0x663ab31b4000a0005000280014000a0005000280014000a0005000280014000a0005000280014000a0005000280014000a0005000280014000a0005000280014000a0005000280014000a0005000280014000a0005000280014000a0005000280014000a000500028e834740a3a9d1d4a8e7b473ca39ad1cd28e5b472ca398d1cc28eb34758a39fd,0x4ab2a2db5522aa0e50002b3cb59d7a94650002b3ab514ca4c3d2eca800159daace956766b3b14f21a74b56746b3a159cface756736b39959cbace556726b39157eeabbf55506a87956f3aaedd4aaea2d95521aa0dd4a2ea2974986a5d8d3c829d2b4000a00056632b3115998accbd0002b3175996accad0002b3155994acc9d664ab3235990acc7d,0x293894000a00050002933549bda4de526be935d4000a4bdd000292e54978a4bbd260693014000a4b8d25c280014979a000525d292ff497ea4c6d263280014985a4c2526269311498fa000500028001498ea4c1d260a9317498aa00056792b3c759e2acf0d6782b3bf59deaceed6772800159d6acedd6752b3a757efabbfd550aa87b56f4aaee5,0x6aea80015aa9a00050002b5515ab5a00056a9e80014000a4d1526d69369499fa4cf5270e938549a7a0005269a937349b8a4ccd266280014991a4c852656932949bba4dd5000293414000a4d950002937f49bea4cbd265a800149aca0005266e935349a8a4d8d26c280014993a4c95000293554000a4e0d2702800149a5a4d2526de936d4000a0005,0x5bdaabbd52b0a8b8d0002b5c15ad3aa9250002b5a5541ea9475453a80015ad6ad6852edab5ab5ad4a791d3a62b59f5aaaad5b55fc2af015545aa2055bd6abbb52afa8b850002b5575523aa0ed4a36a29b4000ad5a52ed69e454e97ad5356a96b5494000ad5856a8e80015aafa00056b1680015aaea00056b0a80015aadad60d6b0280015aaca0005,0x6eb6b76b4000a792d3a6a80014000addb56ebeafe55782aa9ed50e2adef55dfa953d45a2aa4b541fa947d453e97574f24a74cd6e3a80015b96adc6d0002b72b4000add150002b7294000adcfd0002b7275b9eadced0002b7255b9ca00056e4680015b90a00056e3e80015adfad6f56b76b5b95adbad6d56b66b5b15ad1ad6bd5fc6af035546aa20d,0x2b7e95beea5da56fceb7e54f27a74e56fb6b7d957f4abc25550ea87d56f9aaf0d4ab6a2dd5527aa10d4a46a2a34bb3a79353a6eb7af4000adec56f5a80015be0adefd6f7ab7bb5bdcadedd6f6ab7b35bc1ade056eeeb77b5bbcaddbd6efeb77d4000abf9d5e0eaa4d5420ab7c55782a5215150aa9f550e680015bb1a95450002b7615169add75,0x4aaaa2d75c36ae1ad70eeb8754f29a74f52ec280015c3cae1bd5fdaaf0d553faa1d55beeabc752a9a8b5554a6a8475293a8a9d2ebe9e514e9da00057066b8315c24ae11d708a80015c1ea0005706ab7fd5bfdadfe56feeb7df5bfaadfcd6fe2b7ef5bf6adfad5fd6af0b5544aa1fd0002b7e356faa00056fc2abc552aea8b7d54a2a8455292a8a95,0x2f5697a94be7a5f352f2280014000a00052fc680014000a00052fb280014bdfa5ef52e9a974b4000a5ce52e8a97434000a5cd52eaa97534000a5d252e8e80014b9fa5d452e9e97714bb7a00052eea80014000a00052ee6b8915c47ae21d711ab8835c42a00057116b88957f7abc3d54aaa84956fcaaf254a52a2a94000ae1cd550280015c38aa1dd,0x5796a5635172aa95d5096a52b5155a79553a7e80015c5eae2ed7196b8c95c63ae3157186b8c15c5fa00052f4a97cb4be4a5e7d2f3a80014bc3a00052eee80014bbfa5f852fbe97af4bd6a5f4d2fa297954bc9a5f5d2faa80014bd1a5e852f8e97c54000a5e152f0697bb4bdca00052f2e97b34bd8a00052ef697c34be0a00052f6e97b54beea5f6d,0x7c26be0d5f05af8157c06bdfd5efdaf4fd783e80015efcaf7bd0002bdf74000af40d0002bdf54000af10d0002bdf34000aeb0d0002bdf14000ae6b57bdab8fb5c7cae3dd71eab8f35c78ae3bd0002b8e757f9a000571caaf135548aa21d5bfaabcd52b2a8b9d54b2a84d5296a8ab50002b8ed5c71ae3ad71d29e574ea0abfc55e22aa8f5442ab7ed,0x7c5abe2b5f13af8957c42be1f5f0daf8653b069d814ebda75e53aee9d754eb9a75c500029d674eb2a758d3ac29d5f4000a75653aae9d554000a754d3aa29d4f4000a75353a969d494ea3a7515000280014000a762d00029d894000a000500029d874000a7615000280014000a75fd00029d7d4000a000500029d6f4000a75b500029d434000af855,0x733eb99d5ccdae6650002b9915cd7ae63d0002b98d5ccba00057326b9894f49a7a453d169e894f43a7a153d069e814f3da79e53cee9e754f39a79c53cde9e6d4f35a79a500029e9b4000a7a6500029e974000a7a5500029e8f4000a7a3500029e7f4000a79f53cce9e654f31a79853cbe9e5d4f2da79657aaabe2f5e39af8a57646be235d0daf875,0x7556bac55d54a0005754ebab14000aeab57546ba175d0aae84d7422ba0f5d06ae82d7412ba075d02a00055feeaf195534aa17d5c02abd3529ea8afd54c2a8575cffa00057432b9fd4000ae7ed4a6aa2b75d01a00050002b9e75d00abfd55e2eaa67542eab7fd57a2a53b515eaa97d50aaa533515aa0005732ab98b5cd5ae6a5734eb9a55cd1ae685,0x786680015e15af115785280015e16af06d763ebb1d5d8daec65762ebb155d89a00050002bb114000abfed5e3aaa715433ab81557aea5455163aec050002bb215d7fa000575faaa65542da94e54576baef5d82aec0d5ff2af1b5537aa1955c06abd552a1a8b1554c6a859529ba8ae50002baaf5d52aeb05757ebabd5d5daeae5756ebab55d59a0005,0x5e46ae0b55eeaa9cd50d2a5475164a000579f6bcf15e80a000579e6bcff5e7ea000579eebd055e7aa000579f2bcef5e37af1b578d6bc6957ffabc8578ca80015e38af18d0002bc615704aaf6d54daa86352a0a8b0d78bebc675e12af0c55ffaaf1f5703aaf6554d6a861529fa8b050002bc2f5e0ea0005784e80015e1ba00057846bc354000af085,0x463e80015188a0005461ea2e94000a0005459ea2cd4000a8abd0002c58b62c4b16158b06c57f62beb15e58aeec57362b8a00058acec56f62c6b132d0002c56b62c3b09ad0002c56962c0b06358af6c0c162bab004d8adac5654000af5457a82bd4f5ea6af52d7a8e80015ea9af5150002bd435801abc955c1aabdf553aaa1ad4a92a2cb5ea4ac005,0x8b82c05f4000b16d58b7ac5d162e7b172d8b92c5c562e1b16fd8b76c5b962dba8cc5465ea3295193a8c954646a31d518da8c65462ea3155189a8c354616a3095183a8c154606a301517fa8bf545f6a2f9517ba8bd545e6a2f15177a8bb545d68001519ca0005466e80014000a0005466a80015199a0005000280015196a0005465680015190a0005,0x8fdac7f152d7a96b54b4ea5a552d1a96850002a59752caa964d4b22a58f52c4a961d4b0aa58352c0a95fd4afaa57b4000a96dd0002a5b54000a96cd0002a5b14000a96ad0002a5a94000a967d0002a59d4000a9635000280014000a962d4af2a57752baa95cd4ae2a56f52b6a95ad4ad2a56752a6a00054a96c4ff62e9b0c258b9ac1e762e3b0415,0x5162a8af5456aa2ad5152a8a75452aa28d513aa89b544caa25d512aa8935448aa23d511a80015445a000551b28001546ba000551aa80015469a0005519a80015465a00055182a8bf4000aa285513e80015444a00050002a86f5436aa13d0002c7bd5ff4b202d9012c8056401b1ffd8ffa800163f7b1fe5901ac79d6403b1bf59002c6574000a0005,0x2aae54000aab8d0002aadb4000aab65559e80015566aaaed5572aab7555aaaacd556280015557aaab5554eaaa55551aaa85553eaa9d4000aaa5d555680015554aaa555526aa794000aa9dd8fa6c8236394b20758d32c8196409b0bb59022c821640fb206d902ec8156407aa345519ea8c95463aa3155186a8bd545daa2e5516ea8b55459a0005,0x9356c9a94000b268d9342ac0f5606ab01d580aac035600aaffd57faabf755faaafcd57e2abef55f6aafad57d2abe755f2a0005582680015608a00055816ac094000aafed57f2800155f1aaf85579e800164beb25ed0002c97164bca0005927ec97764bab25cd0002aadd556baab5555a6aad14000aab1d0002aac1555faaaf50002aae94000aab9d,0x5e5aaf2b4000abd655eae800157a8abd3d0002af41579fa00055e52af27578aa00050002c9b964e1b2705937ec9bd64dda00055c8e80015722ab90d0002ae41571dab8e55c6eae35571fa00055c7aae335718a00055c4aae235710ab8bd0002ae2d4000ab87d5c3a8001570bab8555c26ae114000a00050002ae0f64afb26b59242c9a764d2b06fd,0x7ffe8001600aaffd57fe680015ffdaff8d0002bff95ff0a00057feebfdf581ba0005606ab0335818ac0bd0002b02d5815ac0a5604eb0255811ac085603e8001580eac06d6032b017580aac04d6022b00f5806ac02d6012b0074000ac0159396c9c964e3b27155eaaaf5357a6abd2d5e92af4757a2abd0d5e7aaf3b579cabcdd5e6aaf335798abcbd,0x82e2c1014000a000581dec0ed4000a000581ce80016081b039581d6c0e94000b02b5817ec0bd605db02e5816e80016061b02c5815ec0b54000b02cd8156c05b602cb015d80aac0536028a0005809680016021a000580bac0416024b011d808abfe74000afff57fca80015ff8a0005801680015ff7b0025800e80015ff6b0015800680015ff5b0005,0x8602c2eb4000b0bfd85e280016183b0bbd85cec2f3617aa000585eec2e94000b097d84a6c2696133b099584c6c2614000b09b584aec255612eb096d0002c2596128b078d0002c1d360e8a0005839ec1cd60e5a00058386800160f2b07058392c1c760e2a000582fec1734000b0625830ec18560c1b06050002c18f60bbb05d582fac17b4000b05e5,0x8d06c681633fa00058c96c63d4000b194d8ca2c64f6326b19250002c6596320b18fd0002c647631db19158c86c4fb627cb13dd89eac4f36275a000589fac4e96278b13bd89da8001625da00050002c4af6264a0005895ac4c74000b12ad000280016254b12f50002c4cd6259b12c50002c4b96251a0005896ec4a14000b12d5893ec3056181b0bf5,0x924ec91563e7b1f358f96c7c963e0a00058fa2c7bf63e3b1f158f86800163cab1e1d8f36c79963cbb1e4d0002c79f63c5b1e250002c79163c2b1e3d8f1ac7256391b1c858e3ec7194000b1c9d8e2ec71d638da00058dd28001637bb1bd58de68001637fb1bb58dd6c6f14000b1bbd8dcec6954000b1a2d8d12c687633cb1a158cfa8001634bb19ed,0x612630ad18558c2946146308d184e8c26c6112308f18488000461163097184c8c6c4612a31af091a8370c15960ac9055c82adc15820abf055982ac4158a0ac3055e82aec156a0ac704ee8264c136609d705059256d92b2c9534000b257592a2c95764aaa0005927a80014000b24ed923680014000b24650002c9416492b248d00028001648ba0005,0x6212310718828c40c61da3101187f8c3f461f630eb18748c3e461ee30f518738c394000230f318718000461e230e118e08c3bc637e307b18de836fc61be30dd185f8c35c61aa30cf18668c36c61b230d318688c2dc617230cb186480004616630c3185e8c2ec000230b518628c31c637230c118db8c6d41b8e307518588c2bc6142309f18548c29c,0x62f6317918bb8c5ac62d2000118ba8c59c62ca31d118b98c73c1b92316318b08c51462be315d18ad8c56462ae315518a98c5446286314118a78c5346296313f00008c524627a313b18e58c51c639215f906e08c4e4626e313518998c4746236313118978c4b46256312918938c464622e312518918c484622a311300008c47c6222310f18868c42c,0x19020dd906f1837341b9e0dd106e9837741372000106d7836f41b760d5b06d982ff41b6e0dc5064f836c417760db90693836d4189a07a306e58c21c610a308318408c1fc60fa3079183b8c1cc60e2306f18368c15c2e5e306b18348c16460ce306518318c18460be305d182d8c5c4631e318d18c58c624630e318518c18c60462fe317d18b78c5b4,0x63c631e118eb8c75463ce31e518ef8c77463da31d318f78c7c4643a23ed09158c86c6432321719098a4ec2be2321119078c83434ea1a710d338697c34c600010d2e869bc00021a650d3986984340e1a590d2b86924348e1a510d278691434861a550d298693434961a6904ab8000434da1a5b06b98378418460dd7065f8376c17c20dd506a28377c,0x137e09cd04e5826f4137609d104e78271c138a07a104678244c129209c304e482824131209ab00008276414060a0100008281c140a14b70a1585ccc2e6216790b2a8700c38021bff0dfe86fec37f21bf70dfa86fcc37e21bef0df686fac147e1be90df386f9437c61be10def86f7437b61bd90deb86f5437a61bd10de786f3463d631e918ed8c764,0xf8a07c303ee81f6c0f5a07ab03f081f7c101a080b03ea81f4c0ff207f703de81eec100a080303f481f9c0f3a079b03c681e2c0f2a079303c481e1c0f32079703c881e3c0f3e0811040781f640fae07fd03fd81f040f7e0809040381fb40fd607a5052c8295c14920a4705288293c148a0a43052a8294c149a0a4b052d8297c14c209d504e982704,0x2094d04b0825441296095300008253c12ce094704bf825f41316099504c0826440002099704c28260c131a090d00008261c1192094304d282684131e09ad04da8268c1362000104db8269c135e000104d48243c1196094503e881f3c0fea07f303e481f1c0f7207b703d481e9c0f6207af040081ffc0f9a07cb03f881fbc0f6a07b303f281f8c,0x2076d03b5800040e62072f000081de40eee000103ae81d6c0e22070f038081bfc0e120707037e81bec0e1a070b038281c0c0e2e0001038a828bc145a0a1f050e8289c144a0a1b050c828ac14520a230510828f4146a0001051c8290414660a3b051b8285c0e260a3104b9825c412be095d04b5825a412b6095904b7825b412ca0963038c82554,0x11ca091504928247c1232092300008249c12360917048e8244412420ae1041482b7c0e8a074303b481d9c0e7a073b039681cac0e3a071b039281c8c0eea077303a081cfc0eca0763039481c9c0eb20757039c81cdc0ea2074f039081c7c0eaa075303c281e0c0e9a074b03b881dbc0e6a073303be81dec0ec2075f000081e040efe000103a481d1c,0x1136086d043582294114608910447820d4106608230416820ac103e083104178209c10a2084f0420820fc10920847041e820ec109a084b04228210c103a081b04fb827d413ca09e304f6827ac13c209df04f9827c413d209e704f78214c11a608d104708237411ae08e30000823a411b208d504738236c119a08df056d8209415b20ad5041082b4c,0x16660b4b05a182c4c168e0a690000829c414d6000105368299c14de0001055782aac00020aad055482a5c153e0aa1000082a6415460001054e82a541536087d043d82264112e08750439821a410ce0859042b8218410be08a1044f821e410ee089504498219410c6088d0445821c410de088504418217410b608890443822a4114e0881043f82274,0x1bfe0e0106bb8309c1bee0001070182efc190a0e07070b838541c320e1b07068383c18660e0b0000838441a6a0c8f06f8837cc1bea0de906f3837b41bd60def06b783564183e0bfb065d8327417ba0bb906a08349418fa0c4b06f28ca1c650a3281193c8c9dc64e6326f19358c9a464ca3261192e8c96c64b20b3705ad82cbc163e0b0f058b82d9c,0x20d21069c834dc00020d1506968302c00020d190699832a400020d13069582f3400020d170698800041a220d29068f834ec1a460c97064a830b419120c8d064582fa4190e0c930000831e419220c83063a8326418ee0c7f063d8317c18ba000106228314c1806000106248315c18aa0c5105e28316c18b20c4f0623831841bf20dfd06fd83824,0x195e0cad06528301c19460cab06538328419360cb105fa82fcc17de0bed05f582f9c17ca0be305eb82fdc17b20bdf05ed80004176a0bd305e880004175a0bc305e08000417620bcb05e48000417660bcf000082ebc178e000105d482ef417560bd505db8354c1aa20c3706a5833341a9e0bf106a48351c1a9a0d55069e8350c1a7e0d1b069783474,0x486024d0082800040482024b005a835ec1afe0d7906ba8360c1b020d7d06c2835ac1ae20d6d06b0835941abe0d6706b1835741aae0d69061d830e4186a0c2f06158305c182a0c290612830f418320c21060e8306c18220c0f060483004181a0c0505ff82fe418260cd10667830c4198a0cb506618330419960cb306648331c19a60cb7065e832e4,0x8e00850041801f400f6007100378017400b6008900438020400fe007500398018400be0001004580104007e003d001d80004007200370000800d40066004500008010c03c2026900ca8098c0256025d006f8095c04360109005e8080c04ce026501308097c04b60259012a8094c0002023f012480004048e025100db80004048a024f00be80004,0xb560417025880ecc095a0379025580cec095202fb025280e5c064e02dd021f810a4093a00c302578129c000200010241812440002048d024d80ffc0002048b024c80e4c00020489024b80d5c00020487024a80c7c00020485024980b64000204810247801e400ee006d0035801a400ce006500318016400ae0055002980144009e004d002580124,0xd360699034b81a540d26062703378180c0cd604d1033480d840c7e06310333806140cda0001032d8198c0cca061703308197c0cba054d02e2814740b8604e702df816f40a16039d02dd80b840aca055302dc804440b82000102d0816bc000205a902db814d4000205a702da8141c000205a502d98132c000205a302d8800040b3e05ad000081674,0x18200bb005c803740002009b004b802bc015a00ab00548029c014a00a300508027c013a00b30000802dc013201dd01128064404460127010f8036c043a022100e58057c0002020f0100800040416021700d9800040412021500bc80004040e0213008080004040a02110058808340d4606050350814ec0d3e04030341819d40d3a01d1000081a44,0x302019300b2805bc0002016d00ae8000402ce017700ba8000402c6017300008058402e2000100b4805ec0002017f00b58048c0242011f008e8046c0232011700868042c022a011300928043c025200010077803ac01fe00fd007d803e401ee00f50079803c4020600010083803b401ae00d5006980344019e00cd006580324018e00c5005f80364,0x98e055b02ab815540826045301d78113c06ea044d019b8112c05ee000102218112408a20447022280004084e0431021d80fec0002042d021c80e3c0002042b021b80d4c086a031b021980b54085e000100ec8073403ae01d500e98076c039e01df0000806ac034a01b100008069c035e01ad00da80004037201a900c68062c0312018700c78060c,0x59602c9000080ad4058e02c5000080b5c057a0001016080ab4000202db015f81a2c0d1206870342800040ce6067f033e819ec0cf2067703118195c0c020653032880d7c0caa00010327819340002062f031c818ec0c260637031a818cc0a920571028c815bc09c6056d02b580e6c0ad20567029c80acc0002055102ac815840a62055f028181574,0x6b6037301b180ddc0002034501a080d44069e034d01a580d24068e035501a180d6406660331019780cb406560325019180cd406520339000080c2c06320317018a80c4c0622031d0187800040642030d017980bc405de02ed017580ba405ce02e5016f80bd405c602f9015880004058602af000080aec05a602d1000080ae4059e02cd000080adc,0x99204b702668103c081a040b02048101c08220405020a8000407e203e1000080fa407f2000101f380fdc000203e501fa8000407c603f3000080ff407d6000101f780f7c0002040101f680eac075203a301d380e64074203a501d680e7c0762000101c180dfc071a038b01c480e1c070a039101c080e5406e2036f01b680dac06ba036901b380d94,0xbf60001030a8181c0002060b02fc800040c32060902a28150c0a82053f02a3814f40a96000102948148c0a5e052d02958149c0a660525029b814540a26051102878145c0a1a051b0000813d40a0204ff027e813ec0a0a04f900008142409ee04df026e8136c09b204d702678135409c204d3027280004097604b502628130c098204bf025e812e4,0x6532329319488caac654a329f19878cc3465e632f119858cc24660e330519818cc0465fe32fd19778cbb465d632fb197c8cbdc2d4232e9197a8cb9c65ca32e319708cb7c65ba32c719628cb6c65b232d7196a8cb4c65a232c319608cb3c659a32cb195f8caf4659232bb195c8187c0c3a0621030d818940002061102ff800040c1e05fd000081834,0x40f2207710258802c3fde205510298813c408e2045102188104407e203d101d880e4406e203508cf80004409a20491019880c4405e334f19a58cd246676333919a18cd04666e334719a28ccfc667a333519998cd4466a6114f19a689b7c4d4a331319478cadc656a32b319588cabc655a32a919538ca8c65423297194a8ca2c6512328d194e8ca6c,0x221600010883844142222111308848443c66de336d19b58cda466ce338f19c68ce2c6712338719c28ce0c6702337319b88cdfc66fa336319b28cd8466f6337919bb8cd7466b6335919af8cdd466ae33551056882ac415220a710528828c4142209f104e8826c41322097104a8824c4122208f10468822c4112208710428820c4102207f103e881ec,0x1daa0edf076e83b4c1da20ee3077083b6c1db20eeb077483d5c1eaa0f1f078e83d0c1e820f4f07a683ccc1e620001077783bb424a2124f0920848fc24921247091e849342496124509218495424a61259092b84534229611390000844b4226e114508a18449c22921147089f844f422520f070895844cc2262112f089d84504226a10e5000084434,0x1f2a12ed09758436421ae10e700008437c21da10dd00008000421c610cf08748436c21d610d50000800041e2e0f15079d83ce41e1e0f0d078183c041de60ef1077d83be41e8e0f45078983c441e6e0f35077f83bf41e560f29078583c241e460f21077b83bd41e4e0f2507a983d441e360f19079f83cf41e0a0f4b07a483cbc1e5a0ee7077283b5c,0x233211bd08dd846a4234e11b508d983f14237211b708d7846b42356119b08ce846c4234611a108d2847a424da126b092e8496c24ca126309348499c24c2125f093e849ec24de1271093a849cc24ee0fbf093c84bec2576103107d084be42532102107c884b9c23c61165091c848dc23ea0001091d848cc245e00010918840b41f3a12f508c484094,0x1f9a0fcb080a8404c1fba000107ed840041ffe1005080183f441f9e0ff507f98403420160fe907f383f241f8e0fe107ef83fc41fde0fe507f184044201e000107ec83f5c00020ffd07fd800042012100707f683fac1f3e0f8f07cc83e5c1f520fa707cd83e4c1f4a0fa307de83eec1f5a0fab07da83ecc1f860fb907db83ec41f5e0fc107c683e2c,0x211a108b08178407c20521027080e8406c20561023081a840cc209a104b081e840ec208a1043081c840dc209210470820840fc20321017096d84b64259212c7096884b3c25aa12d3096684b2c25ae12c3096084b142426121109008000423be11ff09058482422c2120f09068481c240a1185090a8480c23f211f708fd8413c1faa0fd307fc83fdc,0x2302000108cb8460c23161357000084ae4257e11ef000084af4256e116d08ca84a7400021297094f84a540002129b0948845a425261191083c841dc212a10930838841bc20ca1063082a8414c20ba105b084e8426c20ea107308488423c20c2105f08448421c20da106b0840841fc20b2105708428420c214a10a3083e841ec2132109708508427c,0x683e00011a178d074684e34211a0d8d064682e00011a168d0546826342b1a088a4ac2cae35670b8a8d0a46aca356319fc84d1c23e211dd08ec8475423da11db08f58475c23e611e108f28474423ce11d308ad8458c22ba000108b78457c22ce134309b384a9425560001095684a9c000212a9095184d6c2676133908b5845f4230e119308bf80004,0x6af6345b1a3e8d1ec68da346b1a3a8d1cc68ba34791a3b8d1c468de34551a278d14c68a234671a328d12c000234691a2b8d164689a34611a318d5bc6ae6345f1ab88597c2e5617290b8f85c742e4e17250b8c85c5c2b8a17230b9085c6c2e2617110ab38564c684634311a248d11c688a34431a208d0fc687a343b00008d094687234371a1a8d0cc,0x69f635870b5e8596c698e34e71a728d38c69c234cb1a648d37c69ba34db1a6c8d35c69aa34c51a618d34c69a234cf1a608d2fc697a34cd1a5d8d2e4691e34a31a5b8d2d4696634b11a578d2b4692600011a488d2ac695234a71a528d234000234a11a458d27c693a349b1a438d214691234991a418d25c6902347f14978d5fc692a357d1abb85964,0x67fa33fb19ef8cf8c67ee33f519f98cfb467d633e919f38cf9467c233dd1a938d5146a8635411a9f8d4f46a7635391a9b8d4d46a6635251a918d4c46a5e352d1a908d47c6a56351d1a8d8d63c6a52358d1a8c8d45c69f235151a898d4446a1e350d1a858d4246a0e34f700008d41469ea35031a808d3fc69e634f11a778d3b469fa34eb1a748d624,0x4cbe265d132d899644cae265512ed898344c1e25bb13048980c4c0200011303898144bfe25fd1acd8d6546b2635971ac88d6746b32293114968a46c52322917148a8a44c5222292914938a49452462921148f8a4742b86165d0b24859142c86156b0b238594c2c9a16510b258593c2c82340f1a068d02c681234071a028d00c680233ff19f88cfbc,0x6cae36551b208d96c6cb236531b288d8dc6c7636391b258d9246c66363d1b1f8d8d46c8a36471b9b8d90c6e6a36311b178d8b46c5636291b138d8946c4636211b0f8d8746c36360f1b068d84c6c22360b00008d8646c1236071b028d85c6c0637331b0a8dcc46e5e35ed133c899dc4cea26731338899bc4cda266b13348999c4cca16fd133189984,0x6d8e36d51b698db446d8a36c31b608db3c6d7e36bd1ba18db346e8216d31b5d8dae46d6e36b51b4f8da746d6636b11b578dab46d5636a91b4d8da646d4e36a51b518da5c6d2a36a11b498da446d1e368d1b388d9bc6d0e36851b3f8d9f46d1636891b418da046cd236651b338d9d46cf636791b308d9b46cd636631b398d9dc6cbe365d1b278d934,0x6eae37551b008d7fc6bfa35fb1afc8d7dc6bca35e31afa8d7cc6be235ef1aeb85d646bd635e91af38d7846bbe35dd1aed8d7646baa35d31b7d8dc646e2e37151b898dc446e1e370d1b858dc246e0e36f91b7b8dc146e0637011b7a8dbcc6de236ef1b7f8dbb46dd637491b7e8dd1c6dd236e71b658db946dc636e11b6f8db746db636d91b6b8db24,0x6f2e37891bc38de146f2637911bc78de6c6f2a37c51be18ddcc6eea28ef1bb8884fc427a213b109c884dc426a21331098884bc425a212b10908847c423a211b105e884a4424e2125109180004402620ef0ffb8839441c620e10000883b441ce20bb107587f3c41d237691bb38dd942eba175b0b518535c289616631bac8dd4c6e9a37511ba78dd2c,0x704238111c078e10c708238271c1f8e0ec7072383700008ad04567e2b3d159d8ace4566e2b3515998acc4565e2b2d15958aca4564e2b2515918ac84563e2b1d158d8ac1456062b01157f8abec55ea2af315788000455f22af715778abb46fae37cf1be58df246f9a37c71be98df546fa237ab1bd48de9c6f4a378d1bc58de8c6f42379f1bce8de64,0x4db22687137b89bd44de626f11377897844d8226c5136189afc4d6626b1135789ab44d5626a9135389a8c4d421595000089af44d6a2685135d89ae44c7a26b71c348e18470be38531c288e16c70b2384f1c2e8e15c70aa384d1c258e19470ce38631c178e0b4700e38051c158e0a4704a38231c0f8e074702a38131c018e0046ffe380d1c058e024,0x279e13fd09fd80004276a13b30b3a859cc2cce16650b37859b42cc216710b35859a42cee167d0b3d856442b1e157f0abe856342b1615790abb855ec2aea15870ac28560c282a15690ab8855bc2ada15810ac4855cc70fe38811c3e8e1ec4e1a270b138489c1c4e0a2703138089bfc4dfa26fb137c89bb44dd626e9137389b944dc626e1136e89b6c,0x2aba156309f084f7c280a140309ec84f5c279213c709dc84edc278213bf0a088503c27ba13db0a0084ffc278a13c309fa84fcc27aa13d309f684fac277a13bb09f884fbc2832141709f284f8c2812140709e684f2c282613f909fb84eb42756139d09cd84e942746139909cb84ea4274e13a109cf84ec4275e141d0a0d84fa427ce140d0a0584f44,0x2b42159f0a31856c42b5e15ad0000856cc2b3215970acd85bd42de617050b8185c3c2e1a17010b7f85c242e0e170b0b7c85bdc2df6145d0b6185aa4000216f10b75800042dd216ef0b6c85cf4297e14330b9d852ec285e17370aff857f42b7a00010b02857dc2c0215f50afd8580c298614370b76800042e8200010ab08557c0002155b0aac85594,0x28e614710a338519428de146d0a59852c4291e148d0a55852a428f614790a4b8525428fe147d0a498524428d614690a4f85274295e14ad0a4585224294e14a50a3b851d40002149b0a4c850fc287a14310a1d850e4285a14470a22850d4288614410a2d85164289e144d0a2b85154289214610a298514428be14290add856e42b5615a90adb856d4,0x2a1615090a8f8547429ee14f50a91854842a8615410a8d854642a6e15350a83854142a5615290a6785334297a14c70a62852e4299614c90a608534c29a214eb0a748536c29b214e30a708535429ce14e50a6f85374296a15e30af0857442b9e15dd0aed8572c2b9215cd0ae38575c2baa15d30aec857042b7e14ed0a4385214294614a10a4185204,0x712e38951c498e284713e389d1c588e28c2f4e17890bbc85e042d7200010b6385aec2d8216bf0b5385a74000216ad0b4f800042d4a169b0bcd85adc2f3200010bbe85b142d5616cf000085b6c2da216d70b6a85e2c2f1a178f0a8b854542a6615310a87854342a0615010a79853c429f614f90a9d854e42a2615110a97854b429fe14fd0a9385494,0x7af63d731ebe88fd47c023dff17508ba7c5d3a2e9b174c8ba5c5d2a2e9317488ba3c5d1a2e8b17448ba1c5d0a2e8317408b9fc5cfa2e7b173c8b9dc5cc62e61172e8b95c5caa2e5317288b93c00022e5b172c8b9345c9638e11c6c8e34471aa38cf1c6b8e34c719a38dd1c6f8e36c713638991c5c8e2dc716a38b31c578e2b4715638a91c538e294,0x7bb23dd717b48f85c7baa3dd31e268f7447b9e3dcd1ee58f7147b8e3dc91ee18f7047b7e3dbd16978f8447c1e3dbb1edc8eb347b663db11ed58f6a47b6e3db51ed78f6b47b323d9b1ed38f6547b423d9f1ece8f65c7b463da5149c8f8247c0e3d931ec88f60c7b023d8b1ec48e71c7b1e3d8d1ec38f6147ae23d6f1eba8f5fc7ad63d771ebc8f5b4,0x342a1a2b0d1480004341e1a1f0d0e80004342e1a2f0d168000434261a270d128000434361a0d0dd180004375e1bcb0de480004375a1bc70de28000437561bc30de08000437521bbf0dde80004374e1bbb0ddc80004374a1bb70dda86ec47ad23d671eb28f58c7ac23d5f1ead8f5647aae3d5d1e968f7ac7bd23de71ef28f78c7bc23ddf1eee8f76c,0x38ba1c5b0e2c8715c38aa1c530e28870f438761c390e1b870d438661c310e17870b438561c4f0e268712c35da1c490c188711438861c410e1f8000438221c290e1380004381e1c250e1180004381a1c210e0f8000438161c1d0e0d8000438121c190e0b80004380e1c1500008704c380a1a0b0d048000434321a330d188000434221a230d1080004,0x301218070c0a8604c301a180b0c028600c0002182d0c1586074303618250c11860bc305218270c108607c2ff218450c21860d43066183d0c1d86124308e18410c1f860e4306e17fb0c0c86b84356600010d9586d0c368200010d9186ccc366200010d9386cec367200010d9486cfc367a00010d9286cdc366a1b2d0bfb86cbc302e1c630e308717c,0x394218c70e4e8726c39321c970000871c4390a1c830000871bc39021c7f0000871b438fa1c7b0000871ac38f200010e34871dc00021c670e3a8000438e61c650c2c8615c30ea18730c288613c310a18830c2e8616c30f218770c3e861ec30aa18530c38861bc3102187f0c348619c309a184b0c308617c30da186b0c328618c3022180f0c0085ffc,0x316618b10c5f862f4316e18b50c478636c31b218df0c6e8634c31a218cb0c648635c31aa18cf0c6686244315e1ae30d5b8000436b61b730db88000436ae1b6b0db486d8c36c200010dac86dbc36da1b670db286d74311a1b5f0c56872ec39721cb70e5a872cc39621caf0e4a8724c39221c8f0e468722c39121c870e56872ac39521ca70e528728c,0x35921cdd0e6d8736400021cc30e668732c00021cc10e6480004397e1cc7000087314397a191b0c8c8642c3212190f0c86863bc31da18f30c788639c31ca19130c888645c322a19070c82863ac31d218ff0c7e8640c320218f70c7a8638c31c218fb0c7c8629c314a18ab0c548627c313a18970c4a8628c3142189b0c4c8630c318218c50c5d862e4,0x3302198b0cc48000432f219770cba865fc32fa00010cb8865bc32da00010cb386594000219690cb18658432be195d0cab8655432a619510cad86564329e194d0ca586524328e19450ca0864fc35ca1b7d000086dfc371a1b8b0dc486e1c370a1b830dc0864f439de1ced0e6b8735439d61cd30e68873a439ce1ce50d788738c399e196b00008737c,0x337a19bb0cdc866dc336a19b30cd8866bc335a19ab0cd48669c334a19a30cd08667c333a199b0ccc8665433261ae90d5f86e6c37321b970dca86e4c37221b8f0cc8874843a3e1d1d0e8d874643a2e1d150e89874443a1e19bf0e85874243a0e1d050d7a8000439f61d030000873e43a0200010e7b873fc00021cfd0e7a8663c331a19870cc28660c,0x3b7e1dbd0edd876e43b6e00010ed9876d43b621daf0ed6876ac3b521da70ed28768c3b421d9f0ecc876743b261d950ec6876443ad21d6b0ead8757400021af30d7386bbc35d61abb0d638000435821acb0d5c86ad4357a1acd0d6180004358a1ab10cf18678433be19dd0ced8676433ae19d50ce986744339e19cd0ce586724338e19c50ce186704,0x722e39031c838e42471fa38ff00008e42c720239050000878dc3c621e350f19878bc3c5a1e2b0f128789c3c3e1e230f0e8786c3c321e170eff878343c2a1e130f088783c3c0e1e090f00878143bfa1dfb0efc877dc3bea1df30ef8877bc3b921ddd0ef6877ac3bd21de70ef28778c3bc21ddf0eeb8776c3ba21dd30ee58773c3b8e1dc50ee187704,0x73e239ef17b08e71447e239eb1cf48a4d447de394f1ca68e52c729239471ca28e50c7282393f1c9e8e4cc726239371c9a8e4bc7276392b1c9c8e4a4725a39871cc28e60c7302397f1cbe8e5ec72f239771cba8e5c472e639691cb38e5b472d639651cb18e5bc72b600011caf8e56472c239551ca98000472ba39571ca88e44c722a390f1c888e434,0x752a3a931d488ea3c751a3a8b1d428ea1c75063a811d448e9e474fa3a7f1d3a8e9cc00023a7b1d3b8e9c4747e3a451d208e90c747a3a471d1980004746e3a2b1d1c8e8b4745e00011d1d8e8c4746a39f716be8e7d473ca39e300008e72c73c239df00008e72473ba39db1cec8e75c73aa39d31ce88e734738239cf1ce188f5447f2000111fb88fcc,0x76563b331d7c8ebdc75e63af11d868ec2c761e3b091d838eb2c75b23aed1d758eba475ce3ae51d718eb8475be3add1d6d8eb54758e3ad71d648eb4c759e3ad114a28a50c528228f3149e80004527e29371d378e9b474d63a691d338e99474c63a611d298e94474be3a5d1d268e95c74aa3a4f1d2c8e92474b63a4b1d508ea7c753a3a9b1d4c8ea5c,0x77563ba91dcd8ee6477463ba11dc78ee34774e3ba51dcf8ee74770e3b851dcb8ee5477023b891dc58ee0c77223b931e048f03478323c171e0a8f04c78223c0f1e058f01c780a3c031e008effc765a3b3d1da48ed0c76ae3b5b1dac8ed1c768a3b511da78ed04767e3b551da98ed3476963b311dae8ecbc766a3b391d9b8ec94764e3b2900008ecec,0x5a622d2d1dbf8edf476e63b711dbd8ede476ee3b751db58eda476ce3b6f1db68ed8c76c23b5f1db28ef9c77e23beb1df48eff477f63bf91dfb8efd477e63be31df78efb477ca3be11def8ef7477b63c391e208f0fc787a3bc51dec8ef5c77763bb91de88ef3c77923bc71dea8ef4c779a3bcb1dd88eecc77863bc11dd68eedc776a3baf1dde8eefc,0x792a3c931e4b8f37479b63cc11e5f8f35479a63ccd1e658f36479ae3cd11e678f2dc79723cc91e638f2cc797a3cbb1e5a8f30c798a3ced1e758f3a479ce3ce51e718f38479be3c871e468f23c79163c851e448f24478f63c7f1e408f1d478ee00011e418f1e478fa3c5d1e2d8f16478ae3c551e298f12c78923c4f1e288f11c5a6a2d33169580004,0x8a6a453316bd9064c8a62452f2296914ac8a52451f228e9149c8a4a4523228d914848a3245171e8a8f44c7a523d271e8c8f45c7a4a3d231e908f47c7a223d1d1e8d8f43c7a163d0d1e848f41c7a7a3d3b1e9c8f4dc7a6a3d331e978f4c47a562dd717b3800045ed62f6517b18f26c79463ca11e578f2b479563ca91e538f29479623c991e4f8f274,0x3fba1fdb000087f243fc21fdf0fec87f5c3f9a1fcb0fe88815c40ea207300008816c40e2206f00008816440da206b10348819c40ca2063102f881748a16450f2286914248a0e45152289914148a22450322809158c8ac228ff21649157c8aba455b22ac9155c8aaa455322a3915148a86455122a7915348a964541229f915248a7a453b229c914dc,0x42be215d00008852442b6215900008851c42ae215500008854c428a000110a88850c0002214f10a0883ec00022105108c8845c000220fd1085884240002210110888843c00022103108a8844c000220ff10868000441f2210710688833c419a20cb10648831c418a20c31060882fc416e20b51059882c4415e20b90ff287f8c3faa1fd3000087f1c,0x43a221cf10e68872c000221c910e28870c438221b710dd886e4436621bf10de8868c436a21af10d2886ac435221a710d680004432621a110cf800044322219d10cd80004431e219900008865c431a000110ca8862c4312218710c28860c4302217f10be885ec42ce216510bc885d442e6217110b7885b442d6216900008853442c6216100008852c,0x3d7e1ebd0f5b87ad43d661eb10f5d87ae43d5e1ead0f5587aa43d4e1ea10f4f87a7440122007000087fb4400a2003100087ffc3ffa1ffb0ffc87b643fea1ff30ff887a94441a220b11048881c43c221df10ee8876c440a22031100887fc43fa21fb10fc87c0c43ea21f310f8887bc43da21eb10f48879c43ca21e310ec8875c000221c710ea8874c,0x4442221f000088844443a221b110c8885c442a000111098883c3e461f210f9587ca43e4e1f250f8d87c643e2e1f150f8f87c743e1e1f0d0f8587c243e261f110f8387c143dfe1efd0f7d87be43e021ef70f7a87bcc3de21eeb0f7487b9c3dca1eef0f7687b8c3dc21edf0f6e87b6c3da61ed10f6787b343dae1ed50f6587b243d8e1ec50f6187b04,0x3eda1f670fb287d8c3ec21f5f0fae87d6c3eb21f570faa87d3c3e9a1f530fa887d2c3e921f470fa287d0c3e821f3f0f9c87cdc3e6a2025101188084403e201d100d88064402e20150fb888044401e200d0f9e8894c44a222431127888f4444a22231120888fc449a224b0fcd888e4449222471122888ac445222271118888bc445a2237111a888cc,0x2226111378000444be226d00008897444d60001112d889a400022267112c8000444ca225700008898c44aa1fc30fe087eec3f721fbf0fde87ecc3f621fb70fda87ebc3f5a1fa70fd287eac3f521fa30fd087e7c3f3a1f970fca87e643f261f910fc787e343f161f890fc187e043f0e1f850fbf87df43ef61f790fbb87dd43ee61f6b0fb487dbc,0x474e243f121c88e4c4876241d121a890cc486e242f11af890c4480223ff11fe88fec48362419120b89054482624111207890344816240912038900c480a45b322d8916bc8b5a45ab22d49169c8b4a3fc313a59168c8b2e459922d09167c8b3a459522c99166c8b22458f114688a2c45122287114288a0c4502227d113d889e444ee22751139889c4,0x4712238711c288e0c0002239511c088dfc46f2237711ba88dcc46e2236f11b688dac46fa237b11b488d9c46ca236311ae88d6c46b2235711aa88d4c46a2234f11b088d344696234711a288d0c47d223e711f288f8c47c223df11ee88f6c47a623d911eb890b44856242912138909448462421120f89144489e244d122589124488e24451221890f4,0x491a248b12448921c0002248512408920c48de247f123e891cc48ee24751238891ec48f224651233891a448d6246d12318918448be245d122d8916448ae2455122988f24478e23c111df88ef4477623b511d988ec4475e23ad11d588f44479e23cd11e588f14478623b911db88e94474623a111cf88e744736239911cb88ea44722238f11c688e2c,0x4a1a250b1284800044a0e250312828940449fe24fd127d893d449ee24f11279893bc49d624ed12748939c000224dd12708939449c624df125f8934c49b624d9126b8935449a224cb12668931c499224c512608930c497a24bb125c892dc496a00011259892bc000224b11256892a4494e24a5125189284493e2499124d89254492e2493124789244,0x4d9626d3136689b244bbe2689134e89a6c4d322697134a89a4c4d22268f134689a2c4d02267f133e899ec4d0625dd1321898b4000226391329899440002263713278993400022635132589924000226331323800044c622645131f800044c5e263b23f591f9c8fba47df23f291f8c8fb647d923f091f5c8faa47e923fd91fd48fee47f312cc8966c,0x2279513cf89e740002279b13c989e644f2e25e913a989e444f1e278913c389e0c4f1a278b13bb89e144ee6278113ba89de44efa277b13bf8979c4ee2276f13b689dac4ed2276713b289d8c4eb2000113a889d5c4ec2275f13ae89d6c4b7225c312eb897544ba625d112e7897344b9625c912e3897144b8225bf12de89b1c4dae26d5136889b3c,0x5026281112f68a03c501a280b140480004500e280114028a00c4ffe27fd13fb89fec4fe227f313f789fe44fca27eb13f489f9c4fda000113eb89f8c4fc2000113ea89f7c000227d313ee800044fb627d1000089f644f9e27cd13e589f244f8e27ab13d489f144f8625eb13e089ef44f7627b913db89ed44f6627b113d789eb44f4e27a513d189e84,0x532e299500008a5f45326299100008a5ec531e298d14c58a624530a298714c18a5fc5302297114a68a52c5292294714b38a59452c6296114af8a57452b6295914ab8a55452a6294f14a8897944bc625d9000089d244eaa274713a289d0c4e82000113a789cfc4e7a000113a689cec505a282b14148a09c504a2821140f8a07450362819140b8a054,0x53fe29fd14fa8a7ec53e229f714fc8a79c53d229eb14f68a7bc53c629e114ef8a77453b629d914eb8000453aa29d314e68a72c539229c714e28a6fc538229bd14dc8a6ec536e29b314da8a694536229af14d48a69c534629ad14d58a6645336299d14cf8a68451fa28fb00008a3e451da000114788a3ac553628f5154c8a3dc52f2297714ba8a5cc,0x56be2b5715aa8ad4c56ba2b5b15ac8ad44569e2b4d15a58ad24568e2b4515a18ac1c56322b17158a8ac4c56222b0f15858ac2492de496d24b4925ac92ce496524b19258492fe2adf15708ab2455962ac315628a8e4546e2a3500008a8cc545e2a3115108a87c543a2a17150c8a85454222a1315078a82c541a2a0915038a81454062a0114f28a7cc,0x59f22cf7167a8b3cc59e22cef16768b3a459ce2ce524c692644933e499d24cd92664932e499524c99263c9316498924c29260c9302498715d68aea4574e2ba515d18ae84573e000115ca8ae7400022b9315cd8000457322b9100008ae5c571e2b8515c18ae0456fe2b7d15b98adc456de2b7b15bc8addc56ea2b6d15b58ada456ce2b6515b18ad84,0x5996000116608b2fc597a0001165d8b2e400022cb516598b2c400020001166f8000459b22cd700008b324598e2cab16548b29c594a2ca316508b27c593a2c9b164c8b25c592a2c9100008b2bc5a322d6716ae8b56c5ab22d5716aa8b54c5aa2000116b18b5cc5ae2000116b08b5bc5ada000116af8b5ac5ad22d4f16568b5945a9a2cfd167d8b3ac,0x5b922dcb16e38b7145b862dbf16e08b4745a2a0001168d8b44c00022d1716888b43c5b4a2da316de8b6ec5b722db716da8b6c45b662dad16d78b6ac5b4e2da917158b8a45c4e2d8716d08b67c5b3a2d9b16cc8b65c5b2a2d9316c78b6445b1a2d8916c58b60c5b0a2d7700008b5fc5af22e1b16c08b86459ba0001166d8b35459a62cd116678b334,0x5efa2f7b17bc8bdbc5eee2ee917798bbc45dde2eed17758bb9c5dca2ee317708bb7c5da62ed117678bb745db62ed9176b8bb545d9a2ecb17648bb1c5d8a2ec317608bafc5d722eb7175a8baf45d762eb317588babc5d5a2eab17548ba9c5d4a2ea317328b9d45ce62e7117378b9b45cd22e6724db926d4936649b124d78b7745bb6000116ec8b754,0x7cce3e3f1f278f9347cbe3e5d1f2b8f9547c923e471f228f8cc00023e4b1f1b8f8d47c862fc717e98bf445f9a2fcf17e48bf2c5f5a2fc517e18bf045f7e2fbd17dc8beec5f6a2fb717d98bebc5f622f8d17c5800045f222fab17d4800045f1e2fa717d28be8c5f422f9f17ce8be645f362f9717c98be545f122f7317b88be0c5f02000117ba8bdfc,0x7f6e3fb51f4f8fafc7d623ecb1f648fb1c7d8a3ec31f608faf47d763eb91f508fadc7d4a3ecd1f518fad47d663eaf1f568faac7d363ea700008faa47d3a3e991f4b8fa4c7d223e8f1f468fa2c7d123e871f428fa0c7d023e791f3b8f9fc7cfa3e731f388f9d47cda3e6f1f358f9ec7cd23e391f308f8ec7cca3e631f298f8f47ca23e5b1f2c8f904,0x7eaa3f531fa88fd3c7e9a3f4b1f9a8fccc7e923f471fa28fd0c7e823f3f1f988fcbc7e7a3f3b1f9c8fcb47e563f371f948fc9c7e4a3f231f908fc7c7e3a3f1b1f848fc1c7e323f171f8a8fc4c7e0a3f031f888fc3c7e1a3f011f7f8fc2c7dfa3efb1fe08ff747fb63fd91feb8ff547fa63fd11fe78fefc7f7a3fcd1fe58ff247f763fc71fdc8ff14,0x7de23eef1f768fb947dc63ee11f6f8fb547da63eeb1f748fb447dce3ecf1fc68fe7c7f263f911fd98fec47f5e3fad1fd58fea47f4e3f8f1fd28fe8c7f423f8b1fc48fe747f363f991fc38fe5c7f0a3f951fc18fe048022400f20068fd7c7efe3f7d1fb18fd847ef63f791fbb8fdd47ee63f711fb78fdb47eba3f5b1fb58fda47ece3f591fab8fd94,0x8122408b20449023c810e408520469020c810240a9205390294814640a1204f9027481364099203d901a480fa40752039901e480fe406b203b901bc80c6000120389019c80ca406d202790134807a403b200d900a480724037201a900cc8062402f2016900ac804a401920139008c8042401d200b9007c7dba3edb1f6c8fb5c7df23ef71f7a8fbcc,0x825a413b2095905448316416f20b6905ac82d2416720b29058c82c2415f20ab9057482b6415920aa9054c823241252093904748242412920879046c8246411f208a9044c82120001208b90434821641110000903ec81fe40f9207b8000481ea40e1206f9037481b640d9206b80004818e40d5206990344819e40cd20649031481964097204a9024c,0x847e4239211b908f4847641fb2103907fc840641fd2104907c4840a420120fb907d483d6000120fc907bc83da41f320ef9077483b641e120ec9075c83aa41bb20dc80004836241af20d6906ac835241a720d29068c8342419d20cf9066c8332419520c89065c829e414d20a590524826a413320a39051482864141209c904dc8262412f209f904f4,0x85be42dd216d90b04858642cb216290b3c859a42d1216990aa4857242bd215a90aac857e429b214e90ac4853242ad000090a8c856e42a7000090a948576429f215780004854242b3211a908cc843642192118908bc845a422b21149089c842e421521099089484464221210f90844841e421d21069082c849e424d212590924848e4245212190904,0x86f6437921b78000486ee437121b690dac86ce436521b190d8486be435d21ad90d6486ae435521a690d2c86a6435121a390d148692434121a190cfc869e433d219a90ce4866e4327219290cbc865a4315219d90c4c86464321219990cc486564329218e90c6c8632430d000090c7c8622430f218b90bec85f242c7216c90b9485c642d7216a90b84,0x898a44c32260912fc87be43f321f890f5487a643eb21f490f8c87c243ef21f690f9c87ca43cb21e690f7487b643c721e890f3c879243d721ec9127489364499224b91254892644912247912148906448d2245912248902447f2243911f488f6438f21c490dfc8736439921cb90e548726439121c690e2c870e438521ba90e7486e6438321c090df4,0x88ea44732238911bc88da446b22349119c88b2445722329118c88c2445522299117c88a2444f000091134889644492223910c4885e4445222191104887e443d221d910b488564439221b910d4885244272219910948846440122109107c883a441b220c9105c880a4403220a9104c8822440f21ff90ff4881a440b220490fec87f2440721fb90fd4,0x8c5a462b2311918a48c4e462523109187c8bda45f322f8917bc8bd645f522ef917a48bce45e522f19176c000245e122ee917648bae44e722729138c89c244df226e9136c89b244d5226b9134c899e44d121d790eb4875643a921db90ed4878a43c321e090efc877a43b321d890e94874e43a321dd90e848772439f22539129488f24477222e9116c,0x8db646d9236b91b548d5a46af235891aac8d6e46a3235a91acc8d4e469d000091aa48d42469f235291a3c8d26468d232e919dc8cea46732338919bc8cda466b23349196c8cce466523319197c8cc2461d230d918648c2e460122ff918548c2646052301918448c1e45fd23069182c8c1245fb22fc9181c8bee4655231c918dc8c6a46332318918bc,0x8e9a475b23ac91d5c8e92478323c091dfc8efa477b23bc91ddc8eea476f23b991dc48eda474123a291d0c8e7e4747239a91cf48e7647392398800048e6e4733239791cb48e2a4713238891c3c8e1a470b238491c1c8e064701238291b4c8da246c3236091b3c8d9a46bf235e91b2c8d9246c7236291aec8d7246fb237c91b948dc646e1236f91b74,0x90ba485f24339216c90b2490b2498924ac925e492d2494920fc90a2485524299210c9082482f242b920b490964849241e920ec909e484d242392114906e483524199209c000248392415920a4906247bb23dc91edc8f6a47b323d891ebc8f5a47a123d591ea48f4e47a323d291d848ea2474f23b591da48ece476523b191d548ea6475f23ae91d2c,0x919e48c3245a922dc919248c72458922ec917248b3246092314910e48af24569227c913a488d244592224914e48a52455922a4914648a124409224490fe4895244c9225c90f64883244d9221490fa488f2449924e4926e493524999244c9222490f248692424920e490524819240490e24879243b9219490c64861243a921cc90de486d2435921a4,0x1b3d8da0c6d3600031b358d9cd82a6c14360a5b04ed8266c11b6095b048d8206c1136085b03ed81e6c0e360758000c6d4636ab00018da2c6d27253c929a494b24a49251c928a49432475923a491e648f12477923b491fe48fd247d923e491ce48f7247a9238c91ca48e1246f9247c923a48dd246d922fc917a48d5246992334919648d9246b92344,0x127d8904c49d624d3126d8938c4bd625db12e988b4c000622db11598000c45c622c3115d88b2c4cf6266b133188f2c000623eb11e988f8c000623f311ed8818c40b62053102589fec4fe627eb13f197eccbf465f932fcd97eacc446622b310d9a40cd1c668f3346d9a3ecd1d668d31b218d88c6ca636331b0d8d92c6c7636631b158d96c6d660003,0xda986d2c368600030dcd86ecc00061b2b0dd186eac00061b030d8d8000c35c61b130d7986c2c37761b330dc986bec37961bc3000186dac37161b23000186d6c36f61aeb000186d8c37061b730d5d8000c35361acb0d558000c35261ac3000186acc35b600030d5186b4c5086283314258a0ec50a6230312658930c497624ab1251892cc4a0624f3,0x18e58c3ec6206310b17158000c5c162e3b170d8b88c00062e1317218000c5c062e331a0d8000c6806342b1a098cfec0006340b1a198000c67e6342314c58a64c55262a9b15158a90c54962a13151d8a86c546629eb15018a82c53f629db14e98a7cc53c629cb117d88c6c46162313117588bcc4816241b1211890ac47f624030df186f4c37b61b3b,0x4d8000c012600bb00018022c016608b304558228c1186089b045d823cc11d60003046d8238c000608cb04698ba6c5d262e4b172d8b94c5cf62e8317458b98c5ce62e6b16f58b7ec5be6343b19d58ceec676633e319f58ce0c6746338b19c98ce6c678633cb19ed8cf4c66a6337319ad8cd8c66f6336b18d98c66c6356319318d18c6ec631631c3,0xaf98588c2cd600030b298598c2cb6164b0b1d8590c000615db0af58578c000615cb0ae984a2c2506127b08c58460c22f6117308d1845ac2336116308c9847ec23e611e308f58476c000611c308e98472c000611ab08dd846cc0006115308ad8030c00e600530025801ac00f6005b00418018c0066002b00118002c0076001300218006c015600a3,0x33d81a2c0d0604c3025d812cc099604d302818144c09e604fb0285813ac09c604db0291814ec0a56051b02998152c0ac6055302b58156c0a86038b01c180e8c0006039b01c9808ec0466025300018092c048607a303cd81e4c0f1607ab03fd81f6c0fc607eb03f981f2c0fa607b303dd81f0c34761a330cb18586c2c2616330b058580c2bf6162b,0x4ed8274c139609c304f1826ec13f609eb04f9828ac14960a33051d8290c14360a2305058284c14060a530531829ac13560a7b000182a8c14e60a83054582aac15260a9b0ce18644c3256191b0c858640c324618a30c59862ac2a760a5b08818418c20e6106b083d8422c21261083038181bec0e2606f3037581c2c0e3607230331819cc0cb6066b,0xbdd85eac2f66177b0bb985e0c2e86174b0bb185d6c2ea6176b0be185cec2e36172b0b9985c8c2f9617db0be98520c28f613b309d184eac000613bb09e584f0c25960efb077983bac1dc60f03076d83c2c1e260f4b079d83d0c1e560f33079183c6c1ea60ed307b583d6c1ee60f6306f9837ac19f60cf306018302c17e60bfb00018304c18460c1b,0x24459220c90c6486b242d9224c916642fb217990cac85c64303218990ccc864642eb21a190acc000642bb216d90b2c000642d3215590c6c858643831d9d8ec6c76263b2b1d918eccc890644732231911ec88d6445b22459114c8616449321fd9102c8806434b000190f6c879643eb000190fcc87a643e3404da02ad014680b30bcd85e4c2f46178b,0x22a99156c8ac645432541918ec8c6645cb22f59174c8bb645e322e192aec95a64ac325659288c94664a2b251d9280c94164a1324fd9286c8e664723238991cac8e36470b239d91bec8e063d9b1ec18f64c7ae63da31eb18f5ac7c063e131f058f7ec7c363e231ebd8f74c7b863dcb1edd8f62c7bc600031ed98f7cc7bd63ddb24399226c90f648a3,0x41a9b5d0dae66d73b6b91b5cadae16d7136b8da5fad2fc697db4be9a5f2d2f8697bb2c599630cb146551b2c49962acb13658bb521da90cd4856a42351c1a906cb0f6588b2c319614cb0e6586b2c2d9620cb1d658f32c6d9634cb19658e32c7da904d4816a4032c219612cb06658232c0d960ecb056cf6b67a5b3d8d9eb6cf53679db3ccd9e86454b,0x2d01968ccb4265a232d218000cb4165a3b0001967ecb4565b2b2d9996c8ca106509b283d9422ca12656932dc996e2cb7365b7b2dc195eecaf4657b32bcd95e4caf5657cb2aa59556caaa600032a91954ccaa7600032aa19544caa564e532719938ac9c864e3b2725a69edc0d6e063702daaeacf9867cb33e659f2ed06f6835b41b5a0dcd06c6834b,0x36919b44cda566d3336a59b50cda765fbb2fe997f0cbf966c7336359b16cd8f66c6336419afccd7d66bdb35fd9af8cd8066c33361d9b08cd8566c4336299b12cd8366c1336059a04ccf7667b333d599f0ccfd667f333fd99e6ccf2667a334019a02ccfb667d333e599f8cdd066e7b3739ae48cb5865ad32d6596aecb4c65a4b2d2d9694cb4360003,0x7249b922dc8f6e4837231b91adc8e66b6335a99adacd6f66b7335ad9ad2cd6866b3b353d9aa0cd5266a7335459a9acd4c66a5b34fd9a86cd4466a1334f59a80cd3c66a0b34f99a8acd3b673cb39e1997accb96000332559926cc92664a332719936c000664d332759932cc98664bb36f59b78cdbb66dd300019a92cd4a66a43351d9a8ccdaa66d1b,0x4e2da714d38769cbb4e59a72ad39469c9b4e49a722d315698a34c41a626d3126988b4c35a61cd30c6987b4c21a616d30a6984b4955a340d19f68cf346759feacff467f9b41eda0f2d07a683c33f89af5cd7af6bd6b5a51ad26d6926b48b5a41ad1ed4996e88b7451ba26dd126e87b7439ba20dcde6e6eb737db9b8dcd96e6d3736db9b0d1f56e49b,0x5885ac50d6256b113589dac28d6176b0cb58598000d6126b0c35845ac2ac0006b09b5869ac20d6a46b52b5a8dad44d6a16b5035a79ad3ed69d6b4e35a6dab8cd5c46ae2b570daa24d5146a89b5459aa2ad5116a743539da8e8d4736a39351c5a8ded46e6a36b52d9a96ad4b76a5a34e71a736d39869cd34e65a71ed39069c734e35a718d38969c43,0x84f5c270e137709cb83d1c1b4e0d97041b81f9c0f2e078701837d29be30d7c36be135ed9add0d6e96b73b5a19ad0ad6836b4135a11ad00d6816b3fb5ae9ac76c0006b1f358e9ac7ad63f6b1cb5989acc2d6476b2235915ac8cd65b6b2035905ac86d6426b38358f1ace2d62b6b17b58c5ac5ad6306b16358b9ac46d6246b14b0001ac4cd62a60003,0x16374b1a258e12c6c96354b19258cd2c3e961e4b102586d2c38961d4b052582d2c18960d4b07a583919208c8f464723245192c87b5442a2214d10ee8878409b2115508ee8476423c211d54824e39571a6b8ba9c368e18570a23850dc284e14170a038521c292e14b70a53851dc28ce145709d384f9c276e13f709e3]⟩
def actions : Column := ⟨13,#[0xa6052021810806a03402881400820c001980c804e02600e807009e84f027213806283101820c003681b00d2068026813009204809604a01680b002e0160078038013009004402009204801ca2e417002b015007c13c01500a003511a00c001600910400144080000,0x568aa40fa27902a894403601a00c8e343121450a084142020cd0648274132075038831412a04602100b825a05d011808804201700b00542de16e0b685a424e1260928c841ce0e6072838415e0ae0568aa40fe27e03e81e40ae25602a814403e01e00e88642b81580,0x9204801ca2e407002b015007c03c01500a003511a00c003801b00d00640300050c6862428a141082840419a0c904e82640ea07106282542fa17909a8cc41ea0f105e8ae411a089032818408604201588a84522b504280f807603a01c80982da3690928c841ca2e10,0x8604201a80d0052028028814008204001980c804e02600e807009e04e01f80f8062030012a09404801b40d8068026012026813007a03c017a0bc05c0230110064030011008002b01480a025812807683b01d00b4058021010005c02c00f407803800980480220100,0x1c80e024812007203805580a803e81f00f025502a0140068030006803001018d0c4841420209d04c81d40e204602105d46e212d19483b45d20b5158821450205d12c85b42d20e507081f40f205502880342c81600ae05602381180aa054022811006e03602981480,0x8604201a80d0052028028814008204001980c804e02600e807009e04e01f80f8062030012809003601a009804809a04c01e80f005e02e0118088032018008804001600a025a12c09484a01da2ec07483a016a0b405882c010a28404082000ba05c02c816007a03c0,0x3c807401a11408804102000cc06402701300fc07c031058009404801b00d004c02403d01e008c044011008002c01403b01d008404000f007002401000500200e407001f00f0034018007003000500200002c81600ae05602381180aa054022811006e03602981480,0x7c831418229504881ac0d4069026812c09404905e82340c6262130896807c22601105b46d212519083945c20ad15481f44f218d0c48514282105080833419209d04c81d40e20c504a811808412d02f81780ba16d0b4849c24c125190839c1cc0e507082b455207d0,0x45022411006303101840c004402000b005012c09403b01d00b4058021010005e02e0160078038012008002801009204801ca2e407002b015007c03d81e80f207802a014006803000e865432214d1a484342120d50688a941460a2050833453a3850c084f42722fd0,0x568aa40ae25602a807c03c01d007803801a1640b005702b011c08c05502a011408904401b80d80a6052021a10c08403501a01440a004102000cc064027813809803a01c027813807e03e01880c004a02400dc06c034013009013509a04c01ea0f407802f017008b0,0x9c8bf41f20c51608a4c12409103681ac0d4069026812411628a144899410405e113008824a39d05106343121450a084142020cd064827c13c09d04c81d40e209704b025408c0420ba84b416208704302142de16e0b685a424e1260928c841ce0e6072838415e0ae0,0xbe82340b403e113008824a253029014431a1890a2850420a101066832413a09903a81c412a04602104b416e0b605a85bc2dc16d0b4849c24c125190839c1cc0e507081fc4fc07d02b89580aa01e007803801a19d0cc85542a231508883741b22d514d061430213d0,0x2483cc5e42f113283a816c02601105b464a38d0c48514282105080833419209d04c81d40e2095023010825a0ef07703b42da1690928c8415a27d02a807441a1950c8852421a1090688a941421451c2860427a13917e83e418a0c114a82440d6069026812c0940490,0x34813409217d0bc8a080bc22601104944f607a03c86343121450a084142020cd0648274132075038825408c04209784b825a16d0b4839415a27d02a803435a1a90b28d8474211216f04281ac102067061430213d19c8bec1f20c5061830818209514889b40d204d0,0x9803d01e00bc05c02301100630308180086042020810005a02c01404b02500ec07402d016008404001700b003e01e00e004802000a004024812007281500a6052028814033a1990a88c441b234d16a8a680ec3850c084f42722fd07c831458229304881b40d606a0,0x82840419a0c904e82640ea07102301082ee1760ba84945ca0ad13e815403a20d0b205802b815808e04602a815008a04401b80d80a6052021810806a03401480a00a2050020a104080033019009d04e026027813807e03e01880c004a02400d806802701300901340,0xc6862420a10104e82640ea0710be83c408e04602285dc2ec1750b883bc1dc0ed074821c50c285040817c4bc25d02c80147543a20cd0d5832414e0c5060c30213d09d84e82720fd17c8b1418209514889b40d204d02485ec6f43791b904b804c0220c6862428a1410,0x3886143020fd07c825412206d03485702b014c0a404302100d40680510280104180033019009c04c01d00e013509a04c01780b905c01900c004402004bc25c12d09604a42500b705b02d41680b1058017c4bc25d02e01640b003f11f08f407803901c00144080020,0x7482d456208504080fc07c03d01d009c04c025103881800a35c0ac053029010c08403501a01440a004106000cc064027013007403804f427813909c03141880c106001b40d8069034013409804902404b02500b405801700b003c01c063431210508082741320750,0x1f80f807a03a013809804a207103001472a1910a68d2421a10906a834454a0a10828e1430213d09c8bf41f20c50608a5412206d03581a80d204f12709340920621ba82140aa2520c6862428a141082840419a0c904e82640ea07103381980ca1750b884b46520ed0,0x2f097407e03e01e80e800e2060028e743321550a88c542220d91ca8c345340720c2860427a13917e83e418a2c114a824c12409103789b84da069026812411a08a13d06343121450a084142020cd0648274132075038823c11c08d0ba85c425a32907683a416a25d0,0xc6862420a10104e82640ea0710bf85f82fa0ed0438a1850a05d01f80f807a03a003881800a3ad0d484282041850c083f41f60fa07c831c18c0c506081b40d204d02485d41c41a90870634312105080827413207503883dc1ec0f50bb85d82ea1710438a1850a05f1,0x4882400da06c03481a005802a113009004001d10e006831a1890a2850420a101066832413a09903b81d80ea1850c084fc27c13d19c83fc1fc0fd07c8314582095048809803a3a30d106842bc1920c506143061820c084fc27c13d09c831418206d034813409216a0,0x6a834454a0a3051028430a18109e84e45fa0f9062825412205a0b205802b815808e04602a815008a04401b80d80a6052021810806a03401480a00a20500208100066032013809803a01c027a13c09c84e01fe0fe07e8bf01f20f8063831818a0c4060830012a2940,0x3680b404c1640b005702b011c08c05502a03140880b701b034c0a404302100d406802901403450a2050428010518204042000cd066032419009d04e026453027503a01cc0e407103804f02700fc07c031018009404801b00d003c01d00e032a1910a68d2421a1090,0xa6853029010c08403501a00a40500510280104080033019009c04c01d00e407009e84f027213807e8bf01f20f806283101820c004a8a5012024d026012005a02c015089804802000e006833a0a20c6862428a141082840413e09e04e861430213d19c83f41f20c51,0xa404342181091840b541a80d106802901422a01a20500208100066032013a29c04c0cf02700fc07c031018009404801b00d406802601200b805a02c06743321550a88c542220d916a8a6830a18109e83f41f20820b205802b815808e04602a815008a04401b80d80,0x6706143020eb07503a42b81580a6052021810806a03402881400820c001980c804e02600e807009e84f027213803681b00d004d026012004c024010007003418d0c4841c20c1050c2860412a06d01305902c035c0ac04702303540a80c502202dc06c0d342981490,0x4c01d00e00c506203000da06c0340134098048013009004001c00d063c31c18d07e82540da0260ae85702b21580aa05442a01440a004102000cc065032013809809e04e01f82f8062030818009604a02400d806802601201680b305902c41601ad0d486842141020,0x66832409e04e026812408e04602280fc07c03d01b88d806a3540a905402281100a20508280104080033019009c04c04f027413807e03e01882c004a02400d8068026012025812a094068832418a0b905702b014c0a404302100d40680510280104180033019009c0,0x1b00d474a1a108e84641a418d1a28b141860c206082c81540d706a8e34312105080827409e04e026812407c03711b00d473a1990aa854462a11106e836472a295049824812208a14101e81ba0a7053029431e18e0c6862428e1460a28d0420e106082840419e0ce0,0xac8c6432a34d16503141860c206082f41742b205582a815214f0a7053431a189082833453a04f027013409204601f00dc46c0351d686a42ca3611d284486140d60c68bf41f60fa07c83c85d40e2087843821a18d0c485146820cd14e813c09c04d024811807c0371,0x7c83c85d40e208b845822a1950c885346920d503b01bc0dc06d034819c0cc06502f01583543a20cd0e4829c1850c1860830217a1b905a832e1960ca851c28c145183841820a0cf067033453e29e04e813c09c04d024811c08c04501f80f807a03711b00d474a1a10,0x578ab815a3aa1d106687141850c1860830217a1b905a833e19e0ce853461a0d503b01bc0dc06d034819c0cc06502f015836a1b10ad050827a13b09d04e42541220ab855472a19108681d80de06e03681a40bc05712b015475a1a90b2858462439518103f41f60fa0,0x6082444da06902681240ca02601100581ca2351058028012205135813c49603710584f42720fd07c831418209504881b40d204d02482340ca02607288d44120051c9062830a1830c106042e416a0d786b835a0d716b035459e2ce0668b1c18c0c506082dc16c0b50,0x9c83f41f22c506082444da069026812411a065013008802c0e511a882c014009103881800a26b027892c02e03710584f42720f9162830412a29113681a409a049046819404c02200b805802a2e511a882c0140091028a4c0de26b033802c00e33d09c83f41f22c50,0x32809804401607288d441600a004881470613f09d802c27a13907c8b1418209514889b40d204d02482340ca026011005806a20b005002440a29303789ac0ce00b09e84e41fa2f9162830412a29113681a409a049046819404c02200b039446a20b005002440a33d0,0x308114082029042817404207d02a801402e01600a84982420e607082b815a0a903f01e40ac05101b00c400c00509e84e41fa0f9062830412a09103681a409a049046819404c02200904981cc0ae03f015806c00e09c83f45f22c5060825452226d034813409208d0,0x7882f417208d04481940c204502080980242e511a8b0c12e08f04182ac0fe293037819c0b607b02b8cd417212e07702d810e086042817c0bc05d01f009824a3210728b8415a2a903e89e40aa25101a88c4032205101800800213509883d45e20bd05c82345120650,0x7e83e418a0c104a82440da069026812405c0ed01e80441ca23515e83b447a213009015406a00b005002412606b045818c0f605309a84c41ea2f105e82e411a289032818408a041014889802c12519083945c20ad15481f44f205512880d446201910084d42620f50,0x7c031018009404801b00d004c02403d01e00bc05c0230110064030011008002c01403b01d00b4058021010005c02c00f007002401000401c80e005602a00f807802a014006803000e006000812d09483b41d20b5058821410205d02c80f407201503e815427a1390,0x9703bc1dc0ed05b02180bc03f01f00f400a10504e81380c4042076816c0b405901d00940fa03701b00d401211208682780dc08a03103b450608204080944ae05602a80d401211c08c04502200dc06c04302100d40680290140104080033019009c04c01d00e00fc0,0x58021810808002f01700b003e01e00e004c02401003901c00ac05401f00f005402800d006001c00c002000a00409a84c41ea0f105e82e411a089032818408a04109703b816e0b605a82180bc03e007002800a13509883d41e20bd05c8234112065030811408202d0,0x41841418a06502100a816a03b01d00e404c01101a88780c602b01d847023011408803701b010c08403501a00a405004102000cc064027013007403803f01f00c4060025012006c03401300900f407802f017008c04401900c004402000b00500ee07603a016c0b40,0x4602200c8060022010005802807603a0160084040016007803801003901c00ac05401f00f005402800d006001c00c001000013d09c83f41f20c5060825412206d03481340920bd00d05741bc0d207902e80ca0eb07503a416c085008839455c13301583ac17602b0,0xa5842c2860cb04d81cc22408b04502240f607a03c82940c6062030814c0a40510a8829812c0bb05d02e41660b2058821823811808a04401b80d808604201a80d00520280208100066032013809803a01c01f80f8062030012809003601a009804807a03c01780b80,0x4501880bc12517289e40a6052028807454a10504e81380c404201f03940a203301900c403a08d03280a41da08502e80f404212509083945c20ad05481f44f205502880d40620020c184ec246093035818c4a606b025810c46604301d800c2c615b08d854c2260db0,0x3704bc25c12d09483bc1dc0ed17482dc16c0b5058821c10c08514080fc47c03d00b805802a056003001428a1410828c0419a0c904e82644ea07303901c412a26d12100a807402619684a41de0ee0768ba416e0b605a82c410a28102e816402a03600304340ec06e0,0x4304b42520ed17482144ba03d00a82b800c1450a0840419a0c904c89d40e20fd12100a807402619784b825a12907783b81da2e905b82d816a0b102f89780ba03f11f00f402e01600a81f800c0050a6852421a10916a834414a0a114e89a80c404202d00f869a0720,0x2b89584aa05101b88d846a0310ad0d4829430e0a1041827413207904a81dc0ed15a82144ba03d00a849800c14d0a484245a20a11828a744d404e13101080b403e11904b42520b5042897407a01507300182ba15908e8c646a20d2153032813c0c204b02e81140b20,0x2601201e80f0046022008804001600a01d80e80420200078038012008002201007203800f807801a80d006001d00e006001800900404d42620bd05c81940c204502080a40ba03d01084942420ad05481540a2035018805c02c015093849824a12105782b815a0a90,0x7003428a1410828c0419a0c904e82644ea07107e8a544da24201500e804c32503e815407e03e01e849c24c125090839c1cc0e517082bc15c0ad05481fc0fc07d13c815c4ac055028803c01c00d08a0440208100066032013809807e03e01882c004a02400d80680,0x9704b415a05501a80342ba1590a8832813c0c204b02e81140b2043049416e0b605a849424205501a803429a14908684245aa0d10508c1453a26a027098808405a01f0b940be05e02e849c24c125090839c1cc0e517082bc15c0ad05481fc0fc07d11b88d806a00f0,0x2100b865a05d019011c08c04509684a41da2e905a82c410a28102e816404a007003001427a13906283040da069026812417a13505c80bc05c02d09784b825a12905b82d816a0b102f89784ba05901f88f847a039002854822414208304e81fc13207904a81dc12f0,0x4704b415415906702fc17c0bd09784b825a12902f89784ba03f11f08f404e026012801c00c0050a6852421a10916a834414234516689a809406202309480ce06603284b42520ed17482d416208511e809400e0060028514282105180833419209d04c89d40e20c51,0x5e82e411a24500b0514282105180833419209d04c89d40e607203884d40ca03a027813809a13509883dc1ec0f517882fc17c0bd05c823451206503080582a61520a8845828413a09903d824413709b04d416a05f12f097407a025003801800a15d0ac83281840ba0,0x63031418209704b025412202f01700b404e026012807c03c01d0a9050827412a09f84f827a0bd032811402c15d0ac85441940c204b04d41660b2058831c18c0c509a84c40ca04500b053429210d0848b541a20a114e89a80b414d03901bc0dc06d09a84c41ea2f10,0x4f04f45740b2055033c19c0cd09e84e41fa2f904a89b405c02600f05542a20dd06c826827a2fd14502080f409f04e8cf42720c506081b405c02600f807803a14d0a484342122d5068829414234513101680a40a503b81d80ea13f09f04f42720ff07f03f45f20c70,0x27011807c0360ad0d4829434208304c82541220a3851828a0ff07f03f458e0c6062825c12c09513789b80da02f01700b404e026012807c03c01d0aa85442222d90a28c1452408a04101e820e10608284f42720c504a89b405c02600f05742b211d18c8d541a42ca0,0x4b025451e08e046821c10c08503f81f80fa15a1a90528674132095048829e14e0a6841459a09d027011807c0360b285842240fa07903a81c410f0868d142820cd027011807c03701b00d42ba15908e84645a434516102e81640aa06b83581aa1450a0841460209d0,0x1100581cc0ae03e895440a33d09c83f41f22c5060825452226d03481340920f1146819404c02200b039446a20a004881467a13907e8be458a0c104a8a444da069026812411a065013008802c0e511a88280122051a104e826412a091057c2bc15d04f8a7813a2971,0x4881440207207f031812a26d11304946420e517082b455207d13c81544a201d10d8068032009102880412a13509883d41e22bd05c82244ca061022810442c01217288d441c00519d83ec26607209e84e41fa0f9062830412a09103681a409a04904681940820260,0x4889280ce0651228cb40440120070d3821c0d605301d467a13907e83e458a0c104a82444da069026812411a06502e80980440160928b944f2055105002440a33d09c83f45f20c5060825452226d034813405422601104946420e517082b455207d13c81544a20310,0x5a02c010808002e0160078038012008002801007203801580a803e01e006803000e006000a00400004b42520ed07482d416208502e816407a03900a80440aa00d0aa854422a11308904441ba0d9086827813409604901b811c06204302080bc0e510e80141fa2930,0x5d822c08602308282741fa06b03501a409408d123891808a25a01d00880240360070c7023011408803701b010c08403501a00a405004102000cc064027013007403803f01f00c4060025012006c03401300900f407802f017008c044018008804001600a01d80e80,0x44827a13907e83e418a0c104a81b40d204d02483d417c0660228098044016089053429210d08483541a207603901b80d413507a82f808c05e02d01580a400e0d184dc11606309583dc116063075844821a13507a82240c606203084b41da08105d822c07609f0,0x8803701b010c08403501a40d00520280208100066032013809803a01c01f80f8062030012809003601a009804807a03c017a0bc05c0238118088023011008002c01403a016008404001700b003801000500200e407002b015007c03c014006803000e00600180040,0x2000b00500e8058021010005c02c00e004001400803901c00ac05401f00f005402800d006001c00c001000013d09c83f41f20c506081b40d204d024819404c02200b05542a211508984482220dd06c843413c09a04b02480dc13507a821810407e03d04702301140,0x7e81a411608a044807809614b0a505241a41430a1050419a0460b2842c214109069040c20410106682f808c11c08c04502200dc06c04302100d40680290140104080033019009c04c01d00e00fc07c031018009404801b00d004c02403d01e00bc05c02301100440,0x2482340ce066032808802c12517289e40ae25602a88d441400914f825c08602f01f80ec04e07f1b185742ac116052833813a0c204a82e811a0b604282a80fa35d08503481e60f207882b82060cb089041411608a04481ec0f407909d854c1f611508502880ec13d0,0x9388dc6ca13d09c83f41f22c506082444da069026812426a0f5032810444c02200b039c5cc0e511a882801220514d81ac09e24b04784f42720fd07c831418209504881b409a04904680980440e500485340e413d09c83f41f20c5060825412206f03701b40d204d0,0x4981bc4d60670938d3467a13907e8be458a0c104a8a444da069026812411a065013008802c12517288d44140091028d340e413d09c83f41f22c506082444de06e03681a409a049046819c0cc065013008802c12517289e40ac035105002440a33f035813c4960431,0x34813409208d0308098044016093039815c07e01b003800c13907e8be458a0c104a8a444da069026812411a065013008802c0e511a88280122051c184fc27613d09c83e458a0c104a8a444da069026812411a067033099404c02200b04944f205511a88280122051,0x1300881ca25101a882440a34d039025445a02607288d443601a00c802440a2fd0788a340ca01601a881469a07209683b410203d010805424c0e605701f806c01e00701a409a12d07682040b203d093039815c07e01b003829a13d09c83f41f20c5060825412206d0,0x7c8b1418209113681a409a049078899408a02601100581ca235105002440a26b027892c27a13907e83e418a0c104a82440da069026812411a06501100581ca27f13f01f44a2035105002448603f01d809c15e33d09c83f45f22c5060825452226d02681240ca02a1,0x46819404c02200b01f44a2035105002440a29303789ac0ce13d09c83f45f22c5060825452226d034813409208d032809804401607288d44140091028cf42720fd07c8b1418209514889b40d204d02483c451a065023089804401607288d44140091028cf42720fd0,0xb039440a33d09c83f41f20c5060825412206d03481340920891328098044016093039815c05601b003800c13907e8be458a0c104a8a444da069026812411a065013008802c0e513e894406a20a004881470613f09d84f42720f9162830412a29113681a409a0490,0x26812417208d032809804401601a881470613b051830c0de0ab09e84e41fa2f9062830412a29113681a409a1350468194082226011005803400a07f8bf81fa2c609a82340ca02b11508a444c01600e8828186283155834c19609f031810c0a604d09a82340ca0410,0xb0154412205135812c11e037135812c0c632719e84e41fa2f9162825452226d034813409202a113008824a2e515480d441220519c82544da04d01304945ca23510d80680320091028b1426a0b9146819402c0e511a881467a13907e83e418a0c104a82440da0690,0x22810444c02200b004843400a0a681c81fa29512684d42622f50788af417228d022810445a02b11508a444c016009086801406d09a84c41ea0f115e82e411a061022810402c01217288d440a33d09c83f41f20c5060825412206d03481340920f1146819404c0220,0x2a0140038018002801000012d09483b41d20b505882040ba03d01c80440fa00d0a6852421a10906a834414a0a108282740dc06a027019808405e02d00f81ca21d002840c27633319184f42720fd17c8b1418209514889b409a04909a84c45ea0f115e82e451a0611,0x17088803c31c08c04502200dc06c04302100d40680290140104080033019009c04c01d00e00fc07c031018009404801b00d004c02403d01e00bc05c0230110064030010005802807603a01680b004202000b805801e00e004802000a00401c80e005602a00f80780,0x60825412206d02681241ea08d02280980440160a2850420a101066832413a099027012805a03e01d00d806410504e81ac0d40690258128092046099818c0860eb031810c10610504e818408604202080b40b203203b822c0c602f02f808c20610117c831c18a2be0,0x6c04302100d40680290140104080033019009c04c01d00e00fc07c031018009404801b00d004c02403d01e00bc05c023011006403000b405802807603a0160084040016007803801000500200e407002b015007c03c014006001c00c003000013d09c83f41f20c50,0x7c031018009404801b00d004c02403d01e00bc05c023011006403000b00500ec07402c010808002c00f007002000a00401c80e005602a00f807802800d006001c00c000029a14908684241aa0d1052828420a09d03701a809c02d02f01680a411c08c04502200dc0,0x2484c411a065013008802c07d1028d8c2a611306d83281e60f2078838815c115039022c11408903d81e80f214b08383ec13e093086829409206303101840a401e06383dc0ce11c08c04502200dc06c04302100d40680290140104080033019009c04c01d00e00fc0,0x5002440c005127892c06e33d07e8be458a0c104a8a444da069026812405422601104841ca2ad13e894406a2091028a544da0260728ab44fa25101a886c034019004881467a1311788af411a06502280581ca2351028cf42720fd07c831418209504881b40d204d0,0x1a882440a33f09d84f42720c103681a409a04909682c404c0e511a882440a2c706182cc27a13907c8b1418209514889b40d204d02482340ca02600b00545ca235105002440a26f135819c27a13907e83e458a0c104889b40d204d02482340ca12d01300581ca2351,0x5b82d816a0b1043821810a08102f81780ba05901f80f807a039003801800a015093849824a12107383981ca2e105782b815a0a903f81f80fa27902b89580aa05101b88d806a03100c84f418212e05b017847c2e511a882440a33906283040da069026812404c0e51,0x828c0419a0c904e82644ea07109e8ce41fa2f90628b0412a29113689a408422e1150cb407c02611100c803c21a09784b825a12907783b81da2e905b82d816a0b1043821810a28102f89780ba059013809804a207103001466a0b909784b825a12907783b81da0e90,0x5c0a30110264030091008022c0140bb41d80e805a02c050808002c08f007002401000505c80e005602a00f807802a014006803000e006001000409a82e425e12e09684a41de0ee07683a456e0b605a82c40be05e02e816407e03e01e80e404a221103000828a1410,0x21097807c23a02900d846412f09704b42520ef07703b45d20b705b02d4162087043021447e23e01e809c04c025103881800a31c08c04502200dc06c04302100d40680290140104080033019009c04c01d00e00fc07c031018009404801b00d004c02403d01e02bc0,0x4001704b023c01c009004001417203801580a803e01e00a825001a00c0038018004001026a0b909784b825a12905b82d816a0b10428a044be05e02e816407a039012888440c0020a6852421a10916a83441423451a084146022cd164827453226a02709280c42461,0x41020415407e03d04bc25c12d094817c4bc25d01f88f847a007103001463811808a04401b80d808604205a80d01520280608100066032013809803a01c05f80f8062030012809003601a009804807a03c05780b814602204c8260122010045802817603a01602840,0x66032013809807e03e01882c004a02400d806802601201da0ec074020410003c01c00900400e407002b055007c03c01504a0034018007003000800204d417212f09704b425205d02c80f407200600105742b21550a8832813c09a061025812412d05b02c410c0830,0x2403a010808001e00e004802007203801582a803e01e00a825001a00c0038018004001026a0b905a82c40ba05901e80e400c0020a9045822414208304082740fe07d04b81dc0ea09103981c413505b82d816a05f12f097407e23e11e801c40c00518a04402081000,0x80833419209d04c89d40e607203884f42720fd17c831418209514881b40d204601700f804403600f050c2e609b059854c2a415108b03982b20ce09b84d826a0661230ad802c015007883801a31408804102000cc06402701300fc07c031058009404801b00d004c0,0x4480a8052086009039446a21b00d006400a3530a9054428413a06281b409a12e011049803c15d0ac832818415906704f427206d02682d80440ae00f053429210d0848b541a20a113505340e413d09c83f45f20c5060825449a066017017804405600f05142821051,0x408d0c30613702180bc4e609303380bc67a13907e83e418a0c104a82440da069026812404c02200b005446a20a004881467a13907e8be418a0c104a8a444da06903280f812a06d09a82f40ca04101500a407e03e01e80481ca23510d806803200513684d41ea0bd0,0x60825452224d024817806a29505e818408a02a01481780240e511a886c0340190028a540da0f105e823405402907783b81da01207288d443601a00c80145b60c70758cf42720ff07f03f45f20c7063031418209514889b40d202e01b00d443c01d18903741062821,0xd006400a3630b98c6c25638f183893c08e0371a681c827a13907e8be458a0c104a8a4449a049033019405c02d00b015803c16508b042858c0ba1758ba85d233d09c83f41f20c5060825412206d0348134092065013008802c00a004881800a33d09c83f45f22c50,0x28cf42720fd07c8b1418209504889b40d204d02482340ca02601100581ca235105002440a35906704f427206d03481340920b6010839446a2091028d641bc0ce04a81b426a13107a83c417a0b904682240ca061022810405a02a01482d802c012008839446a21b0,0x5982c816213d09c831418206d034813409212e02f08f844c02207288d44122051ac833827a13906283040da069026812416a02601100841ca23510488146b618309f84ec1bc13d09c83f41f22c5060825452226d034813409208d032809804401607288d44140091,0x11039441220519e84e41fa0f9162830412a29113681a409a049046819404c02200b039446a20a004881458a0c103681a409a04909700d452a06d09882f411a04501500a425c01207288d443601a00c801467a13903681a409a04909682c415c01e0028d4412c12d0,0x9c83f45f22c5060825452226d034813411a065013008802c035105002440a2d51668cf42720c506081b40d204d02482d404c022010839455a2091028b1418206d034813409212600f00146ac11109584a82520850ac84f42720c506081b40d204d02482d40bc2260,0x5f02f417206703301940c2045020805802400e01e84942420e707303945c20af05702b415207d13c81540a201900681c81fc0c6046819404c01600e882801220519e84e41fa0f9162830412a29113681a409a0f1146819408c22601100581ca235105002440a33d0,0x7f03f45f20c7063031418209704b025452202f01700b404e026012807c43c01d142849c24c125090839c1cc0e517082bc15c0ad054815c4ac05502880dc46c035007803801a13d09c83f45f20c5060825452226d03484b410a05d01c805440413509883d41e20bf0,0x7c82544da02e013007c43c01d1a285042020cd06482740ea07109e8bf452222a11d009846401e19f84f827a139063831818a0c103789b84da027013009403e21e00e8d3429210d0848b541a20a50508d1453a26e025018848c25a01f094806413f09f04f42720ff0,0x1000504202e407002b055007c03c01504a0034018007001000400004f42720ff07f03f45f209514881b40d202e015089804401e00d05742b211d18c8d542a21150888b4854c0a216502781340c604b024817428e1450ac810c08205501f80f413d09c83fc1fc0fd1,0x1904f42720c7063031412a26d017009803e21e00e8c7023031408803701b030c0840b505a02a40500c102000cc06402701300740380bf01f00c416002400d806802601201e80f015e0ae0518088132098048804011603b01d00b41580a1010005c12c08f00700240,0x5a02c050808002e0960478038012008002821017203801580a803e01e00a825001a00c0038008002000027a139062830412a29103681a405c02a113008803c01a0a685242122d105285146821051808b3459209d14c89a809c24a031091848425a01f08e80a40361,0x7103fc1fc0fd163831818a09704b02544de26e03680bc05c02d013809804a01f10f007463811808a04401b80d808604205a80d01520280608100066032013809803a01c05f80f8060025012006c03401300900f40780af017028c04409904c024402008b01d80e80,0x3701a8094066031091808a05e02d00f80ac05201b04d417204501684b42520ed17482d416208514089740b2025107001827a13907e83e458a0c104a82444da06902482340ca02601100581ca235105002440a35a1a9052861c14208304f81f413217b0ca81dc1220,0x5c0a30110264130091408802c0140bb01d00b40580a1010005c12c08f007002401000504202e407002b015007c03c01504a003400e0060010004000053429210d08483541a20a505089140bc05a0a6852421a10906a834414a0a11a2850420a301066832413a0991,0x1b05542a20dd06c826c134099041027427a13907e8b1418209103681a408c02e01300d803c14d0a484342122d5068829414225a08e046022811006e036021810816a03405480a018204001980c804e02600e807017e03e01880c004a02400d806802603d01e02bc0,0xc585686a414a1a1850828212a0828b3413a27509f012826c04601f049806c1550a8844c62431116c82481041650890d142820cd04e89d41fc04a07b011807c0e601b05742b211d18c8b485960ca06482cc1640b10a2850420a30104e89d418c04a05f011807c0ae0,0x5481f44aa03500685340e413d09c83f45f22c5060825452224d02483b40b203d008881829a07202e849c24c125090839c1cc0e517082bc15c0ad05481fc0fc07d11b88d806a019007803801a14d039023405a02600b039446a20a004881467e04b04d812c06e3531,0x7c825c12c09512680bc05c02d01300782ca1121a2850419a0c904c89d40e213907c831452a26d11708e804c21a0a68514282105180833419209d04c8bf44d606a03480a847402610f0d340e413509883d41e20bd05c8234112045020805802400e07684942420ad0,0x7704881cc14d07e8b1412a24d01780b805a02600f053429210d068828460229d13501184b403e12900c827e13e09e84e418e0c6062813c49c24d013809804a01f10f00746ba15908e8c646a21150690a9828a2ce04d030812c0ba1450ac810c0aa03f04f42720fd1,0x3a84f42720ff07f03f45f20c70630314182095048811805c02601b007803a33505c819405a12d09483b45d22b5058821450223d01c809441c0060a104181cc1470a3051420c0ce04f01b808e04602280f406e23601a8d6863c1520a50d1820413a07f04c85e432a0,0x86851428210106682744d404e033011807c05601b05742b211d08c8b4858409605982c816214d0a484346122a506701c80dc0be033017815c05608284f42720c506082544da06902300b804c03600f057419c0c306103041e62f21788b4c13e093052850419a09d0,0x3a81c427a2fd16080a847402619e84e40da069026812425a0b105a84942420e513e895406a01900684e409a0b1013039446a2091028cec2c63930a98e4c22634b0ad0d4829433b09d04e425410d16a829428c07203704d80cc05e09301582ca16108903e81d414d0,0xa883381940c6061025825c08601f089840a35906704f42720c103681a409a049097017847c2e511a882440a356089050827412a07704880de26e136813c49c24d013809804a01f10f007469a149086842454234516482744d405a01f08c828a1410828c0413a0991,0x4e02601f80f80620b0012c09404801b00d004c02403b81d80e801f08f007002611200801c80e00560aa00f807802a094006803000e0060010005102056419c13509882f40ca061022810425e12e09684a40be25e12e816407e23e11e80e401c00a00300146ba1590,0x9485581b40ce06302d824c0ae0ae827452e29604a8a1c10c08503e8d341aa1450a0841460209d03501380cc04601f015806c1a30cd84ec19a13d09c83f45f209514881b40d2046017009806c01e0ac855427a29304902442260df035845022211008204001980c80,0x2e816407a03900700182a20ca061025816408608684245aa0d10508d0419a29d13501384b403e11904146020cd064827413227503884e418a29511d009858a0c103681a409a04909482d407a12d0728ab40fa25501a806401a02607288d44122051a104e825612a0,0x468228112065030811408202d014821802c01207289ec0f407900e88142ba09e04b02c810c0ae03f053420a301066832413a06a027019808c03e02b00d828a07107f83f81fa2f9063831818a0c104a8a440da06902300b804c03600f007466a0b905a82c40be25e1,0x5002440a2a504e81b826a13107a83c417a0b904682240ca062030811408404101680a407c01600903940a403301900c403a00509a84c41ea0f115e82e411a089132818408a04101680a410a05d01e839446a21d101000461a09e07f04d42620f507903c417a0b90,0x5002440a33d09c83f45f22c5060825452226d034813409208d032809804401607288d44140091028cf42720fd07c8b1418209504881b40d204d02482340ca02601100581ca235105002440a2a50a2850420a301066832413a099146819407c03a00b03944a401d1,0x62830412a09113681a409a04902280f404c02201a88280122a513b0cf42720fd17c8b1418209514889b40d4069026812411a065013008802c0e512900d44140091028e0c27e13b0528cf42720fd07c8b1418209514889b40d204d02482340ca02601100581ca2351,0x9c830412a091034813409202601a882468a14106683240ea07101f00e81ca27504b04d41ea089032810808202901f0394466032018807440a0c3055858c33634d03904f42720fd17c8b1418209514889980ca02e013008806c03510f051820c0ce04f04f42720f91,0x1100d44140091678e0c28a1410828c0413a29913a81c418c06501f00e802c0e51028b5813c13507a82e4114089030811405208600b03944f607a03c807440a11f06b8b1c16e0af1d583ec2a618b051832c27a139063831818a0c103681a404c03611a887828a13d0,0x3883f811a06501f00e813a13507a82f4112062030810405a05e00903944a6052028807440a16708b843c5fe0f7077839c6b618b0ad866c27a13907e8be452a29113681a417c02e013008815c03510f04f42720fd07c8b1418209504889b40d204d02482340ca0260,0x62830409a049046819405c02d01300880ac01e0a681c818a09503701b411a065011005824c0e7173039455c03711b00d441c009003881800a33d09c83f41f22c5060825412226d03481340920f1123089804401607288d44140091028d142820cd06482745322750,0x1f00580240e501980c806201d00284d42620f50788af417208d04489940c204502080b405208502e80f41ca23510e880800229e09a84c41ea0f105e82e411a08a04481940c204502080b405208600b00481ca27b03d01e403a205085850c29a07209e84e41fa2f91,0x28b0c09e24b01b8d5827a13907e83e458a0c104a8a444da069026812411a065013008802c0e511a88280122051828c0419a0c904e8a644ea071046819407c03a00b039443a20a004881453a07509f04d42620f507882f417208d04481940c2045021010405a0290,0x7c8b1418209514889b40d204d02482340ca02601100581ca235105002440a34519e84e41fa2f9162830412a29113681a409a049046819404c02200b039446a20a004881468a33d09c83f41f22c5060825412226d034813409208d032809804401607288d44140091,0x5089b80d408d02f016802c01d1028a9426a0f105c82340c406102080b40bc016072814c0a405100e80141fa2f9162830412a29113681a426c02e01300d443c10606702780ec13d09c83e458209113681a409a049032811407a02601a882801233f09d84f42720fd0,0x3701a80bc05a00e8a9420a0f104681880c204101681781ca253029014403a0050cb8bfc1ee14d09e84e41fa2f914a8a4449a04903280b804c022057007827a13907e83e458a0c104a8a444da06902681240ca02601100581ca235105002470614d0a484346122a50,0x46819404c022005002461a30916a834414a0a113701a811a05e02d007454a13105e82340c406102080b40bc0e502981480a201d00284f42720c5060813409202601103981ca21e09e84e41fa0f906283040da069026812404c02202a882470613f0a685241aa0d10,0x14839455a27e00e88045fe0fb059809c04600716b033826a13107a83c417a0ba05c8234112065030811408202d01482d802c0120728aac1540a900e80141fa2f9162830412a29112681240ca02e013008824c01e03b0cf42720f9162830412a29113681a409a0490,0x26812417c08d032809804401607288d44140091028d5427a13907e83e458a0c114b025412206d03481340920bd047019410402601100581ca27e01a882801220517d813c496037167032818c0c2059039443a2091028d5826a13105e82e411c08d044811408202d0,0x3801800a005003801800a0ed04280f404201105688744120b104281740220ad10e882400e006002801c00c00503681a409a049013008803c0d51668cf42720c506081b40d204d02482d404c0220728ab446a20919f84ec27a13907e83e458a0c104a8a444da0690,0x4280f4042011056887441201101b00d40da0230110084066032018806801a01102b01541a403b01d00e415a053029014415a05501a80741cc07e01b08785da0e515689f44a207d11880745cc0ae03f015806c01e007039815c0ad13f01580aa23601a807803a0050,0x7702140ba00607783b81da0b705b02d404a0ef07703b416e0b605a821800c0ee05b02180bc02500303bc1dc0ed05b021c10c08502f00fc07c03d003039815e0ae05681f80ae05602a80dc06c03500f807803a0ed05a820404a00505882140ba01105688744120ed0,0x1a801403c205002839815e0ae05681f806c01f10f007400e006002839815e0ae05689f80ac01f10f007400e006002807440a0ad002844414c09605a821804a005188829812c0ee05b017807c02600284741a401105702b440a2b6043004403c01d1028a140ba0250,0x7301f806e23611a807c43c21d07301f806c23500f087400a005003801800a00700300140aa20502b015440a00500f081403c01d00281580aa00500280d806a005082881420a04a02300d800a11d05702b400a105025011806c035002841819c09e03b013448a03d0,0xe801800a00501b88d846a00500280d800a0af05702b400a03701b00d40960630238b9815c07e02b015446c035103001403a00500f081400a01f10f087400a05702b015440a01f00f007401c0cd07e8a5445403a01308c80340c5136813411a22200b08680140160,0x280140220e607700f844c216002844412c085008801414c005002844412c086008801422209600b00440fc009003001402203701b00d400c005008807c03c01d077021807c22610280141da08100b001400c005076801800a01d00280141cc0ae05689f80ac01e0,0xf03f818c09603700b404a01e10e80140ea24e12100f840a07510280f840a00503a80f800a01d03a811c48c04511d009404403600f001422209607700f844c205040805800a00502280140940be047001403c205002827452a28d04280441cc07d002844410a03e1,0x4283980fa00507301f800a10d03301681cc056002801421c05e07301f40ac08504101f809c20501b00d400a0c706288e806c00506302580dc04e016809403a00500283f440a0fd102843800a00500e83d804a02200f007840a0fd10283f403c01d002819c0ca2220,0x33018408c0ed00e881800a0b706681d408c04511d009404401e08182fc59409b04d026417c0b31590ac44d60cf057804415a05501a807401211606f029413a095037023410a07d102819444401e05e890c08222a076816c0b405902b012815c07e01a8a7452a28d0,0x8e83480c20ae05688142060bf06902f411c06100f00741a40cd04f013419a0be02302d81a409e02682f816c11606f029413a095037023410a07d18703580ea06d03281740aa315065026811c08603f03481ea0bd02280581a40bd047823811a02d007034817a08e0,0x700181da08501e80840220ad10c80345cc0ae03f015803c00e003010405a0e5156894406201d00284140940e5156894403a241016839415a051018807400a041016839455a251018801420a04a00e890405a0e5056814406201d08e82c410a05d00882a403a20d1,0x578ab815a27e01b00c403e21e00e801c00c005020807803a04905e810402c00e03183340ea04601f00c808c04101682b400c00500b8314474036049824457c08e05982c81620ae00882b40aa03500e80240aa28b03181ec00a2e515688c403a2e605701f806c01e0,0x76820402c0151028bb4102006084835816c0ae076820402c01510300145da08100b005440c005176820402c0060028bb400c0ed040801800a2ed040801800a2ed04080145da006002881800a2ed040801800a20510300544aa24101682b815a24602080b40ac0e60,0x76821407a02100882b443a20904e8a545dc08604280f844c27d1028c4412c0ee043021407c2261028c4414c09607702d810c05e01f009802c00507683b41f606b08584282120d6057044412c0ef07703b407c2261028bb41020060028bbc1dc0ed01f089840a2151,0x3300b402c00d17f031812c06e016809403a2461828c1409404601b04741a40bd057041409404601b009818a06d017009805c21e10e89544aa22e12b015822208501f0c4412c0ee01f089840a20605882140ba01105688744120b913280b842a2ed040805800a2151,0x5b82d816a03e01300182220a604b03b816e0b605a817807c027013009400a11104b03a410a025053017442a2ed05a801811c08e03f01f80ea0c604b00f806401d14b00f805c2e605701f803c00e00301d44da22e11f09b449a02d01300680ca04601680580140890,0x882b815a21d106881412e00b002802c18e00b002801400a02e17e885462209601f0c340b405900b00145440a102a8bf453a29714b025450c08503e8d4c1f611107e88985be06b088825810a0250a9844c1d611105302581dc05d11f00546220a604b03bc1dc0ed0,0xb6043017807c02600b00145a207603303440ec06606881d80cc0d103b01980da26512a8b440cc09a04700f405405e01e809813405e01f009800a005002801400a00501682b815a21d00284741a40bd05702b403a00508e834816c0850]⟩
def parentRuns : Column := ⟨28,#[0x21c803f218803e216003d212803c20f003b20a803a207803920080381fc40371f800361f400351ef80341ec40331e880321e480311dc40301d4c02f1d3c02e1cbc02d1ca002c1c1402b1be802a1b640291b3c0281a6c0271a30026194802518f4024181802317c002216c80211654020160001f15a401e155401d14dc01c145c01b13d801a135001912c4018121c01711dc0161100015108801410100130fb00120e580110dcc0100d6800f0cd400e0c6400d0bd800c0b3400b0aa400a09d4009084c008078400706f4006063800504b4004043800302b000201dc0010108000,0x2f981422f501402f0c1382ed81352ea41302e501172e441132e341112e2410f2e1810e2e1410c2e1010a2e0c1082e081062e041042e001022dfc1002df80fa2df40f62df00f42dec0f22de80ea2dcc0e72db00de2d880d52c840d42c4c0d02c140cf2c080cb2bfc0c72bc80c62bbc0c42a900c32a340c229d40be29940b529540b128440b028080af27c00ad279809f2780092270c09026cc08d26b408c269c08a262407a25d80642590061253005e24d805c24c805a24740582460056240405223a4050238c04e232c04c231404a22c004822ac0462260042224004121f4040,0x3e641fb3df41f73d981f23d501d13d441d03ce41cb3c881c73c301bd3c1c1bc3bd41bb3bb81ba3b901b93b741b83b481b73b201b63af01b53ad01b43a701b33a481b23a1c1b139ec1b039bc1af39941ae39641ad39341ac38c01ab38b01aa38941a9386c1a8384c1a738241a637ec1a537b01a437681a337441a237141a136f41a036a019f366819e362c19d35ec19c35a819b358419a352c199350419834e819734b81963498195345819433f819333a81923340191327c190322c18f31e015631b41543194152315c150313814e30fc14c30d414a30a014830401463008144,0x4dd03114dc03064d703034d382fd4d2c2fa4d142f94cf42e64c942e34c382e14c2c2df4bd42dd4bc42db4b6c2d74b0c2d44ab42d24aa82d04a482ce4a342bb49e42b749b42b2499829f495c299492829148c428e487028c486428a480028847ec286478c282471428046f827e469027c467c27b463c27845c027645a0275459c26c4564266454825f454425d454025b4520256451c254451424e44e824b44e424944c024644942414394240435c23f430c23d41fc23c41b023b4160235414c233413c22d411022a410422840f022240ac21c3f9c21b3f6021a3f082143edc20a,0x5f444575f104555e6c4545e3c4535dec4515db844f5ca844e5c5044d5be444b5b844495a704485a084475990445592844358b4441584c436582443357f443157ec42f57b442d57a842b5754429574842756f042556e441b568c418565840b562c3f655dc3ec55d83e655d43e455d03e255cc3d655b43d155943cc55883c855803c455603ba55543b954583b854143b653143b552d03b452943b252703ad52603a952543a552303a2521839c51f439a50e439950b0398505c390504c3854fe03824f843764f443644ef035e4ee035c4ed034b4e803484e4c33f4e283254dd8322,0x6dcc5c86cbc5c76c7c5c66c145c46be05c26ba05c06b5c5be6b145bc6ab05b96a545b86a145b569d05b3698c5a869605a3690459f68b4595686c58e684858b683057867f05746798570677856c6738562670c55f66f454b66b05486668546665854465fc54165a453e656c53a64f453064ec52f64e452d64d05236484520646450b641450063e44fc63ac4f963684ec635c4e063104dd62fc4d862e84d762d84c862884bb62584b762104b461d449f61c049d61a449b6194499616c497614c495610c49360dc491609c46f6094469608c4656078461604445b5fa845a5f80459,0x7c1c7097b6c7087b087077ad46fd7a946e87a786e67a486e47a186e179e06de79c06da799c6d7797c6d479786cf79706c979686c779606c379446c179186bf79046bd78cc6bb78a46b978706b6783c6ae781c6a578106a277b469d7770680776466e772c66c76f466a76cc66876986667658664760c66275d8660759065d754c65a751065874ec65774a8653744464a74186417410640740463773fc62973e062773b46257394623735c621733061f72fc61d72dc61b72a46197280617716c616714061570cc60870885fd70345d26ffc5d06fa85ce6e985cd6e605cc6dfc5ca,0x896481e891481c890c81b88b4818885881587fc81387ec812879080f874880b86dc808868480586207fd86187fa85d07f485747f1851c7e984e87e384a47df84887dc84807d884787d6843c7d083f07cd83e87c783ac7c183647bd83507bc83487b983407b883387b683087b182d87aa82b47a5827479c826c79a8264798821c79181c478e815c78c815078a80f4786809c782804477e7ff477a7f807777f287747eb87707e9c76b7e687627e187557de873d7dd073a7d9c7377d687347d447307d2472f7d107287cfc7267ce07237cbc71c7c847187c787137c407117c2870e,0x91f8bd291f0bce91ecbba91bcbad918cb799184b72917cb699160b66913cb0d9124af9910cac59100ac290f0abf90d4abc90b4ab9909cab6906caa69034a969020a7f9004a798fe4a6f8fd8a698fb4a5e8fa8a5a8f889ed8f789e98f689a28f5499f8f4898c8f2c9768f0493a8f009218ef49058ef08ef8ee48ec8ec48d48ea88cf8e9c8b48e908958e748908e3088e8e2888d8dcc88a8d608898d508878d2c8838ce88828cd08808c688788c308728be886b8bb88678b7c85d8b508588b188568b108528aec84d8ab08498aa48428a6883c8a188398a1483389dc82f8998824,0x9560e1b9554e079550df29548dec9538de79530de3952cdda950cdd194fcdcd94f8dc894f0dbb94dcdb894c8db494c0db194bcdae94a8dab9490d9a9488d8e9478d7b9470d6d9460d5f944cd5c9448d589438d549430d509424d41941cd2e9418d1693f4d1393f0d0f93e0d0b93dcd0793d4d0493c4d0193b8ceb93accea9388ce79380ce39378cdf9374cdb9364cd79354cd39348cae9344ca89324ca59304ca192e0c8b92c8c8892c4c8492c0c8092b4c7c92a8c2892a0c249294c209290c1c9288c19927cc169270bff926cbfb9260bf79258bf39244bef9234bec921cbdd,0x99d927299bd20d999d1da99851d399651ab9949185993d17e9921176990115698ed14b98e914098e113e98c913598b912f98a912b98950d498710ba98550a2983d09f982909c980d04a97e504697e103997c103597b9034979902d979502c978cfea9774fd5974cfc19740fbe971cf6c970cf0796f0f0496e4f0196ccefe96c8efb96b4ef896a8eee96a0edd9694ed59684ec89680eb49660eb1965ceae9654eab964cea89644ea59640ea2963ce9f962ce929624e7b961ce65960ce5c95fce4c95d8e4995c4e4595bce4195b4e3d95b0e3995a4e3695a0e33957ce2c9578e1e,0x9d9dccf9d99c7b9d89b2d9d7daab9d79aa79d75a9f9d71a989d6da7d9d69a109d5d9c09d4591c9d418e49d258d59d158d19d058c29d0188e9ce18239cbd81c9c9d8149c717d09c6d7ca9c697bc9c657b69c617b29c4d7af9c2d7999c1d7819c057289c017249bed71e9be16b79bd169a9bb96969ba16929b8d68e9b8568a9b796489b756449b656409b5963c9b4d6389b456349b356249b316209b2d61c9b2959b9b255729b1556b9b055689ad155d9ac54df9ab14b99aad4a39a994929a814889a7d4869a714839a5143c9a393e99a353b59a293989a2535c9a1535599f9299,0xa0b27b6a0a67b1a09a718a08e711a086608a0825eda07a5cba072567a06e3f5a06a3e9a05a31fa0562e4a0522b1a04e26ba04a1bca04618da042169a02e165a0121609fee12e9fea1209fe20de9fde0d99fda0d49fd20a29fcdfe59fc9fb39fc5f989fc1f949fbdf829fb9f429fadf369f99f339f8df0d9f89f069f6defe9f65efa9f59ef79f51ef39f41ef29f35ef09f19eed9ee9edd9eb5ed29ea1ece9e95eca9e89e9e9e85e9b9e7de989e79e559e61e2c9e59e0d9e55e0a9e3ddfd9e31df99e2ddd99e19dd29e05dce9df1d5a9dd5d239dd1d1f9dcdd1b9dbdd189dadd14,0xa0e67e1a0ca7c3a0be7c0]⟩
def exitRuns : Column := ⟨28,#[0xfd01b00f8feb00f4fb700f0f8500ecf5300e8f2300e4ef100e0eb500dce7900d8e4900d4e1200d0de200ccdac00c8d7a00c4d4700c0d0600bcca300b8c7e00b4c1400b0bea00acb8200a8b5800a4aee00a0ac4009ca600098a3900949c9009099a008c936008890f008489d008086c007c83200787fc00747c90070788006c74d006871b00646e100606af005c64f005862b00545ab005056d004c535004850d00444a30040463003c43c003840400343dc00303a7002c370002833c00242fe0020294001c254001822900141e2001017d000c14500080de00040a1000006c,0x5094f905014e204e14ce04d54bc04c14ab045d48f044d487044547e043d475043946b04314660429462042145d04194590411454040944f040144b03e944603d944203d143c03c943703a9432039d426037941b035540e03513c503413af033d39c032d394031d38d031937c0311374030d327030930c02f92f002d52dd02c52cb02c128402bd27302b525f027d24a02492420241221023520b023120302291fb01e91db01911c701851a8017918c0171175016917001611590159152014913b0141122013911a013110101290f901210e201190db01090c401050930101052,0x7edafd07ddadd07c9ac40745aae0741aa9072da91071da7906f5a6206f1a4d06eda2906e9a1006e59fe06e19e806dd9d406d99be06d59ac06d199606cd97606c995d06c594b06c193206bd92006b990806b58f406b18df06ad8bc06a98a806a589506a187d069d86a06998570695842069182d068d81606897fb06857e306817ce067d7aa0679790067577c0671763066d74f066973e066571a06616fe065d6ee06596d406556c406516ab064d68f06496750645659064160d063d5eb05595d005515bc05495ac0541595053958505315700529560052154e051952e051151c,0xc45fd60c19fcf0c0dfb80bf5fa90be9fa20be5f9b0b99f8f0b8df750b85f5c0b7df570b75f3e0b6df370b5df200b51f070b49eee0b41ee70b39ecc0aedec20addeac0ac9e9f0a7de940a65e810a45e6b0a39e500a31e390a29e340a21e180a19e100a09df70a01dd709f9dcc09f1dae09edda409e1d8d09d9d6b09d5d5f09b1d590999d3f097dd2e0975d28096dd240959d170951d120939d08092dcf40925cef0919ce20905cd50901c8d08fdc7608f5c5d08f1c1308edbfb08d5be708cdbe008b5bd608a9bc308a1bbd0889bb50871ba1086db5a0869b490851b320829b1d,0x115e5c511565a8115255c114e5381146511113e4f5113a4ac1136488112e467112644b1122401111e3dd11163bb110e39f110637b10da35c10ce34b10c633410be32f10b631610ae30f10a62f6109e2ee10962d4106e2cc10622b4102e2a60fda2980fb22840f9a2800f9227c0f8a2760f5a2720f4625f0f3224c0f222430f1223b0eea22a0ee62230ee21db0eda1c30ed617c0ed21650eca1550eb61490ea61410e9613a0e8a1280e7211e0e6a1080e660c10e620b00e420990e160920e0a0720dda0580d920420d7a02b0d720250d2e01e0d220080cfdffa0c95fee0c89fda,0x1722b4b171eb03171aaed1712acd170aabb1702aa416faa8816f2a6f16e6a5316e2a3416d6a1c16cea0616a29f1168e9e4167e9cb16569b4163a993162e97b15e296e15d295315c293c15b292b158a919157e8ff152e8f315228d7151a8ba15128b2150689a14fa88314ea86614c284514be83e14b6838148e830148280f142e80114027e813f27d813e67c713b27b413827ad1376789136277d135e775132276b12ee75212de74212d272e127e71c1276710126e6fd12666f3125e6dd12566d3124e6be12466b211be69f11a66921196685118666e116e651116a60911665e5,0x1c270d31c230801c1f0471bf70321ba30121b9b0001b92fe21b86fcc1b7afb51b6afa11b5ef901b52f821b3ef7e1b26f7a1b1ef771b0ef741b06f641afef511af6f451aeef301ae6f221adaf0f1abaef81a96ee81a8aee21a76ec11a02ea819bae9c19b2e8519aae6f19a2e5e199ae481992e2c198ae131982e011976de5196adc81962db4195eda3194ed8a192ad681906d5a1902d5218ded4a18a6d46189ed3a1896d27188ed1b1886d06187ecf71876ce4186ecd61866cc3185ecb9185ac701856c641822c4017f6c27174ac101742bf9173abdd1736b941732b7e172ab5d,0x207b5952073578206f573206355c2057544204f52c204b525203f50d202f4f620234da20174c31ff74a81feb4a11fd34831fc74671fa744e1f8f43d1f7f4291f7341b1f634161f5b4111f433fa1f373e21f1f3de1f073cb1ef73b71ef33aa1ee73a51ee33a01edb3981ec737e1eab3661e973561e733441e6b33e1e633381e4731e1e3b3021e332e51e2b2df1e1b2c71e0b2af1dfb2981deb27c1ddf25b1dd32441dc32231daf20f1d8b1fb1d571df1cf71c31ceb1af1cdf1981cd31831cc316d1cbf15c1ca31521c9b1421c8f12f1c7311c1c631071c4f1011c470ea1c3b0d8,0x2eeb87e2eb78722de78662ddb8642dcb8632dbf8612da78602d9b8582c3784e2be78462b1783e2b0b8322aff8262af381a2ae780e2adb8042a9b7f62a5b7e829ff7e329e77dc29bf7d429a77cf297b7c6296b7c127b77b927a77b4268b7ae267f7a826337a425db79d24eb78f248778e241778b23bf78a23b3787235377f233f77822d377522577722243760223b742223773c222b7242227707221f6ff220f6e8220b6cb22036bf21e36a421cb69021af678219f6682177657216363f215b628214b62421376142127603210b5fd20f35e820e75d120cf5ce20bf5bc20935a9,0x37cb98c37b398a379f986378f984376b98337479783737973372397236ef96f36e396836d396236c796036bb95f36af959366b951363b94e35ef94935b7946357f941357393a356393935539353543932350792e34bb92b345b92a344f91e343f91d342f919341f9183413916340791233af90e33ab90a339f8fe338f8fc337f8fa336f8f9335f8f5334f8f132bb8ed32a38eb32978e132878d9322f8ca32238bc32138bb32038ba31f38b730a38b430938b230838ae30738ad30678ab305b8a72fff8a32fef8a22fdf89e2fcf89c2fbf8972fb38912f7788a2f4b8812f3b87f,0x46afabf4617ab745fbab445dbaac455baa4453ba9d452fa9d4503a9c44fba9844e7a9144d7a9144bfa8d44afa884353a8242eba79428ba70427fa6a4273a63412ba5c411ba5140e7a4e40d7a4240d3a3e40b7a3540b3a313faba2e3f57a283f07a1e3efba193db3a0d3c1fa093c13a003c079fd3bfb9f73bef9f63be39f03bbb9ed3b779eb3b579e73b239e23ad39e13ac79d93abb9d83aaf9d63aa39d43a979d23a8b9d13a7f9d03a4b9cc39ef9ca39979c839739c339339be39279b439179af39079ad38f79ab38e79aa38db9a638cf9a538b399c387b99b386f990381f98d,0x5ddfb8c5dd3b8c5dc7b8c5ca3b8c5c93b8b5c7bb855be7b815bd7b815bc7b815bb7b815babb815b9fb815b93b815adfb815a6bb7c5a5bb745a4bb6c5a3bb665a2bb645993b605983b605973b605963b605953b605943b605937b605923b605913b5f5903b5958f3b5558e3b5158d3b4e58c3b4858b3b4658a3b465893b465883b455873b445863b43566fb4355cbb4255afb3d55a3b39558bb2b5577b2a537fb2552e7b20528fb1d5283b17524bb165223b0f521bb0c520fb0750f3afa4fa7af44ed7af34e63af04d73aef4d57aeb4a67ae449cbadc4837ad5476bacd474fac7,0x6fffc126ff3c126fe7c126fdbc126fcfc126fc3c126fb7c126df7c126ddbc126cb7c126c0fc0e6befc0e6ba3c0e6b93c0e6b83c0e6b77c0e6b6bc0e6b17c0e6b07c0e6af7c0e6ae7c0e6ad7c0e6acbc0e6abfc0e6aafc0e6a9fc0d6a8fc0c6a7fc0c6a6fc0b6a63c0b6a07c0a69f7c0a69c7c0969b7c096843c09674bc056703c046507bfa6473bf963bfbf86393bf7637bbf06357bef6347beb630bbe7623bbe66223bde61e7bdd61d7bdc60ebbdc608fbdc6073bcb6053bbe5f43bb35f37bb25f2bbb25f1fbb15ef3bb15edbbb05ecbbaf5ebfba95e67b9d5e07b955defb8c,0x8597cfb8583cf384bbce98483ce8837bce68367ce58353ce48333ce2828bce27f97ce17ecfce07e63cdf7e53cde7e0bcdd7d0bcdc7cdbcd67ccfcd07c37ccb7c1bcca7bfbcb67bebcb37bdfca87bcfca67bcbc967bc3c907bb7c827b77c727b4bc647b3bc5d7b2bc597a7bc557a6fc547a63c527a57c507957c5078b3c4a7837c48782bc4777f7c4077e7c3d7767c3c774bc37773bc3276e3c2d769bc2d768bc2d767fc2d7673c2d7667c2d75ffc2d75efc2d756bc2d749fc26748fc26747fc25746fc247463c207453c1c73f3c1873afc18734bc18733fc1872efc1771efc17,0x9f03d279edbd249ec7d219c63d1e9c47d179c1fd149b03d149aebd149adfd149a73d149a63d149823d1497b7d1397a7d11973fd11972fd119697d0e960fd0e959fd0e9487d0d946fd0d93f3d0d93d7d0d93c7d0d9377d0d9367d0d9357d0d92fbd0d92efd0d92c3d0d92b7d0d91ebd0d91d7d0d91cbd0d91bbd0d91a7d0d919bd0d90f3d0d90e7d0d90d7d0d90cbd0d909fd0d908fd0d907fd0d906bd0d905bd0d904fd0d9043d0d8fd7d0d8fcbd0c8fa7d0c8f97d088f03d088ef3d088eabd088e9fd088c7fd088b93d078ac7d0689afd0588b7d0486f3d038637d0285a7d01,0x9f87d319f0fd2a]⟩
def arcs : Column := ⟨18,#[0x884021100a000270009800250009000230008800210005040131002c400a1003c400e1002400081001c401200044001010034000c10080001f00070401b10078001d00068401910070001b0006800190006000170005800150000c00021000440140004c00121004440100003c000e00034400c0002c000a0002440080001c00060001400051001000031000800010,0x158005500150005300148005100140404f00138404d00130004b00128404900120004700118004500110404300100403f101080041000f0403b100e84039100c84031100d8403510100003f000f8003d000f0003b000e00037100e80039000e04037000d80035000d00033000c80031000c0002f000b8002d000a04027100984025100b0002b000a800290009040231,0x24400440005c00901023c408e10234008c0022c008a0022400880021c00861021400841020c0082102040080101fc007e101f4007c101ec007a001e400781018400600017c0077001d80075001d00073001c80071001c0006f001b8006d001b0006b001a80069001a0006700198006500190006300188006100180005f00178005d00170005b0016800590016040570,0x32c00ca0032400c80031c00c60031400b20031000c30030800c10030000bf002f840bd002f000bb002e800b9002e000b7002d800b5102d000b3002c800b1002c000af002b800ad0021c0067002b000ab002a800a9002a000a70029800a50029000a30028800a100280009f00278009d00270409b00268009900260409700258009500250009300060008b0005c00920,0x42401080041c01060041401040040c0102004040100003fc00fe003f400fc003ec00fa003e400f8003dc00f6003d400f4003cc00f2003c400f0003bc00ee003b400ec003ac00ea003a400e80039c00e60039400e40038c00e20038400e00037c00de0037400dc0036c00da0036400d80035c00d6002c800d50011800d40034c00d20034400d00033c00ce0033400cc0,0x4c0012f004b8012d004b00129104a0412b004a80127104984129004a0012700498012300488411b00468411f00478411900460412100480411d00470412500490007800188412310488012110480011f10478011d10470011b10468011910460007810188011700458011310448411500450011110440411300448011100440010f0010c010e00434010c0042c010a0,0x5b0016b005a80169005a0016700598016500590016300588016100580015f00578015d00570015b00568015900560015700558015500550015300548415100540014f00538014d00530014b00528414900520014700518014500510014300508014100500013f001e80079001900063004f8013d004f0013b104e80139004e00137004d84135004d00133004c801310,0x69001a300688019f1067841a100680019d10670419f00678019d00670019b00668019900660019510650419700658019310648419500650019300648019100640018f00638018d00630018b00628018900620018700618018500610018300608018100600017f005f8017d005f0017b005e80179005e00177005d80175005d00173005c80171005c0016f005b8016d0,0x7380140004fc0118001ec01cd0073001cb0072801c91072001c70071801c50071001c31070801c10070001bf0044001be0011c01bb106e841bd006f001b7106d841b5106d041ad106b041b1106c041bb006e801b9006e001b7006d801b3006c841b5006d001b3106c801b1006c001af006b801ad006b001ab006a801a71069841a9006a001a51069041a70069801a50,0x7fc01fe107f401fc000900023007e001fb007e801f9007e001f7007d801f5007d001f30008c01f2107c441f01025001ef007b841ed007b000b4007ac41ea007a441e80079c41e60079441e40078c41e20074001cf007380142005040119101f040650078401e00077c01de0077401dc0076c01da0076401d80075c01d60075401d40074c01d2002cc01d10074001cf0,0x8e40238008dc0236008d40234008cc0232008c40230003a8022f008b8022d008b0022b008a80229008a0022700898022500890022300888422100880021f00878021d00870021b0086802190086002170085802150085001f40075400b500280006b0084c02120084442100083c020e00834020c1082c020a0082402080081c42061081402040080c02021080402000,0x9d8004b009d40274009cc0272009c40270009bc026e009b4026c009ac026a009a402680099c02660099402640098c02620098402600097c025e00974025c0096c025a0096402580095c02560095402540094c02520094402500093c024e00934024c0092c024a0092402480091c02460091402440090c024200874024100900023f008f8021d008f4023c008ec023a0,0x51801450046c407e10aa402a800a9c02a600a9402a400a8c02a200a8402a000a7c029e00a74029c00a6c029a00854029900a60029700a580295002d8029400a4c029200a44029000a3c01e200510014300468007d00a38028d00a30028b00a28028900a20428700a18028500a10028300a08028100a00427f009f8427d009f001c0009ec027a009e40112009e002770,0xb5c42d600b54027f00b5042d300b4801c20090002d1007e8411010b4002cf00b38004f00b3402cc00b2c02ca10b2402c800b1c02c610b14420b00b1002c300b0802c100b0042bf00af802bd10af040280009c02b800aec02ba00ae402b800adc02b600ad402b400acc02160009c02b210ac442b010abc009600ab802ad10ab002ab002dc02aa10a44029000a3c01e31,0xc0c030200c0403000079402ff00b9842e510b90409800bf802fd10bf002fb0020002fa1008c02f900be002f700860414a004740149102e442f600bd402f400bcc02f200bc402f000bbc02ee00bb402ec00bac021700ba802e900ba000b800b9c02e600b9402e400a4801e400520014700470007f00b8c02e200b8402e000b7c02de00b7442dc00b6c02da00b6402d80,0xcc4033000cbc032e00cb4032c00cac032a00878032900ca00327002e8032600c94032400c8c01e600530014b00478008100c88032100c80431f00c7842d800c74028300c7001c400c6c411400c68005300c64031800b1c431700c58031500834431410c4c031200c44431000c3c030e00c34430c00c2c030a00c24430800c1c00240008c030400c1801bf00c1403040,0xae8411210d6c005700d68035900d60435710d58031610d54435400b24035300d48020f00d44035000d3c034e00d34434c100b0002b00d24034b00c6c034a00d24034800d1c034600d14434410d0c034200d040340000ac033f10cf8433d1087c033c00268033b00ce8033900ce000bb00cdc433610c94032400c8c01e710538014d0047c408210cd4033400ccc03320,0xaa8029310cd80326107a401d110d90436310d8842ff00b9c409c00dec037a10de4037800210006610ddc402700dd8037500dd00298008844152004840151102f4437300dc8037100dc0036f00db8036d00db0036b00da8036900da0022000d9c036600d9400bc00d90036300d8801e800540014f00480008300d84036000d7c031f00d7842dc00d74028700d7001c80,0xe9003a300e8803a100e80039f00e78039d00e70037700d9c033c00ca402fa00ba8039b00e68039900e60039700abc029900a5c0222007cc01d4002f8009f001a8039600e5402cb10e50435800e4c021100e48439110e40431300e3c038e10e34038c00e2c038a10e24038800e1c4386100a0002700e0c0385009e4038400e0c038200e04038000dfc037e00df4037c1,0xf7c03de00f7403dc00f6c025b00f6803d900f6003d700f5803d500f5003d300f4803d100f4003cf00f3803cd00f3003cb00f2803c900f2003c700f1803c500f1003c300f0803c100f0003bf00ef803bd00ef003bb00ee8039b00ee4027b00ee003b700e6c03b600ed403b400ecc03b200ec403b000ebc03ae00eb403ac00eac03aa00ea403a80039c03a700e9803a50,0xfd403f400df4433710c004294007ac41560055401231021844040100c040201004040000ffc03fe00ff403fc00fec03fa00fe4022300e7403f800fdc00bf00fd803f500fd0037c007a801540054c01220021403f310d8003f200c8403f110b8003f000a2c03ef0073003ee1045803ed0016c03ec00fac03ea00fa403e800f9c03e600f9403e400f8c03e200f8403e00,0x109844250109000460108c004410004439f10894419a0055c015710308408800304404610110042310004039611088435a01084031911080441f00b34041e010740213010700030000bc04190106c03ee01068041901060041701058041511050441301048041111040440f01038040d01030002f0102c440a11024422400e78009e0102004070101804050030003f60,0xce0032700bec42e800aac0295007b001d200054012400310408a0030c4089001a000d5102480443111080441001a00440010fc043c110ec443e010f4043a110e4443c010ec043a010e4022500e7c0438010dc0436010d404340030800c1002204433010c80431010c0042b010a80429110a0442f010b8042d010b0042701098042511090442b110a84429010a004271,0x119004630117c445e11188046101180045d11170445f01178045d0117000c40030c008a1022440681116c045a0116404580115c04560113c044e01134444c1112c444a1115404540114c04520114404500112404480111c44461111444441113c444e11134044c0112c044a0112444481111c04460111404440035404430024844421110440681101403f700de043650,0x11e8447d011f00479111e0447b011e80479011e0022600e800436010d40434002c803a010898419b005600158102c84475111d04477011d80471111c0446f111b8446711198446b111a84475011d00473011c80471011c0046d011b0446f011b8046d111b0046b011a80469011a0046701198040510fdc42ab10a54433810c9c41ec10748437800d9442fb00ba044650,0x1258049501250049301248049101240040610fe042ac10a58433910ca041ed1074c437900d9842fc00ba4448f01238048b11228448d01230048911220448b01228048901220008b101a4440600fe0037910d98033900ca002fc10ba402ac00a5801ed0074c001700494008b001a4048701218048311208448501210048111200448301208048101200047f011f8047b1,0x111404b80109004b7012d804b51013c43a8108ac419c00564015d1032844b4112cc04b21011c04af112b844b1012c004ab112a844a9112a044a11128044a51129044af012b804ad012b004ab012a804a70129844a9012a004a71129804a50129004a30128804a101280049f01278049d01270049711258449511250449b0126804990126004931124844911124044970,0x137444dc1136c04da008a003a20026004d910bf444d80135c04c80131c04c601224045d0031c00c60023443a9103a840940135844d5008b441ee108b0419d00568015e1032c44d40134c04d20134404d00133c04ce0133404cc0132c04ca01324022700e8404c80131c04c601220045c0031404c50131004c31130804c10130004bf112f804bd012f004bb012e804b90,0xe8c050b01428050901228045e0032005080141c05061141405040140c0502113084501012f00500013fc04fe0112c04fd010a004fc013ec04fa1015c43ac108c8419e0056c01611033844f9113e004f71012c04f6013d404f4113cc04f2013c404f0013bc44ee013b404ec113ac04ea013a404e81139c04e60139404e41138c04e20124c04810138404e00137c04de0,0x14c0452f113b8052e014b4052c014ac052a014a445280149c05261149444970120c05240148c05220148405201147c451e01474051c0146c022a0039c009c01468051910e94037a10e90050b0142805090135c048b0117c00c900eb440960146002ad108cc419f00570016210340408c0033c451701458051501450051301448051101440050f01438050d0143002290,0x1534454c1153c054e01534054c008c003aa0152c054a01524048c011840460010dc00cc015200547015180545015100543015084503115040540014fc44c0115104543115080503015044540114fc04c0014f8053d014f00451014ec042c014e80538014e4405310ea8423010680015f0057c40cc114e84539014e04053014dc0536014d40534114cc0532013d005311,0x15b0456b015a8405b015a40568014cc4567113c84566114cc0567013c805660159405640156c455a1126c04850158c05620158405600157c055e01574055c0156445581156c055a01564055800268455610ce8423100eac05570152c054a01524048d0118800cd00eac409a01558033a008c441a10058001601033445550155045540154c05520153c454e1154405500,0x123c046501190043800348009e01604040700ebc42351068c01640059040d211600057f015f0457b115f8057d015e84579115f0057b015e80579008d003ae015e00577015d8048e0118c00d1015d00573015c84507115d40545015c444c4115d04573115c80507015c404c4015c0056f015b80457015b40430015b0056a015ac405b10eb842341068801630058c40d11,0xc0801bf000304478010e405970109000d600ee8423c107d8023a1090041fa016584007006900165005a440da114dc4591115a405950165005930164804f61164045370164404f601640049f0121c058f01638058d01630058b01628058901620058511610458701618058311608458501610058301608009e116044407108d403af015e00577015d805570136044d80,0x146c050c0136804c9016e005b70111405b60029440701103003f900e18036800d00032a00c2402eb00acc029a008f441f7008ec41f5007580241107ec05b5116d005b30075800210049800a1001b005b2016c405b0016bc05ae016b405ac016ac05aa016a405a80169c05a60169405a40168c05a20168445a00167c059e01674059c0166c459a016640598008d803b00,0x178405e00177c05de0177405dc0176c05da0176405d80175c05d60175405d40174c05d20174405d00173c05ce0173405cc1172c05ca0172405c80171c05c60171405c40170c05c21170405c0016fc05be016f405bc016ec041000ff442bc00a80434400cb841fe00768437e00db0430300c0402ef10c1805ba016e442ef11608057901494051011560054c0139004cd1,0xc2842ec00ad0029b007e001d70008c012700288006d0181806050181046030180806010180005ff117f805fd017f005fb017e805f9017e005f7117d805f5017d005ac117cc05f2016a005a701698023700ec40481017c404dc111e4043a0035c03bb1087441a500598016a1036c45f0017bc05ee017b405ec017ac05ea017a405e80179c05e60179405e40178c05e20,0x188c06220188406200187c061e01874061c0186c461a1186406180185c06160185406140184c06120184406100183c060e01834060c0182c060a0104403fe10af402a110d14032f107fc41db10ec8037f00db4430400bc04583015e805260144445590153404e511338451c0143404930182406080181c04dd1136c04ca0029840711103403fa00e1c036900d04032b0,0x16bc464a019240648017c805a90191c06460191446440190c06420190445a0119000598008e003b500e0403b3009ec0279018fc0010111e8043b018f804280036003be10ad8024410ae8000a006980167005b440df118f4063c018ec063a018e40638018dc0636118d40634118cc0632118c40630018bc062e018b4062c018ac062a118a406280189c06260189446240,0xcc842020077843b600e0803b400e00037010c1c02f310ee4038501968065901960437011610057b014a4051411568054e013a004d111474050e0138804cb0195c06560112c0655002a440741103803fb00e28036a00d08032c00c3402ed00adc02b500a7001fc0076002bb01950065300a700025004a000a3001b806520194406500193c064e01934064c0192c05f70,0xefc429e0091441a7005a0016e10380468c01a2c068a01a24068801a1c068601a14068401a0c068201a040680019fc067e019f4067c019ec067a019e40678019dc0676019d40674019cc0672019c40670019bc066e019b4066c019ac066a019a406681199c06660199406640198c06620198406601197c05ca11978465d0197005bc0196c04140100442c000a90434c0,0x153c04e911348449701a78069d01a70052011478050f0138c04cc002a840751103c03fc00e2c436b00d0c032d00c3842ee00ae0029f00a740246107f401d90009c012900290006f01a6c069a01a64069811a5c069601810069511a5045fe01a4c069201a44069001938468f01a3805f8116c0464a019240648017cc05aa008e4039b0120c068d0147c447b010f000d90,0x1b2c06ca11b2406c811b1c06c611b1406c411b0c06c201b0406c001afc06be01af446bc11aec06ba01ae406b80189406b701ad846b511ad006b301ac806b101ac006af01ab846ad01ab046ab01aa806a901aa006a701a9806a501a90061901a8c06a201a8406a001a7c04150100842c110a94434d00ccc42031077c438300dc4430800bd04585015f0052a11454455b0,0xdb8034800d18033000c2c42f100af802a20080001dc00d2c06db01b680330000a4012a0029c007201b6406d801a38464b11b5c06d601b5405f5116b4468e0192c05f5016b406d401b4c06d21190846d11167046d20190806d10167003471090803bc00c6c400e111f0043d01b40042c0037003bc10d1c024210c6c000e006a0016b005ac40dc11b3c06ce11b3406cc0,0x1bb806ed01bb006eb01ba806e901ba006e701b9806e501b9046e31198846e211b8446e01171046df11b9006e30198806e201b8406e00171006df0104843ff10af842a210d20434610cc0420010770438800db8430b00bc4434b11b6c46da10cc04586015f4052711448455c0154004e61133c45270144804e60133c06de01b74045101b7000a7101c8441200ffc03881,0x1a5c470211c0c060211c04470011a5c070201808070101c0006ff01bf8068f1193046d701b5806d5017d845ae11a3c064c017d805ae0090c03bd0121406fd01bf006fb01578047d010f800dd00ef44243106a4016c005b040dd11be046f711be806f901bd046f311bc846f111ba846e911bb846ed11be006f701bd806f501bd006f301bc006ef11bc806f101bc046ef0,0x1884071401c4c071201c44071001c3c070e01c34070c01c2c04131100042bf10a8c434910cc4420110774438900dbc430c00bc84587015f805281144c449b01c28070901c20070701c18055f0157405510139c44d0114a005130139c04d00037800a8101cc441301000038910dbc034900cc4030c10bc802bf00a8c020100774002b004ac00de102a0007301c1407040,0x1918072a0169004171091c03c000fb84013111f8043f01ca4043000384041700f00424710fb80013006a8016f005bc40e111c84472011ca0072701c98072501aec471d11c70471b11c90072301c88071a11c64471811c5c470c11c2c462111c50471311c48471111c40470f11c84072001c7c071e01aec071d01c70071b01c68071901c58071511c60071701c5847150,0xbd4441b11cc447301100c4588015fc052b1145845640154804ea1134c452b0145804ea0134c073401ccc045701cc800ab101d8441801058040300e30437200d38033400c3c42f500b0802a60081001e00106c073101cc00403000b4012c002ac007601cbc072e01cb406911193c46fe01b6005f9116c446910193c05f9016c4072b11918472c01b4c072a11690472b0,0x5c040e211d34474c11d3c074e01d24474811d1c474611cfc473e11d0c474211d34074c01d2c074a01d24074801d14074411d1c074601d14474401d0c074201d04074001cfc073e01ce84739119a8473811cf4073c01b98073b01cdc473611740473511ce80739019a8073801cdc07360174007350106044161100c42c210a98434e10cd0420410780438c00dc8430f0,0x14b04517115940553013ac44d4114b00517013ac04d4002b0407711064040400e34437300d3c033500c4042f600b0c02a700924420500784002f004b400ac001dc069b11d48470501d4c060611d44469b01d48060601d44072f01cb8072d01a48465011bfc06d9017e845b211a480650017e805b20092003c10121c075001628047f0110000e200f044248106ac01700,0x1ca0077101dc0076f01db8076d01d944764118a4476311d88476111d80475f11d60475711d70475b11b0c076c01dac076a01da4076801d9c076601d94076401d78075d118a4076301d88076101d80075f01d78475d01d70075b01d68075901d60075701064440410b0c42a710d3c433510924020510784438d00dcc431000bd8449f01d58075501d50058b0162405800,0x1e2c078a01e24078811e1c078601e14078401e0c078201e04078001dfc075701cf806c601a0c470b01ba406340179c469f019b80651019b4060a0174c077e01df4077c016f0059801dec024a00f08077a01de4077800b70452d01ddc077601dd404bc012800466003c403e310aa0026411dd0477301dc841c0006b0017100614410511b0c476c11dac476a11da447681,0x1e8c41c2006b80173005cc40f311e8807a101e80079f11e78079d01e70079b11e68479101e40078f01d60073f01b1c468411c3006ea018d445e81186405fe01e64079801e5c079601a80066f0182c05d40092c031301e5443c400e3843c3013b80794012840467003c803e41082c07930099842061099441ad005c8018610418479201e44079001e3c078e01e34078c0,0x1ec8424e0081c024d00f2004f001ecc04a3011a400f400f20420d01ec8024e1081c424d106bc0174005d040f411ec407b001ec047af01eb807ab11dfc47ad01eb007ab01dfc075901d0006a4119c0470d01bac060c1175446a4019c0060c0175407aa01ea407a801700059a01e9c024c00f1c07a501e9047a30070847a6012f804a2011a000f300f1c424c11e9447a40,0x179446a6019c8060e0175c07c701f1807c501710059c01f10025100f2407c300b6047c20130004a4011a800f500f84426211f0447c001efc41c4006c001750060c410311ef807bd01e7047ba11ef007bb01ee4079c01ee807b801ee447b811ec407b001ec0475a01d0406a5119c4470e01bb0061d0180007b701ed807b501ed0060d1175846a5019c4060d01758020d1,0x1f6407d811f4007cf01f38075c01d0c06c511a0846210180807d701f5807d501f50071101c00071001bb806331179846a7019cc060f01760031601f4c43541094803ca013c807d20155004ec11294046b003d803e21083c07d100d400263106c4017600610410411f4007cf01f3807cd01f3007cb11f2807c911eb007c801e0c075b01d0806c401a04470f01bb406320,0xc4402c51095041b3005f00178103e047f101fc007ef01fb807ed01fb007ca01fac477f11fa8078701d74074401ab0067811c5406ef018a805dd11aa006740184005d901fa407e801f9c05ca0168007e60094c03cb01f94027f11f9004c201298046c003dc03cf1095c47e311f8807e11072001b2005dc017b103ec47e001f7c07de11f7447dc01ef007db11e7807da0,0x3e403e51099c48051201008031073001b4005e401871041c48020200407a01200047de01ffc07fe11ff447f111fbc47f011e7007fc01ee0079201d78074501aa4467511c5806f001894060401fec07fa01fe407f80184445da11ab8469411ab40679018ac05de0096c021101fdc07f61096003d100e4043d0013d007f50129c046d003f003cc10b1c07f401fcc07f20,0x95803ce013d80820012a4046f003e802130207c03e6109a041b5005e8018810420481e02074081c0206c081a0206447ed0206008170205807cc0205408140204c47ae02048481102040078b01d7c074601b20068511c5c06f1018d805e911aa806760184805db0203c080e0203405d001690080c0095403cd0202c080a0202402e01202008070201804c4012a0046e0,0x1abc067a020cc0832020c40662019080830018b005df0097003d2020bc082e020b4031f120b00503012a80470003f403e7120ac0283009c041b6005f40189104244802120a847e0020a407be020a047a20209c082602078081d0207007d811ee4462901818082502090082302088076001d1c06c911a18471801bc80637117a846ab019dc061301770031902084441f1,0x21184845120f0083b020e8079e0211007d901d94074901b2c468811aec06970210c084202104084001c6806f4018e445ec11ac0067b018b405e000d60083f1097403d3014cc083e014bc44ab011c400fe00fa042c9020f40352009c441b7005f8018a10428483c020ec083a020e40838020dc4836020d407ca120d0078301d90074801b28068711c6406f3018e045eb1,0x216403d610e4403d51097c41b90060001801040048580215c08571215808550215008360214c47871214c078701d98074a01ac4467c11c7806f5018b845e111ac4067c02148085102140066601910084f018b805e10097803d402134084c1212c0287121380505012b00472003fc03d412134484c0212c42870097841b8005fc017f103fc484a0212408480211c47de0,0x18c005e30098003d70219c0866021940360121900507012b804740040403eb1218c028b009d041ba00604018d1043448620218408480218007a01217c48580215c085711ff447a00217c07fd01d9c074b01afc069902178085d02170085b01ac8467d11c7c06f6018bc45e211ac8067d018bc05e200b2c48591097c03d600e4443d5014d4085a012b404730040002cb0,0x21e00877021d8076901d3406cf11a30472101be0063d117c046b401a000652019fc0631017900396021d4426100f600537021d00530112bc04750040802cd021cc041d00fb042a9009d441bb00608018e104384872021c40870021bc4855021b80838021b407ed121b0078b01da0074c01b38068b11c8006f7018f045ef11acc067e021ac086a021a4066a0191808680,0x1db4074e01b30468911c8c070301c8806f90221c08860221406e601b4c0884018e845ed11b300689018e805ed00d584880021fc487e00c84427200fa405550220c0882022040545012c004760042c03e910d580880121fc087e10c840272106f0018b0062c410b12188087d12128087c02008087b121c80871021c0084511ff847a2021e8082601e6846c301a6c08790,0x223807e01225c47dc12128089801f80089701f70072801c1408960225408940224c076e01d3c06cd11a28472401be8063b117b846cd01a28063b017b8035a12244427300fa80569022480592012c4047700430035a0224403ea109cc41bd00630018c1043048900223c088e02234088b0223048381222808891222007cc12234488c0222c48380222848890222047cc0,0x232c08ca12324089e0232008c70231848c50231008c30230848c10230008af022fc48be022f408bc022ec08ad022e808b9022e008b7022d848b5122d008b3022c848b11009008b0022bc48ae0002448ad122b008ab022a808a9022a008a70229808a50229008a30228808a102280089f02278089d0110c000302270489b102c400b002268089912128489812240088f0,0x241849050241009031240849010240008ff023f848fd023f008e8023ec48fa023e408f8023dc08f6023d408f4023cc08f2023c448f0123bc08ee023b448ec123ac08ea1009008e9023a048e702398089f1239448e40238c08e20232808e11238008df0237848dd1237008db0236808d90236008d70235808d50235008d30234848d11234048cf0233808cd1233040280,0x25040940024fc093e024f4093c124ec493a024e40938124dc4030024d80935024d00933024c80931024700930124bc092e024b4492c124ac092a024a409280249c09260249409240248c091a12488492102480091f12478402802474091c1246c001202468091902460091702458491512450091302448491112440090f02438090d02430090b0242809090242009071,0x2484097102464497002414096f025b8096d023bc096c02390496b0233c496a0231c0969022d04968022b00967002c4096602594018f02590096302588096102580095f02578095d02570095b025680959025600957025580955025500953025480951023b049500239848d41253c08c612538094d024d4094c0252c494a1252409480251c49461251409440250c09420,0x9e009aa026a409a8125ec09a70269804360269409a40268c09a20268409a00267c099e02674099c0266c099a1266409981265c09961265409941264c09921264409901263c00c212638498d12630098b02628098902620098712618098502610098312608098102600097f025f8019b025f4097c025ec097a025e40978025dc0976025d40974024e80973024cc09720,0x277849dd0277009db0276849d90276009d70275809d50000009d41274c09d20005809d11274009cf1273809cd1273009cb1272809c91272009c71271800461271440d41271009c30270809c10270009bf026f809bd026f009bb026e809b9026e009b7002bc09b6126d449b4122680006025940005104c049b3026c809b100b4009b0026bc09ae125f009ad026b009ab0,0x28340a0c0282c0a0a028240a080281c0a06028140966028100a03004c00a02028040a00027fc09fe027f409fc027ec09fa027e409f8027dc09f60226809f5027d009f3027c849f1125dc49ee027bc09f0027b44899127b049ef127b84191025dc0977127b409ec0226409eb127a849eb027a809e9027a009e70279809e50279009e3026ac09e20278409570278009df0,0x29280a49029200a47029180a45029100a43029080a41029000a3f028f80a3d028f00a3b028e80a39028e00a37028d80a35028d00a33028c80a31028c00a2f028b80a2d028b00a2b028a80a29028a00a27028980a25028900a23028880a210288009f60287c0a1e028740a1c0286c0a1a028640a180285c0a16028540a140284c0191028480966028440a100283c0a0e0,0x2a04098d02a000a7f029f80a7d029f00a7b029e80a79029e00a77029984a56127cc0a760298c0a75029d00a73029c80a71029c00a6f029b80a6d029b00a6b022700a6a027bc0a69029a00a67029980a65029900a63029880a61029800a5f129780a5d029700a5b1226c09ee029680a59029600a57029580a55029500a53029480a51029400a4f029380a4d029300a4b0,0x2aec0aba02ae40ab802adc0ab602ad40ab402acc0ab202ac40ab002abc0aae02ab40aac02aac0aaa02aa40aa802a040aa702a980aa502a3c0aa402a8c0aa202a840aa002a7c0a9e02a740a9c02a6c0a9a02a640a9802a5c0a9602a540a9402a4c0a9202a4409e902a4009e802a3c09ed0274c0a8e02a340a8c02a2c0a8a02a240a8802a1c0a8602a140a8402a0c0a820,0x29684af30296049f402bc80af102bc00a9a027b84a591288409ea02bbc0aee02bb40aec02bac0aea02ba40ae802b9c0ae602b940ae402b8c0ae202b840ae002b7c0ade02b740adc02b6c0ada02b640ad802b5c0ad602b540ad402b4c0ad202b440ad002b3c0ace02b340acc02b2c0aca02b240ac802b1c0ac602b140ac402b0c0ac202b040ac002afc0abe02af40abc0,0x2c700b1b02c680b1902c600b1702c580b1502c200af50031000c302634089d02c500003027b04b1302c480b1102bfc0b1002c3c0b0e02c340b0c02c2c0b0a02c240b0802c1c4a6912c180a671295c49f502c140b0402c0c0aa2027bc4a68128a409eb103a80b0202c040b0002a780a25027a84aff02bf80afd02bf00afb02be80af902be00af702bd80af5029a84af41,0x2d500b5302d480b5102d400b4f02d380b4d02d300b4b02d280b4902d200b4702d180b4502d100b4302d080b4102d000b3f02cf80b3d02cf00b3b02ce80b3902ce00b3702c100b3602cd40b3402c040b3302cc80b3102bc40b3000350044302cbc0b2e02cb40b2c02cac0b2a02ca40b2802c9c0b2602c940b24001180b14027b44b2302c880b2102c800b1f02c780b1d0,0x2d280afe02b5c0a3d02df00b4802b540a62128ec0b7b02d180ad3029904a3902de80b7302de40b7802ddc0b0e029ac4b7602dd40b740296c09ee02dcc0b7202dc40b7002bf40a7012dbc0b6e02db40a5f027bc0b6c02dac0b6a02da40b6802d9c0b0902d980b6502d900b6302be809f002d880b6102d800b5f02d780b5d02d700b5b02d680b5902d600b5702d580b550,0x2e380195000900b8d02e3001f212e2c400910be40b8a0064c001802e240003002404b8802e1c41900000c409002e1c0b8602d880b1302bbc0a5502e140b6002bb40a5302e100b5e02c480aeb029440b8302d700ae90293c0b8202d680ae7029cc4a4d02e040b6b02d600ae50292c0b8002d580ae3029240b7f02d500ae1029d44a4702df80b4e02b6c0a4102df40b6a0,0x2ee40bb802edc497902ed80bb502ed00bb302ec80bb102ea00bb002ebc039a00e640bae02eb40bac02eac0baa025e00ba902ea00ba702e980ba502e900ba302e880ba102e800b9f12e780b9d02e700b9b12e680b9902e600b9702e580977002c400b0028480977025d80b95025d0003002e500b930102c4b921102c0b9200664002802e440b900004802b212e3c43760,0x2fa40bab02e60039a02fa00be7006500be602f940be412f8c0be202f840be002f7c4bde02f740bdc02f6c0bda12f6441a502f600bd7025fc0bd602f544bb712ea80b9702f500bd302f480bd102f404bcf02f380bcd02f300bcb02f284bc902f200bc702f18096702f140b9602f10019202f0c0bb602f080bc102f000bbf02ea40bbe02ef44bbc10870021b02eec0bba0,0x30680bf0030644c180305c0bc9030580c1503050096b02ee80c1302ee00b9a008700c12030440192130400c0f030380c0d130300c0b030280c09130204bde0301c01a7030180c05026040c040300c4b99030080c01030000bff02ff80bfd02ff00bfb02fe80bf912fe00bf702fd80bf502fd00bf302fc80bf112fc00bef12fb80bed02f1c0bec02fac0bea025a40bad0,0x30c84c49131200c0c0311c0c4602f880c450311001a90310c0c42026140c41031000b9d030fc0c3e030f44c3c030ec4c1d030e80bf4030e40bcb030e0096d030dc0b9c030d80196030d40c34030284c33030c80c3102f804c30130bc0c2e030b441a5030b00c2b0260c0c2a030a44b9b030a00c27030980c25030900c23030884c21030800c1f030780c1d030704c1b0,0x31bc0c6e02ef44ba1031b44c56031b00c3e031ac4c25031a80bfc031a40bd3031a009720319c0ba0031980198031940c64030384c63131300c6202f900c61131804c5f130bc0c5e0317441a7031700c5b0261c0c5a031644baf131600bbc02e7c0c57031580c55030f00c54130840c5302fe00c5202f3c0c51025c00c5002e780c4f006504c4e031340c4c1312c4c4a0,0x325c0c96132544c96032540c940324c0c920323c4c8e132440c90032344c8c1323c0c8e032340c8c0322c0c8a032240c8b032280c89032200c87032180c85032000c7f031f84c7d132100c83032080c81031f00c7b031e84c79132004c7f131f80c7d031f04c7b131e80c79031944c78131380c77030d44c76131d40c10031d00c7302f980c72006ac0c71031c009890,0x330c0cc2033040cc0032fc0cbe032f40cba132e44cbc032ec0cb8132dc4cba032e40cb8032dc0cb6032d40cb2132c44cb4032cc0cb0132bc4cb2032c40cb0032bc0ca2032b80cad032b00cab032a04ca7132984caa032a40ca5132904ca3132a00ca7032980ca5032900ca3032880ca1032800c9f032780c9b132684c9d032700c99132604c9b032680c9903260019b0,0x33c00c99033bc0cee133b40cec033ac0cea033a40ce8032340cea033a40ce8032300ce7033980ce5033900ce3033880ce1133800cdf033780cdd033700cdb033680cd9133600cd7133580cd5033500cd3033480cd1031e40cce133344cd00333c0cca133244cc81331c4cc0132fc4cc41330c4cce033340ccc0332c0cca033240cc6033144cc80331c0cc6133140cc40,0x34880d21033f00d201347c4d1e133d80d1d0347041a70346c0d1a0326c0d19034604d17034580d15034500ceb0323c0d16034540d14032380d13034480d11034400d0f034380d0d134300d0b034280d09034200d07034180d05133804d041340c0d02033500d01034000cff031f40cfe033f40cfc133ec0cfa033e40cf8033dc4cf6033d40cf4133cc4cf2106940cf10,0x33b40c93035040d40034fc0c92034f44d10134f80d2a034f04ce4134f40d10034f00ce4034ec0c85034e80d39034884d37134e00d36133e84d35134d04d22034dc0d36033e80d35034d001a9034cc0d32032740d31034c00d2f034b80d2d034b00c91034b80d2d034b00c90034ac0d2a034a44d08134a04cdc134a40d08034a00cdc0349c0c81034980d25034900d231,0x35740ca2035840d600357c0d5e035740d5c0356c0d5a035640d540354c0d52135444d580355c0d56035540d500353c0d4e135344d541354c4d52035440d501353c4d4e035340ca1032500ca0032b80c9703530018f034984d49135204d3a0352c0d4a033f84d47135184d26035240d48033f80d470351801ab035140d440327c0d43035080d41035000d3f034bc0ced1,0x36380d8d036300c7d0362c0d8a036244d880361c0d86036140d841360c0d82036044d64036000d7f135f80d7d035ec0d7a035e40c99035f00cee132940c95032900d7b035e80d79035e00d77035d84d75035d00d73035c84d71035c00d6f035b80d4d0328c0d6d035b00d6b031e40d6a035a40d66135944d680359c0d641358c4d66035940d640358c0d620357c0d5e0,0x36484db1036c00daf135cc4db4136cc4db2036480db1136c04daf035cc0dae036b40dac035540ca9036ac0daa036a40c81036a00da7036980da5136900da3036240da2136844da01360c0d9f036780d66036740d9c136680d99036600d7d0326c0d9b034604ca8032580ca7036680d99036600d97036580d95136500d93036480d91135d44d90035bc0d8f035440ca60,0x35840c9f037480d42032b00dd1037400dcf037340dcc0372c4d96137380db5037284d77137344dcc1372c0d96037280d77037240d59032ac0dc80371c0dc6032140dc5037100da41370c4d87137084da40370c0d87037080d68037040dc0036fc0dbb036e80db9032740dbe034c00caa036f40dbc136f00dbb036e80db9035800db8036dc0db6036d40db4036cc0db21,0x37e44df8037dc0df6037d40df4137cc0df2037c40df0037bc0dee037b00deb037a80d64037b40d7f132e00dec037ac0dea037a40de80379c0de6037944de40378c0de2037840de00377c4dde037740ddc0376c0d4d033c00cf1006480cb7036a04dd6137140dda037640dd80375c0d8b137544da8037580d8b037540d6a037500dd3037440dd00373c0dbf035f84d7e0,0x37000d62032f00e1b038680e19038600e17038584dff138544de0138580dff038540de0038500d55034c80d33006580cbb0384c0e12038440e101383c0e0e037e40e0d138304df30382c0e07038180e05037b80d66038280d9c132e80e09038200e07038180e05038100e03038084e01038000dff037f84de4137f40ddc037f00d51034680d1b006500cb9037ec0dfa0,0x38c80e31033500cbf0384c4e2f138940e30037ec4e2e1384c0e2f037ec0e2e038b00e2b038a80e1f037bc4def035a80e2d0374c0cbe038b00e2b038a80e281380c4e290385c0e27137a04e280380c0e27037a00e26035640d44035140198032f40e25038900e0f138884e23037dc4e21138804e0f038880df7038840e200387c0e1b038680e19035a00e1e038740e1c0,0x39800e5f038e80e5e037780e5d035c40e5c0396c0e5a033600cc1039640e580395c0e56139540e540394c0e52139444e4c0392c0e4a037cc0e500360c0e4f033d80e4e034704cf2133000e4d039300e4b039280e49039200e47039180e45039100e43139080e41039000e3f038f80e3d038f00e3b038e80e08038e40e38038dc0ddc036780e36038d40e34035bc0e330,0x39ec0e7a039e40df7039f80e200361c0e7d036f00d81133e80e7c034d00cc4039ec0e7a039e40e78039dc0e76139d40e74139800e73038f80e72037800e71035cc0e70033700cc3039bc0e6e0394c4e6b139b40e6c039a80e53039ac0e69039a84e69139940e64039904df5039a00d850399c0cf8039980cf3033cc4cc2039940e64039904e63039880e5f138e84e610,0x37a00ea203a840ea0035dc0e9f03a780e9d033900cc703a700e9b0395c4e9a13a140e9903a604e9713a484e9013a444e5303a580e69039340df903a540e0c136240e94033f00e93033d00d1e133180e9203a440e9003a3c0e8e03a340e7503a304e3a13a2c0e4203a280de403a240d7503a200ce0033140e8703a180e8513a104e83039b40e82139540e8103a000e7f1,0x34d80cca03b200ec703b180ec503b100ec313b080ec1039d44ec0038f80ebf037fc0ebe036480ebd034200cc903a704ebc13a1c0ebb039bc0eba139640eb903ae00eb403acc0eb2039fc4e6a137ec0eb70362c0eb6033f80eb5035180cc803ad00eb303ac80eb103ac00eaf13a380eae03ab40eac039dc0eab03aa80ea9139880ea813a9c0ea6039180ea503a900ea30,0x34400ccd03b900ee303b400ee20395c4ee113b740edc03b704e971395c0ee103a5c0e1103b800da603b7c0d2403b780d1f0347c4ccc03b740edc03b704edb03b680ed903b080ed8139084ed8039080ed7038040ed6036500ed503b500ed3034300ccb03b480ed103b400ecf13a140ece13b344ec803b1c0ec6039540ecc03a000e0f03b2c0da403b280da0134880ec90,0x3c084ec403c044f0003bfc4e770388c0efe03bf40efc0385c0dbd03bec0efa03be40db5035280d3803be00ef703bd80d2a0333c0ee403bd44ed203bd00e9c03bcc4eee03bb40eec03b344e98139640ef203ae00e511384c0ef1038240da803bc00da1134980eef035200cce03bb80eed03bb00eeb13b680eea03b100ee903a384ee8039180ee70380c0ee6036580ee50,0x3ca00f2713c984bd203c940f2413c8c4f2203c840f2013c7c4f1e03c740f1c13c6c4f1a03c640f1803c5c0f1603c540f1403c4c0f1203c444f1012f380f0f03c384f0d13b484f0c13c1c0f0603c140e8713c2c4e8313b480f0c03a1c0f0b03a0c0e2503c280dc503c240dd7034e80f08033400f0703c180f0503c100f0203c0c4ec413c040f0013bfc0e7713c104f030,0x3d884f6103d80021a03d7c4f5e03d740f5c03d6c4f5a03d644f5813d5c4f56000180c12000144f5513d500f5303d480f2713c444f5103d400f4f03d380f4d03d300f4b03d280f4903d200f4703d180f4503d100f4303d080f4103d000f3f03cf80f3d03cf04f3b13ce84f3903ce00f3703cd84f3503cd00f3313cc84f3103cc00f2f03cb80f2d13cb00f2b03ca80f290,0x3e700f9b13e684f9903e600f9713e580f9503e500f9313e484f9103e400f8f00088000003e384f8d03e300f8b13e280f8913e200f8713e180f8513e100f8313e08023f13e04024013e004f7f13df80f7d03df00f7b03de84f79116a00f7803ddc4f7603dd44f7403dcc4f7203dc44f7003dbc4f6e03db44f6c03dac0f6a008f04f6913da04f6703d980f6503d900f630,0x3f3c0fce03f340fcc03f2c0fca03d580fc903f200fc703f180fc513f100fc303efc4fbc03f080fc213f040fc003f004fbf03ef80fbd03ef44fbc13eec0fba13ee44fba03ee40a5b03ee00a5b13ee04fb703ed80fb503ed00fb313ec80fb103ec00faf13eb80fad03eb00fab13ea80fa903ea00fa703e980fa503e900fa303e880fa103e804f9f13e780f9d109b04bdd0,0x40281009040200fca0401c10060401410040400c100204004100003ffc0ffe03ff40ffc03fec0ffa03fe40ff803fdc0ff603fd40ff403fcc0ff203fc40ff003fbc0bbb030440fee03fb40fec03fac0fea03fa40fe803f9c0fe603f940fe403f8c0fe203f840c1103f800fdf03f780fdd03f700fdb004e00fda03f640fd803f5c0fd603f540fd403f4c0fd203f440fd00,0x41080ffa0295c104104100103f040f8103d03fe00a5b13ee04fc2040f0103b040e81039040e01037040d81035140d05033040c85031040c0102f040b80a5f040b40a6b040b0502b040a81029040a0102704098102504090102304088102104080101f04078101d04070101b04068101904060101704058101504050101304048101104040100f04038100d04030100b0,0x41b4102e13f240fb912980106c041ac106a041a410680419c10660419410640418c10620418410600417c105e04174105c0416c105a0416410580415c10560415410540411c1002041381053041481051041400b0e041180a5f140b450000413c104e022b4104104134104c0412c104a0412410480411c104604114102c03f180fb80296809b1029640b730411010430,0x429810a50429010a30428810a104280109f04278109d04270109b0426810990426010550425c105104258109504250109304248104304244103f04240108f04238108d04230108b0422810890422010780421c10860421410840420c108204168108104200107f041f8107d041f0107b041e81079041e00f6d041dc1076041d41074041cc1072041c41070041bc106e0,0x436c10da0436410d8040bc4fba10870021b03d580a610435c10d60435410d40434c10d20434410d00433c10ce0433410cc0432c10ca0432410c8008f40f6d008ec10c704318104b0431410c40002410c30430810c10430010bf042f810bd042f010bb042e810b9042e010b7042d810b5042d010b3042c810b1042c010af042b810ad042b010ab042a810a9042a010a70,0x4440110f04438110d04430110b04428110904420110704418110504410110304408023f016d411010440010ff043f81056043f41052043f010fb043e810f9043e01044043dc1040043d810f5043d010f3043c810f1043c010ef043b810ed043b010eb043a810e9043a002400431010e70439810e50439010e30438810e10438010c5016d410df0437810dd0437000090,0x4498113e044f4113c043281041040d40fcb03ef8113b03ef40a62044e8110904298100f03ef05130044e41138044dc1136044d41134044cc1132044c41057041340fbb044c0112f044b8112d044b0112b044a81129044a0112704498105304130112504490112304488112104480111f04478111d04470111b0446811190446011170445811150445011130444811110,0x299411590456011570451411320455811550455011280433c104e040d01153040c80fd003ef00a6404548114f0445c10b4040f0501d045441115042c8101b04540114f04508114e04534114c02dcc103a1452c114a045240fc20298c1148045041111042b810170451c11450451811400449c110f042b00fc2140ec50150451411440450c1142045041140044fc11310,0x4608118104600117f045f8117d045f0116c045ec117a045e45178145dc1176145d41174145cc4bec045c8117112c405170045bc0018045b8116d045b0116b045a8116912fa8000312c4051680456411300449410c3040ac1167045981165045901163045881161045801144044d810d40457c10d30457810ba041fc106c04574115c0413c0fd50456c0fd4045684fbf1,0x46d011b3046c811b10456011b0046bc51ae046b411ac046ac51aa046a451a812fbc11a70469851a51082811a40009011a30468851a1046800009145604bed0467c119e04674119c0466c119a0466411980465c065a0465811950465000120464c1192045b41191040c4039a00e641190029c8118f04638118d04630118b0462811890462011870461811850461011830,0x47ac11ea047a451e81479c4bf70479811e51479051e30478811e10478011df0477851dd0477011c30476c51da0476411d80475c11d60475411d40474c11d20474411d00473c11ce0473451cc1472c11ca047244bf30472011c71471851c50009011c40470c51c201fd051c1147005194146fc4bf1046f80fb3046f411bc046ec11ba146e411b80468811b7146d811b50,0x48881221148804bff0487c121e14874403004870121b048680bfd048641218047fc121714858121504850521314848121104840120f04838120d04830520b048281209048201207147f4520604814520412fec1203048085201100a01200047fc51fe0004811fd047f04bf9047ec51fa047e411f8147dc51f6047d411f4147cc51f2047c411f0047bc11ee047b411ec0,0x4958125504950125304948125102784125004834124f047f0124e0474c124d0470011ab0493011a0045f8124b045bc124a0492412480491c12460491412440490c1242049041240048fc123e048f4123c048ec123a048e41238048dc1236048d41234048cc1176148c811691486c1231048c0522f148b8122d048b0522b148a81229048a012270489812250489012230,0x4a2c528a14a24128804a1c528614a14002604a10128304a08000004a045280049fc127e149f4127c149ec527a149e41278049dc464a049d81275049d05273149c81271049c0126f149b8526d049b0526b049a81269004d45268100180c4f00014526714998126504990126304988126104980125f04978125d0497011da0496c11c5149681259046141258045c012570,0x4af452bc04aec12ba04ae412b81450c12b704ad812b504ad012b304ac852b11306412b004abc52ae1009012ad04ab052ab0002451431305c12aa04aa412a804a9c12a604a9412a404a8c12a204a8412a004a7c129e04a74129104a70129b04a68529914a60129714a58129513058129404a4c4afc10060129204360129104a40128f04a384c140000c4afc14a34128c0,0x4bdc52f6100a012f504bd052f30004812f20308812f104bc012ef14bb852ed04bb012eb14ba852e904ba012e704b9812e504b9012e304b8812e104b8052df1308012de04b7452dc14b6c12da04b6412d814b5c12d604b5452d414b4c12d204b4412d004b3c52ce04b3412cc14b2c12ca04b2412c814b1c4c1c04b1812c514b1052c304b0812c104b0052bf04af812ac0,0x4cb8132d04cb0132b04ca8132904ca0132704a64532604a38530d04c94132414c8c532204c84132014c7c531e04c74131c04c6c131a04c64131804c5c131604c54531414c4c1312130a0131104c40530f100c0130e04c34130c03098130b04c2812f404c24530804c1c130614c14530404c0c130204c04130004bfc12fe04bf412fc04bc852fb14be812f91309012f80,0x4d88536104d80135f04164400004d78135d04d70535b04d68535904d60135704d58135514d50535314d481351016a0135014d3c005204d3844dd04d34534c030a409ae14d2c134a04d24134804d1c133004d18134504d10134304d08134104d00133f104e0400602f10000514cf8533d04cf0133b04ce8133904ce0133704cd8133504cd0133304cc8133114cc0132f0,0x4e64539804e5c139604e54539414e4c139204e44539004e3c138e04e34538c100180c3600014538b14e28138904e20138704e18138504e10138304e08138104e00137f04df8137d04df0137b04de8137904de05377100c0137604dd40c3f00a08137404dcc137204d241371030b4137004dbc136e14db4136c04dac136a14da4536804d9c136600088136504d9013630,0x4f3c13ce04f3413cc04f2c13ca04f2413c804f1c13c604f1453c404f0c13c204f0413c004ee853bf14ed453be14ef4402404ef013bb04ee813b913150002404ee013b704ed853b5100244c5204ed013b304ec853b114ec0002a04ebc53ae14eb413ac04eac13aa0000013a914ea013a704e9853a514e9013a314e8853a114e80139f14e78139d01b5c139c04e6c539a1,0x50080f5410ee014011500013ff14ff813fd04ff013fb1000013fa009ec13f904fe013f704fd853f514fd013f304fc853f104fc053ef04fb853ed03d4c53ec04fac53ea04fa453e814f9c53e604f9413e41192813e300ed413e204f8413e004f7c13de04f7453dc04f6c13da03d48439804f6413d804f5c13d604f5453d414f4c5190000180be80001453d214f4413d00,0x50e01437050d81435050d01346050cc143202f9c1431050c009e2050bc142e004d4142d050b0142b050a81429050a0142705098142505090142305088142105080141f04640141e05074141c0506c141a1494814190506001cb0505c141611ab81415150500c5f0504c14120504454101503c140e05034540c1502c00260502814090502014071501814051501014031,0x51d41474051cc1472051c41470051bc146e051b4146c051ac146a051a414680519c14660519414640518c14620518414600517c145e05174145c0516c145a0516414580507c145705158145505150145305148145105140144f05138144d05130144b05128144905120144705118144505110144305108144105100143f02eb80be7050f8143d050f0143b050e814390,0x525014980525c1496051380a6a05254149402468148c0524c14920524414900523c148e05220147e1506c148d040b40a69026ac0a6805230148b05228148902bf414880521c144a029ac102c15200148605214148515210503a15210148305208148215204503a05204148014644547f14644147f029c0147e029c0547e151f4147c051ec147a051e41478051dc14760,0x531c14a60279414c60531414c40530c14c20530414c0052fc14be052f413ea052f014bb052e814b9052e014b7052d814b5051fc141e040c00299029c414b4052cc14b2052c414b0052bc14ae052b414ac052ac14aa052a414a80529c14a604a0814a50529014a30528814a105280149f05278149d0523c148904958149505270149b052681499029c0147e051480b730,0x540815010540014ff053f814fd053f014fb053e814f9053e014f7053d814f5053d014f3053c814f1053c014ef053b814ed053b014eb053a814e9053a014e70539814e50539014e30538814e10538014df0537814dd0537014db0526814da0536414d80525c14d70535814d50522814d40534c14d20534414d00533c14ce0533414cc04d1c14cb052f414ca0532414c80,0x54c81531054c003b801968152f054b8152d054b0149b054ac152a054a41498054a0152705498148b0549415240548c15220548415200547c151e05474134805470151b05468151905460027b0541809e60545c15160545415140544c15120544415100543c150e05434150c0542c150a00ed813ea00ed015090542015070524c11970541812570004815050541015030,0x5584153b053ac1463040d455600557c12f205578155d05570155b05428149d052301480155681420040d05559040cc0a73055601198052f815570436c155605160155505550155305548155105540154f05538154d05530154b05528154905520154705518154505510154305508154105500153f054f8153d054f0153b054e81539054e01537054d81535054d015330,0x55d8154f053fc1477055d4156d0553414fd052001475055d0154b053ec1473055b411fd055cc114f055801564055c81571055c0150e052941495055bc1483055b8148215090103c029d4156d03c9c156c0557c1562055ac156a055a4150d0529014940520455680559c156604d241423040ec0a74055941560055901563054fc14ef040e814810519c11420557c15620,0x15ae156b415ac056ac15aa156a455a81569c15a61569455a41568c55a201cbc15a105680559f15678559d05670559b05668159905660559715658159515650559305648159105640158f05638558d100180c6600014558c1562c158a0562415880561c15860561415840560c1582056041580055fc157e055f4157c055ec157a055e45578155dc155505414147d0,0x11380a7f0577015db1576855d91355015d80575c55d6100a005230575455d40227815d3035480a7d1574815d10574015cf1573815cd056f015cc1572c15ca0572415c80571c15c60571415c40112015c30570855c11354015c0056fc4a79156f815bd1009004e0056f055bb029dc089f156e84d4e056e4002e056e055b7156d815b5056d055b3156c815b1056c015af0,0x580c16000580416020116815fe0580456001357015ff057fc55fe100c0058e057f415fc0356815fb057e815f8157dc55ed057e415f6157d455f8057dc15f6057d415f0057c415f4057cc15f20115015ee057c455f01356015ef057bc55ee100b00562057b415ec01bf415eb0355815ea057a415d5057a055e70579815e51579055e30578815e10578015df0577815dd0,0x2a385630058bc162e02c88098c0262c162d058b0162b058a81629058a0162705898562505890162305888162105880161f05878561d05870561b058681619058605617058581615003540b220024856140584c161205830160d05844160f05840160e0583c560e15828160d158304d5f0582c160b1582855fd0582416061581456080581c16041580c56060581416040,0x268049d60599c16661599416640598c16620598416600597c165e15974165c0596c165a0596416580595c16561595416541594c16520594416500593c164e15874564d15930164b15854164a0592400c40030c098d05920164705918164505910164305908164105900163f058f8163d058f0163b058e81639058e01637058d81635058d01633058c8163102a98499b0,0x5a6c0abc02a4c099c15a68169905a60169705a58169505a50169315a48169105a40168f05a38168d05a30168b05a28168905a201687058f0163b05a18568512ad849a102a44563415a10163315a0c168205a041680159fc167e059f4167c059ec567a059e41678159dc1676159d41674159cc1672159c45670159bc09da059b8566d159b0566b059a80608059a456680,0x5b5816d505b5016d305b4816d105b4016cf05b3816cd05b3016cb05b2816c905b2016c705b1816c505b1016c305b0856c105b0056bf05af856bd05af056bb05ae856b905ae056b705ad816b505ad016b315ac816b1059a416b015abc16ae05ab416ac05aac568515aa816a905aa016a705a9816a505a9016a305a8816a105a80169f0109c169e02688169d05a0c169c0,0x5c34570c05c2c570a15c24570805c1c5706159e8170505c10570302778170215c04570015bfc069d05bf856fd0276016fc05bec56fa0267416f905be016f705bd816f505bd016f315bc816f105bc016ef05bb816ed05bb016eb1597456ea15ba416e80594416e705b9816e51589456e415b8c16e21586416e105b8016df05b7816dd05b7016db05b6816d905b6016d70,0x5ce8099f15ce4571715ce0173705cd8173505cd0173305cc8573105cc0172f05cb8172d010ac172c05cac171505ca8172902b080a9702678572805c9c172605c94172405c8c172205c84169605a54172015c7c571e05c74171c05c6c168e15a34571a05c6416440590c171815c5c4ab9126900a92158e05716058dc571505c50171305c48171115c40170f05a00170e1,0x5dcc577205964177105dbc177015884577115dc0176f15884176e05db4176c05dac176a05da4176805d9c576605d94576405d8c576205d84176005d7c175e05d74175c05d6c575a05d64175805d5c175605d54175405d4c175205d44175005d3c574e05d34574c05d2c574a15d24574805d1c574605d14574405d0c16fe05d08574105d00173f15cf8573d05cf0173b0,0x5e404abf1268c0a95159005791058fc579005e3c178e05c40578b15e34178c05e285789159f8578815e1c578615c40178b05e281789059f8178805e1c178602770577e15df4577c15e14178401c24070805e0c178205e04178005dfc0a9402770177e05df4177c02a50577b05de8177905de0177705dd8177515bb8577405dcc177215964577715dd8577505bb817741,0x5e8c17a215ec817b105ec017ad15eb0578205ebc17ae05eac57aa15eb417ac05eac17aa02a58179c15e4057a905ea017a715e9817a505e9017a315e8817a105e80179f05e78042f05e740a9615e70179005e6c179a02afc0a950268c579905e60179705e58172405c8c179515e50569205a44179315e48572415c8c579505e50169215a44579305e481640058fc17911,0x5f4017cf05f38177805f2817c905f20566115f3457cc15f2c16f605f2857c915f20166105f1c17c505f18562915f1c57c605f14562905f0857c115f1017c305ef857bd15ef057bb15ed057b315ee057b715f0817c105f0017bf05ef817bd05ee817b915ef017bb05ee857b905ee017b705ed817b505ed017b305ea457a815e8457a015e9457a415e7c579e15e9c17a61,0x5e64179805fa017e705a68169905f9057e315ca0572715f9817e505a68569915f9017e305920164705f8857e112b1449a502a60564815f88164715f84171415f7457dc15f6c578f05f8017df05f78168215f6857d915f60571405f7417dc05f6c168205f6817d905f6009e015f5057d315f4857d701d5417d605f5409e005f5017d305f4817d105f3417cc05f2c56f61,0x602818070601858090602018071601818050601018030600818010600017f815fdc57f015fbc57f415fcc57ee15fb457f605fd457f205fc457d605ffc17fc15fec57fe05ff417fa15fe457fc05fec17fa05fe417eb15f8457f805fdc17f615fd417f405fcc17f215fc417f005fbc17ee05fb4043305fb017eb05f8417ea05fa40ac502a6009a515ca0172705f9857e51,0x607c57ea05f44172a05ec8179b05e1416b705a70166b15ca856b715a70566b0592809a70607c164a16078181d16074181c0606c181a0606418180606458181605018120604c57e905ca417810605c177f05a6c172915a6c564901c2418160605418141604c181215924580f16038581106040180b16028580916020580116000580516010580f06038180d06030180b0,0x611006530610c1842061045840060fc183e060f4183c160ec183a060e41838060dc1836060d45834060cc1832060c45830060bc182e060b4182c016e4582b016e0182a060a41828016cc182702b6c16820609817d905d6817bc05b341768159e04b4e02ba44b5c160940ad50600c175405ed8167c06090167205d50567212d200ad512d2058230608818210608009a71,0x61ac186a01cc01869061a018571619c583f1619858570619c183f0619818650619058640618c186206184584c16180583216184184c06180183206174585c11b68585f01b78185e06174185c01b68185b06168185906160585706158184106154583b06150185306148185106140184f16138184d06130184b160d0584a060b818490612006581611c06570611818450,0x625018930624818910594018900623c188e06234188c0000c188b0622858891622018870621818851002418840620c188206204188005934187f061f8187d0000c187c061ec587a161e41878061dc18761616c5872161a41875061d018730610c58711616c18720610c1871061bc5850161c01862061b85836161bc1850061b81836061ac586a11cc0586d01cd0186c0,0x63005489126c80808062fc18be062f418bc062ec5047135f80777062e818b9062e018b712bf4148802c385046135f418b6062d418b4062cc18b2062c418b0062bc18ae062b418ac062ac103d0521c18aa062a4188e062a018a71525858a6135ec18a50629058a31628818a106280589f06278189d06270589b1626818990009004910626018970006006080625818950,0x639418e40638c18e20000c18e10638058df1637818dd0637018db1150418da0630c18d9063604d8102bf858d70635818d50635018d31634818d10634018cf0633818cd1633058cb06328044915730044700088103e04d3818c9059b858bc016e0001602be40af2026cc504a1632018c712de458c606314566702c0858c40630c0449059a415bc062ec18b70630858c11,0x6460191706458191506450191306448191106440190f06438104206434190c0642c190a0526450501366819090642058e41641c19061641419040640c5902164041900063fc58fe100a00495063f418fc063ec001801a7418fa163e40012063e018f7063d816e7063d418f4063cc0003063c818f1163c058ef063b818ed063b058eb063a818e9063a018e705b9018e60,0x2c4c0da101510193b06480193a12c480da0064e45938164cc1937064d81935136780b11164d01933064c81931064c0592f164b8192d064b0592b1113c55e8011340026064a819290524819280649c0b7206498192505c0846570005819240527059230648816fc02c3449ad02c1459210113c16fe0575419200647c591e06474505306470591b1646858b8126b059190,0x659c1966065945964100b004990658c59621659419640658c196206578195f06584001801c24070806580195c0657c595e136b8195d06574595c1656c195a0656419580655c19560655419540654c19520654419500653c194e06534194c0652c194a05dc419490652019470000c194606050194506510194316508594106500193f064f84574064f41921064d0593c1,0x6678599d136e0199c06670599b11654199a0659c1999066601997060680db606658199506650199306648599106640198f16638598d06630198b066281989066201987066181985066105983136d01982066045980165fc197e065f4197c165ec197a065e41978165dc1976065d41974065cc1972065c41970065bc196e165b44db1065b0196b165a85969065a059680,0x671059c3011541782057b419c21670819c10670019bf066f80b6302d8c59bd066f019b9166e059bb066e819b7166d859b9066e019b7066d819af066c019b5066d019b3066d059b3166c819b1066b419b0166bc4dbb066b819ae166b459ac066ac59ab066a819a90669859a5166a019a70669059a31669819a50669019a306674199e0668819a10607019a00667c199b0,0x373419e9067a059e7100c0049d0679059e31679819e50678859e11679019e30678819e10677c19e00006007550677c59de0677419dc0676c19da0676417c70676019d70675800030675419d41674c59d20674419d00673c59ce0673419cc1672c4455057e40453000a819ca1672459cc0672c19ca0672419c616714577e1672019c701b7800160671019c606714177e0,0x684c1a150685017d40684c445b05f5815fd068481a110415c1a100683c1a0e0683418bd162f41057168301a0b068281a07168185a09068201a05168105a07068181a05068101054067fc1a020680c1a02168041a00067f419ff141504dd1067f819fe167f459fc067ec19fa067e459f8067dc19f6167d459f4067cc19f2067c419f0067bc19ee067b419ec067ac59ea1,0x171c1a36068d41a34068cc1a320555c5a311378c1a30068bc5a2e166b01a2d068b01a2d168b05a2b068a81a27168985a29068a01a25168905a27068981a25068901a1e041601a1f0688c1a220608c1a21068801a1c0687c5a1e141604dda068741a1d16870445b058240459000b81a19168605a1b068681a17168585a19068601a17068581a151685057d411cd000160,0x69c01a6f169b81a6d069b01a6b069a81a69169a01a67069980306069941a64058541a63069881a61069801a5f069781a5d055605a5c137b01a5b069685a59169601a57069581a55169501a53069485a51169401a4f0693805cd069345a4c0692c1a4a169241a480691c1a46169144de7069101a43169085a41069001a3f168f85a3d068f01a3b168e85a39068e01a370,0x6a6c5a9a06a641a680090410ec007ec5a6516a601a9706a58161d06a541a9406a4c5a9206a441a9006a3c5a8e16a341a8c059a8049104d481361059b85a8b06a281a8906a201a8713de00f8d0599c1a86008f40f6d008ec1a8506a101a8306a081a8106a001a7f069f81a7d069f01a7b069e81a79069e01a77069d81350069d410ec03db00f6b069d01a73069c81a710,0x6b3c5ace16b3406a206b30136806b2c5aca16a341ac906b204f9106b1c1ac6042884f79141805ac506b101ac306b081ac106b001abf16af81abd06af01abb06ae81ab906ae01ab716ad81ab506ad01ab306a905ab206ac41ab0059441aaf16ab81aad16998135504d501aac06aac1aaa06aa41aa806a9c1aa606a945aa406a8c1aa206a841aa006a7c5a9e06a741a9c0,0x59641afb16be81af9169a81af806bdc1ad116bd81af506bd01af30186c5af206bc41af016bbc5aee13de80f9306ba85aed16a3c1aec06bac536a06ba81ae916ba01ae706b981ae506b801adf06b785ab616b901ae306b881ae106b805adf16b781ab606b681ad916b601a6816b741adc06b6c165506b685ad906b605a6806b5c1ad606b541ad416b4c1ad206b441ad01,0x6cb01b2b16ca81b2916ca01b2706c98135906c941b2416c8c1b220427c4f7b0417c5a8116c841a8016c801b1f06c781b1d16c705b1b06c681b1906c605af516c5c5b1606c545ad306c501b1306c481b1101c4c1b1006c3c136c06c385b0d16c305a9106c2c1b0a06c240f9506c201b0706c181b0506c101b0306c081b0116c001aff16b841afe06ae81afd06a805afc0,0x6da05b6706d981b6506d901b6306d881b6106d805b5f06d781b5d16d701b1006d6c1b5a06d641b5806d5c1b5606d545b5416d4c5b5206d445b5016d3c5b4e06d345b4c06c905b4b06d281b4916d205b4706d181b4516d105b4306d081b4106d001b3f16cf85b3d06cf01b3b16ce81b3906ce01b3716cd81b3506cd01b3306c80059f06cc81b3106cc01b2f06cb81b2d0,0x69f05b9906e601b9706b545b9616c741b9506e5006b616e4c5b9206e445b9016e3c5b8e06e345b8c16bc81b8b06e285b8903e5c1b8816e1c5b8616a4c1b8506e105b8304d68136e06e081b8116e001b7f06df81b7d06df01b7b06c001b7a16ad85b7906af81b7806a705b77059741b7616dd41b74169b81b7306dc85b7106dc01b6f06db85b6d06db05b6b16da85b690,0x6f381bcd06f305bcb06f285bc906f205bc716f185bc506f10535c16f0c1b9d16f081bc106f001bbf16ef81bbd06ef05bbb16ee81bb906ee01bb706ed85bb516ed01bb306ec81bb106ec01baf06eb85bad06eb01bab06ea81b990168c1ba906ea01ba706e981ba506cb41b2c06e901ba306e885ba106e801b9f04d6c1b9e06e745b9c06e6c109c13df0105e169f45b9a0,0x6a541c03070080f99070041c00041845bff06ff81bfd16df81bfc06fec1bfa06c101bf906fe01bf716b941bf616fd41bf406b081bf306fc81bf106aa05bf006fbc1bee059841bed16fb01beb169c81bea06fa41be806f9c1be606f941be406f8c5be206f845be006f7c5bde06f741bdc06f6c1bda06f641bd806f5c5bd606f541b8d06f501bd306f481bd106f401bcf0,0x70cc1c320630818c1070c41c30070bc1c2e070b45c2c070ac1c2a070a45c281709c1c260112456b00111c182a070944441170901c23011041c22070841c200707c5c1e070741c1c0706c5c1a070640616070601c17070581c15070501c13070485c11137c81c100703c5c0e16e605c0d16c7c1c0c06be05c0b170281ad7070241c080701c0762070181370070145c041,0x71a41c680719c1c66071941c640718c5c62071841c35071801c5f017f41c5e071741c5c0716c1c5a071641c580715c1c56071541c541714c1c520714418c4171401c4f071381c4d071301c4b071281c49171201c47071185c45071101c43071081c41171001c3f019741c3e052801c3d052781c3c1528c1c3b070e80658170e41c38070dc1c26070d81c35070d006530,0x72985ca5072901ca307288583b072841ca00727c1c9e072741c9c0726c1c9a072645c980725c5c96072545c940724c1c92072441c900723c1c8e072345c8c0722c1c8a072241c880721c1c86072141c84070fc1c83072085c81072005c7f071f85c7d171f05c7b071e81c3c171e41c78171dc1c76071d41c74171cc1c72071c45c70171bc1c6e071b41c6c071ac5c6a1,0x72941cd2073441cd0060fc1ccf073381ccd0630c5ccc0732c1cca173241cc8172c85cc70710c1cc601b841cc5073101cc301b685cc2070a81cc10730006da072fc1cbe0728c5cbb172e45cba172f41cbc0728c1cbb072e81cb9060f41cb8072dc1cb6072d41cb4171041cb3072c805c2172c41cb0072bc1cae072b405b9172b01c28072ac1caa016cc1ca9072a01ca70,0x72a41cfc073ec1cfa0610c1cf9073e05ce2073dc1ccb073d85cb5173d41c47073d00737073cc1cf2073c40730173c01c2e073bc1cee01cc01ced073b01ca7173ac5cea173a45cd5073a01ca30739c1841073981ce5073905ce3073881ce1073241ce0172bc5cdf071141cde019801cdd073701cdb0194c5cda070b01cd90736006580735c1cd6073545cd4172f41cd31,0x748c1d22074845d200747c1d1e074741d1c0746c1d1a074645a9c074605d17074581a6600ee4151a00e141d15074501d13074481619074441d10074185d0f074381d0d074301d0b17428429f0381c1d09074205d0717418002401fe85d0501fd054b9146504dfe017f41d040009007980740c14b8074084dfd074045cbf074001c9a073b45cff1735c1cfe072fc1cfd1,0x75381d4d075301d4b075281d49075201d4707518127607514151a04fa413e8075101d43075081d41075001d3f16a901d3e074801d3d069b802bb174545d3c058941d3b074e81d39074e01d37174d85d35074d01d33174c856ff012541d31074c013e604ff81702174bc1d2e074b41d2c149d4128005bf01d2b074a81d2904f8c1272049c41d280749c1d26074941d240,0x75d45d74075cc1b941188c1d72075c41d5d175c05d6f075b81d6d075b01d6b175a85d69149dc128706e085d68174cc1d670759853f5050341b88075941d640758c1d62075845d600757c1d5e075741d5c16b3406170721006150756c5d5a075641d580537c13f4052a8140a06b2c5d57174c41d5607554528406b1c1d541754c1d5200ed813ea00ed01d51075401d4f0,0x767c1d9e076745abe1767c5d9e176741abe076641d981765c1d20176701d9b0766816f2076645d980765c5d20076581d95076505d93176481d91075c85d901763c1d8e17634071c076301d5f0762c1d8a0503c1d89176205d350761c1d8604a241d85076101d83076081d81176001d7f075f81d7d16c005d7c06ae81d7b075e81d79075005d7805bb81d77074701d760,0x75d05dc81771c076b077181d63077141dc40504c1dc3177085d39077041dc004a341dbf076f81dbd076f05da3076ec1d82076e85b7e176e41ac2076e01db7076d81d42176d416f6076d01d24076cc1db2076c406bd176501db0075841daf176b85dad175bc1dac04a2c1da8176ac5d37076a81da914fd81411076a01da7076981da5076901da3076881da1076801d800,0x77b0191c0646c1deb077a81de9077a01de7177985de5077901de317788444f15d08044d061181de1077801ddf111045dde077740441077701ddb076f41d8e175d85d6404fe01d53074ec1279077681d2a077641dd80775c1dd6077541dd4075d41d5a0774c1d590185c1c19070fc1dd2077441dd0075481dcf074e81dce177341dcc174a41db31772c5dca076581dc90,0x78501e13016e45e12077881e110784005b30783c05ce069581b8d078105e0e078341e0c0782c1e06178285e0917820512704dc8591e0728c1e07078181e05078041126178101e03078081e01078001dff077f81dfd077f01dfb177e81df9077e01df7077d81df5077d005be070f81df3077c805b91647c1df1077801265044ac5df0044a8512f177bc1dee116cc1ded0,0x78f41e3c078981e3b177e85e3a078e41e15078e01e37019605e36077981e35078d00653078cc1e32078c41e30173541e2f172941e2e078b41857078b01e2b078a81920178a41e280789c5e26178941e181789006e40788c1e22077d81e210788006da1787c1de4078781e1d01b681e0d078301e1c0786c1e1a017381bd4017305cdd078641e180785c5df4178581e150,0x797c0e18079785e46079741e41179705ced0796c1e5a1729c5e59079181e58178cc1e57073b41e561783c5ca9079541e540794c185b079481921149981130179445e3e179401e280793c1e1a17938073a079341e4c077f81e4b079280730179241de8079201e4701cc01e46079141e31079101ca71790c5e0e1729c1e43078381859079081e41079001e3f078f806681,0x79f0139f04ebc1b0e179ec5e74079e81e7914e7413ab06c201e78079dc1e76179d45784012641e74179cc5e76079d41e74079cc139c14ea0577e179c81e7104e7013a805df8139804e5c1e70079bc1e6e079b45d40079b05aa0079ac1d1c079a81a6a00d2c5e69079a016210799c1e66179981e620798c1e65079901e600798c5e621386c1e61079845e60100c008950,0x7a781e9d07a705d8217a6c1e9a07a645b0417a785e9d17a701d8207a6c5e9a17a641b0404e805e9507a505e93079b85e9807a5c1e9605de013a007a545e9407a4c5e6e07a481e9107a401e8f1763406b907a101e8e17a345e8c07a2c5e8007a2813b2076245e7607a241e8814e7813ad076141e8707a181e8507a105e8306c44061f07a081e8117a001e7f079f85e7d1,0x7aec5ebf07af81ebd07af01ebb07ae81eb807ae41eb707ae05eb717ad81eb617ad41eb417ad01eb307ac81eb017abc470707ac41eae17ab45eb007abc1eae07ab41ea807aa41eac07aac15f307aa81eab17aa85960060581ea607aa45ea8138781ea707a9c5ea617a485ea317a94077007a901e8617a885e9207a8c1e8607a8813b417a7c5e7807a841ea004ed01e9f0,0x7b6c1eda17b681ed907b601ed617b5459c0066fc1ed7060541ed417b4c5ed607b541ed407b4c0b6602d941ec617b145ed207b441ed007b3c1ece07b341ecc17b2c445505eb80453061781eca07b241ec817b1c5ece17b345ecc07b2c1eca17b245ec807b1c0b6907b0c1ec4111044b6617b180b6517b140b6917b101ec3111041ec207b041ebf17af85ec007af45ebc1,0x7bfc1efc07bec5efe07bf41efc17bec1efa07be41ef807bdc1ef607bd41ef407ba85ee917b885ee117b985ee517b805edf17ba01ee717b901ee317bcc1ef207bc41ef007bbc5eee15ebc1783060541eed07bb05eeb17bc05eef07bb81eed17bb01eeb07b741edc17b145eea07ba41ee817b9c1ee607b941ee417b8c1ee207b841ee007b7c06fd07b781edd17b701ec50,0x7c301f1e07c741f1c07c6c5f1a017201b5b017181cc507c645f1807c5c1f1607c541f14016e45f1307b1c1f1207c4405b307c401f0f017201a3d06c401f09078b41f0e17c341f0c07c2c19c207be81eda07aec18d912da80b6b172f41f0a07c241f0807bdc1f0417c0c5f0707c181f0507c005eff17bf85efd17bd45ef417be85ef917be05f0407c0c1f0207c041f000,0x7cfc073d07cf81f3c17c705f3d07cb01f3c07c701f3a17ce4473017cec1ecf07ce81f3901cc01f3807cdc1f3607cd45f3407cdc5f3617cd41f3417cc01f0607b6c1ec007ccc1f3207cc40b6c07cc04b6c17cbc1f2e07cb41f2c07cac5f2a019901e2307ca41f1a17ca01f2707c581f2607c94065817c901ecb07c8c1f220194c1cd707c841f2007c7c1f0e17bf81f0d0,0x7d5c5f5a07d641f5617d545f5807d5c1f5607d5415a1156b457d417d501f5307d485f520568415ad05f50159b056681f5107d405d4207d3c1e6e07d385aa807d341d2407d301a720106c5f4b07d28162907d1c1f4807d241f4507d205f47138b01f4607d185f45178cc5f4417ce01cd717d0c5f0f178cc1f440735c1f4307c3c186907d081f4107d001a1207cf45f2c1,0x7de45f7a07d945f7817ddc5f7207de41f6507de01f77056d85e9f17d681f7607dd415b607a7c1dc701b041f7407dcc5f7207dc41f6707dc05f6f07db85f6d17d841f6c07dac55b80770c5f5807da81f691568815b2076fc1f680701c062707d9c5f6607d941f6407d8c1f6217d841f6007d7c1f5e17d7455a3056d01c0517d581f5c07d6c55b00700417d7012741f581,0x7e741f7f07e701f9b0194c1f9a07e6405d2073cc1f9807e5c1f9617e541f9407e4c1f9207e441f9017e3c1f8e07e341f8c07e2c05b917e281f7d044d45f89044d0513917e201f87116cc1a100683c1f8607e141f7c1116c17ff01164186c07e081f8107e005f7f17e101f8307df85f7d17e085f8117e001f7f07df81f7d07dec444117df01f7b011041ea501c981f721,0x7f201fc707f181fc5077381fc407f0c1fc207f041fc006abc1fbf07ef81fbd07ef01fbb07ee81fb907ee0193507edc1fb607ed41fb417ecc1fb207ec41fb017ebc1fae01ba01f3e07eb45fa317eb05f9117eb41fa307eb01f9107ea45fa811b685fab07ea81f8307ea41fa801b681fa7019b01e4d07e985fa507e901fa307e881f9517e841fa007e341f9f07e7806581,0x38e4200007ffc5ffe17ff41ffc000481ffb07fe81ff907fe01ff707fd81ff507fd01ff307fc81dd207fc41ff007fbc1ab507fb81fed07fb01feb064d81fea07fa41fe807f9c1fe607f941fe407f8c1fe207f841fe007f7c1fde07f745fdc07f6c1fda07f645fd807f5c1fd607f541fd407f4c1fd207f441fd007f3c5fce17f344e3607f301fcb13e741fca000241fc90,0x80d86035080d02033080c82031080c01938180bc202e080b4202c180ac4e41080a82029180a0602708098202508090602308088202108080201f08078201d08070201b080682019080602017080586015138f420140804c60121804420100803c200e18034200c0802c200a0802440280185c1c1a01854002401a8820080801c19370801820050801020031800820011,0x81bc206e081b4606c181ac206a081a460681819c1dd9081982065081902063081882061064e460600817c205e08174605c0816c4e490816820591816060100815c2056081541dd70391c20541814c20520814420501813c204e08134604c1812c204a0812420480811c20460811420440810c2042181044e4508100203f180f8603d080f0203b180e86039080e020371,0x45144e5302048209b082686099145640e510826420980825c20960825460941824c2092082446090116f8002601974002205574208f08238208d06b2c608c0822c1156182282089182201ac70821c20860821420840820c208207968208118200207f081f8207d181f0207b081e82079044e82078081dc2076081d40b7b055d46074139302073081c84b82181c460701,0x830c1aea0830820c1083001e05182f05f08082fc20be082f41e05082f020bb082e81561082e020b9060940b7c0558460b81399420b7082dc4b7c182d820b5082c860b1182d020b300090461b182c820b100090061b082b820b0082bc20ae1002420ad082b020ab082a820a9082a01ada0829c20a60829420a40828c60a20828420a00827c609e0728c209d0557c209c0,0x838820e10838020df1837820dd0837020db1836820d80836420d20205420d81834848151835c20cd0835420d6083544e6e083501cbd0834c1f09039b408150834820d1045044e6a01e0820d00833c1e06045081562045004e690833820cd0832060c71833020cb0832820c90170840221832020c7017080022044f820c50831020c316ba860c606090113e1831460c41,0x84502113084482111184401b08083f0610f08438210d08430610b084282109084206107084182105084102103084082101084000b7d055d060ff139ec20fe083f44b81183f060fa083ec0e78083e820f9083e060f7000b0061f083d860f5183d020f3083c8002401c4c20f1083c020ef083b820ed183b060eb0002420ea083a420e80839c1afb0839820e50839020e30,0x84f4213c084ec0009084e80012084e42138084dc213606dd82135084d02133084c82131084c0212f184b8212d084b0212b184a82129084880818084a0212718480488a18498211d07c40212508490212313a18081808488212107c3c0e830222821200847c1f0e039fc211e08474211c1846c45c8068f005c6000a8211a1846461180845c06e1000882116084541b0e1,0x85c41e0a085c0216f085b8156805054216d085b0216b085a82169185a021671859811cb04b3c216518590216318588216108580615f08578615d08570215b08568615908560215708558615508550215308548215114518156308540614f08538214d08530614b13a48214a0852461481851c2146000a046230851421440850c6142185042140084fc002401ad8213e0,0x867c219e08674219c0866c219a06fb4219908660219708658219508650219308648219108640218f08638618d08630218b08628618901e2821880861c1e0e05590114f13a5c21860861421840860c2182186046180085fc06601008845ce1695405cc00098217e085f4217c055ac1416085ec114e085e8217906e206178085dc1373085d8217506e082174085cc21720,0x876c21da0876421d80875c61d613a9421d50875061d31874821d10874021cf0873821cd0873021cb0872821c90872021c70871821c506fcc21c40870c21c20870421c0086fc21be086f421bc086ec21ba086e421b8086dc21b6086d421b4186cc21b2086c421b0186bc21ae086b421ac086ac21aa086a421a80869c21a61869461a413a8821a30868840090868421a00,0x8848621108840220f08838620d08830220b08828220908820220708818220508810620313aac22020880462001878021ff087f861fd0874861fc13aa421fb087e821f9087e021f7187d821f5087d061f3187c821f1087c021ef087b821ed087b021eb087a821e9187a04ea80879c21e61879440300189c21e41878c21e20878421e01877c61de08774002401d8821dc0,0x609c0b7e055d8624813ad02247089184b83188b4621618914224403ac8224308908224108900623f088f8223d188f0623b088e82239088e02237088d82235088d02233088c8623113ac42230088bc622e188b4622c088ac222a188a462280889c22261889462240888c22220888422200887c221e08874221c0886c621a13ab822190886062171885862150885022130,0x89ec227a089e46278189dc0012089d82275089d02273075ec2272089c42270089bc226e089b4226c089ac226a089a422680899c05d2000b822661899462640898c22621898462600897c073700088225e089741c051897018260896c625a070042259089602257089582255089501e5c0894c5f1f089481d010894462500893c224e08934114808930224b0892822490,0x8a9c22aa03b4422a908aa022a708a9862a511990002a08a9062a311b90002608a8822a108a80229f07624629e08a74229c08a6c1d8508a68229908a60229718a58229508a50629318a48229108a40228f04544228e08a34228c08a2c228a18a244ec808a20228712e10628508a180ec508a14228408a0c6282100b006b908a042280100a0071c089fc227e089f4227c0,0x76a022d408b4c22d208b4422d008b3c22cc18b2c62ce08b3422cc08b2c115208b2022ca08b240b7f08b20515213b7422c708b1c4b7f18b1022c608b140edb08b1022c3000a046bd18b0822c108b0062bf100a006bd08b0022bf08af022be08af422bc18aec22ba0004822b908ae01d9908adc22b608ad422b408acc22b218ac422b008abc22ae08ab422ac1223462ab0,0x8bf40b80055dc516813bb822fc08bec4b86100c006c108be862f918be022f708bd822f5100a0076b08bd022f308bc822f108bc022ef18bb8001208bb422ec08bac1db808ba822e908ba022e708b9822e508b9022e308b8822e108b8022df08b7806681009862dd08b7022db18b6846680009822db08b68157208b5c62d608b545da818b6422d8055c862d708b5862d50,0x8cd4633408ccc233208cc4233008cbc232e07a54232d08cb0232b08ca8232908ca0232708c98232508c90232308c88232108c80631f08c78231d08c70231b019b0002e08c68631918c60231708c58631511ce8002608c50231308c4823110770c631008c3c230e08c341dbf08c30630b08c281e5e08c24630808c1c230618c14630408c0c230208c04230008bfc22fe0,0x3c00003001c98235418d4c402c01dc0235218d44635408d4c235208d44234e08d3c233a08d40234c08d3c634e13bf8234d08d34634c18d2c1a2308d28234908d0c634218d20234707ccc234608d14234408d04634018d0c234208d04234008cf8233d18cf0233f08cfc633e18cf4233c13bec233b08cec459508ce8233907cc8232308ce0233708cd8233508c8c4efa0,0x7ce0238c08e2c0f0508e28238908e20238718e18238508e10638318e08238108e00237f08df8237d08df0237b08de8237908de0637713c10237608dd4637418dcc237208dc4237008dbc636e08db45f3608db0236b08da8236908da0236708d98236508d90236308d88236108d80235f08d78635d08d704f0108d6c235a18d64635208d601f3508d5c635608cd063551,0x8ec823b108ec023af08eb823ad18eb063ab08ea823a908ea023a708e9823a501ba0002e08e9063a311cf4002a08e8863a118e9023a308e8823a108e785e9f18e80239f08e781e9f08e74239c08e74639c18e6c239a08e5c639618e64239808e54639418e5c239608e54239408e3c238e08e40239308e48239102e14239018e3c638e13c1c238d08e344b8518dcc23731,0x8fa423e808f9c23e608f9423e408f8c23e208f8423e008f7c0aa608f7823dc08f7423db08f7063db18f6823d918f6063d718f580a7918f5463d408f4c4a7f18f4823d108f4023cf08f3823cd08f3023cb08f0023ca08f2463c808ef023c708f1863aa18f1423c408e9c63c308f0823c108f0023bf08ef823bd08ef023bb08ee823b908ee023b708ed823b508ed063b31,0x908c24220908424200907c241e09074241009070240f0906c241a0906424180905c24160905424140904c24120904424100903c240e09034240c0902c240a0902424080901c24060901424041900c640209004240008ffc23fe08ff423fc18fec63fa08fe423f208fe023f7050f023f608fd423f408fcc23f208fc423f008fbc23ee08fb423e508fb023eb03fa823ea0,0x9114644419100243c090ec2443090d4243409108242d0909c242609104241b091002439090e0243f090c82431090f8242c09090241a090f42419090f0243b090e82439090e02437090bc242b0908c2422090d82417090d42434090cc2432090c42430090bc242a090802416090b82415090b4242c090ac242a0907c241e090a42413090a024120909c24260909424240,0x91f4247c091ec247a091e42478091dc2476091d46474091cc2472091c42470091bc246e091b4246c191ac246a091a464680919c24660919424640918c646203fa8246109180143c0917c245e09174245c0916c245a07b74245919160245709158245509150240b0914c24520914424500913c244e09020244d08fd4644c0912c644a19124244808ff8244708fa464460,0x92d424ad192d064b3092c824b1092c024af092b824ad092b024ab092a864a9091e824a80929c64a60929424a41928c24750928824a10928024720927c249e09274249c091b8249b0926824990926064970925824950925024930924824910920c246909240248f09238248d09230248b09198248a0922424880921c24860921424840920c6482092042480091fc247e1,0x939024e30938824e10938064df0937824dd1937064db0936824d90936024d71935824d50935024d30930c24d20064424d10932424d01933c64c70933824cd0933064cb0932824c91932024c70931864c50931064c30930824c10930024be092f424bc192fc24bb092e824b9192f864bd192f024bb192e864b9092e024b0092d824b5192dc24ad092d024b3192c064b61,0x945825170945425161945465140944c25120944425100943c24be09438250d0943024bb0942c250a0942465090942025070941824fc1941425041940c2502093d465010940024f1093fc24fe093f424fc193ec64fa093e424f8093dc24f6093d424f4093cc24f2093c424f0093bc24cb038cc24ee093b424ec193ac24ea093a424dd193a024e71936464e60939464d50,0x952c654a1952425480951c25460951425440950c254109508254119500253f094f8253d00644253c094ec253a094ec653a194e42538094dc2536194d82535094d02533094c82531094c0252f094b8652e094b4252c094ac252a094a46529094a0252709498252500644252109490252309488252109480251f00644251b09478251d09470251b0946825190064425180,0x96042580095fc257e095f4257c095ec257a0959c6579195e02577095d86575195d02573195c82571195c0256f195b8256d095b02554095ac256a095a425680959c65660959465640958c25620958425600957c255e09574655d09570255b09444255a0956c655a194b0255909560255709558255509550255309548255109540254f09538654d0953025370952c254a0,0x96f025bb096e825b9096e025b7096d825b5096d025b3096c82548096c425b0096bc25ae096b425ac096ac25aa196a425a5096a025a70969825a50969025a41968c25a20968425a00967c259e09674259c0966c259a0966425980965c65960965465940964c25920964425900963c258e09634258c0962c658a0962465880961c25830961825850961025830960825821,0x974065ef197b825ed097b025eb097a825e9197a065e71979425e60979463ee0979065e508f9825e40978c25e20978425e00977c25de0977425dc0976c25da0976425d80975c25d60975465d40973c25d30974c65d20974425cd1974025d01973c25ce0973865cd0973025cb0972825c90972025c70971825c50971065c30970825c31970865c10970025bf096f825bd0,0x988c26220988426200987c261e09874661c0986c261a09864260f09860260a0985c26161985426140984c26120984426100983c260e0983426080981c260c0982c260a0982426080981c26060981426040980c2602098042600097fc25fe097f425fc18fa425fb097e825f908f9825e4097e025f70975425f0197b465f6097d465f4097cc25f20979825f1097a825f00,0x996826590996026571995866550995025ee1994c26520994426501993c264e09934264c0992c264a0992423ef09920264709918264509910264309908664119900263f04288263e097a4663d098f0663b098e826390974065ef198e02637098d826350972c2634098cc2632098c42630098bc261f098b8262d098b0262b098a810a2098a426280989c26260989426240,0x9a68269909a60269709a58269509a50269309a48269109a40268f09a38668d09a30268b09a28668919a20668709a18668509a10268309a08268109a00267f099f8267d099f0267b099e82679199e02677199d82675099d02673099c82671099c0266f099b8266d199b0666b099a82669099a0266709998266519990666309988666109980265f09978265d09970265b0,0x9a6026c709b1866c509b1026c309b0826c109b0066bf09af866bd0997426bc09aec26ba19ae426b809adc26b609ad425ef09ad014df097a426b309ac826b109ac026af09ab826ad055ac26ac055a026ab09aa81c7b09aa426a809a9c14df09a9826a509a9026a308fd426a209a8426a008fb825e419a70269f09a7c669e09a74266c19a68666c09a70269b09a6c66991,0x9bdc26f608f6826f509bd026f3090d426f209bc4642719bc026ef19bb826ed090c826ec09bac641f19ba826e919ba026e709b98242319b9426e419b8c26e209b8426e009b7c66df09b7866dd09b7024050904c66db09b6866d909b600a9609b5c66d60904066d509b50641a19b4c26d219b4426d008ff4241619b3c26ce127b409ed19b3466cc09b2c66ca19b2426c80,0x9ca0272819c9c272609c94272409c8c272209c84272009c7c271e09c74271c09c6c271a09c64271809c5c271609c54271419c50271309c48671209c44271009c3c270e09c34270e19c34670c09c30670b09c28243c09c202709190f0670909c20670709c18270509c10270309c10670319c08270219c04670009bfc243909bf826fd19bf066fb09be826f919be426f80,0x9d50275309d50675319d48275210644275100644275009d3c274e09d34274c19d2c674a00644274919d20274719d18674509d10274309d08674119d00273f09cf8273d09cf0273b19ce8673900644019109cbc273809cdc273819cdc673109cd8273309c60273509cd0273209ccc673219cc0273119cc0672f09cb8672e09cb4272a09c1c272c09cac272909ca867291,0x9e3c678e19e34678c19e2c678a09e24278809e1c278609e14278409e0c278209e04278009dfc277e09df4677c09dec277a09de4277809ddc277619dd4677419dcc277209dc4277009dbc276e09db4276c09dac276a09da4276809d9c276609d94276409d8c26a709d88660819d84676019d7c675e19d74675c09d6c275a09d60275909d60419109d5c275619d5827550,0x9f1027c309f0827c109f0027bf09ef8270d09ef427bc09ecc27b119eec27b019ee827b909ee027b709ed827b509ed0270c09ecc27b209ec427b009ebc27ae09eb427ac19eb027ab09ea827a919ea427a809e5c67a719e9867a509e90276719e8c27a209e8427a009e7c679f09e78279d09e70279b09e68279919e60279709e58679509e5027930998c279209e4427900,0x9f34271809f7827dd09f1827cd19f1867ba09f7067ba19f6c27da09f6067d909f5827d819f4c27cb09c4827c409f3067d719ee027b919f5827d509f5027d319f4c27ca09c44271009f4827c309f0827d119f2867c319f0867d109edc27b719f4027cf09f38270f09f0427c119f3427cc09f2c27ca09c3827c009efc27c919f2027bd19ed827b509f1c67b219f1827c50,0x9b00280f0a038680d0a030280b0a028280909ae828080a01c28060a01428040a00c28020a004280009adc67ff09ff867fd19ff067fb09fe827f909fe027f709fd827f509fd027f309fc827f119fc067ef19fb827ed19fb427ab09fb027ec19fac27e109fa827e909fa027e719c6027e609f9427e409f9067e319f8827e109f8067df09f8867e119f8027df19f7027cf0,0x28390a0e028370a0d828350a0d028331a0c828310a0c0282f0a0b8282d0a0b0282b0a0a828290a0a028270a08c28260a09428261a09468240a09068230a08868220a08428200a07c281e1a078281d0a070281b0a06828190a06028170a05828150a05028130965c28120a04428100]⟩
def graph : Graph := ⟨10298,14,14,835,962,rows,actions,parentRuns,exitRuns,arcs⟩
end CoJunctionArchive1

namespace CoWholeRoot1
open CoJunctionComplete4482 CoJunctionFixed4482 CoPortRoots4482
abbrev gr := CoJunctionArchive1.graph
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private instance : NeZero gr.size := ⟨by decide +kernel⟩
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def hints : Column := ⟨17,#[0x27ed17d659f365ed90ff00bf64e7c0775a796e9db6877c23bda0fee8ef68b7be5bd93cf19ed6df1c27adc0ff00f768cfbe3dda2ef097764cfc46ddb39ef1d764f9c07f1e0ff20fe689fba5f993bcf1de68f7427b9c0fed0f7687db41fda1fcd0fe687f343f9a0fed0ef683fb83ed90fed13f6c3fb81fdb0fed177643fbc1fde0fed87f68e7bc1fdc,0x1fad07f6c7eb437dd1fad07f647eb43be31def1f97cef347b5a0fed0fe7c7bb43f991fccbe594fe343bdc7d2d87f7877b46f681ded07f70b7b26f631eed1dd80e7b4e79f73b2b3d99f3463ee579ce3ea687f343ddb1fad07f6c7eb437da1fad07f647eb43bdd1fad0df687eb47e5f3dce1f5683fb43f9f1f6c8fe647f32fe1c0ff20fd687f483eda,0xff29fa687f347cdd1fad0bf647eb473de3cf00fd6cfcb65f992fac97d64beb25f592fac97b645fb21fda0fed07f683fb42fd90fed07f683fb41fda17ec87f683fb41fda17ec8bf643fb41fdb0fee07f687f341fda1fad0fd687eb4f35e3f8d0df69ecb01fe21bed0fd9477b41fdc2bec8f768f3ba7d5e4fcc27d747ed89f6279cd3da5c7f343ddb,0x1f6d87f6c3fb41fda0fed07f807f3c3f9a1fcf0fe683fba3f9a1fad07f687eb43f5a0ff08fe683fbe3eda27ec87f8c77b479dc0ff187f843fbe3f610fec8df646faa1fd917ec8df646fb22fd93f4d0fe687bb83f5a0fed1cf6877ba7e611fcd0fd683fba1fda0fed87f683fb63f9a0fec8fd683fb65f990fee17b643fbc1fd91ded0f7689fb24fdd,0xfed0fe643fb23ed91f6c8f7647bb23dd91eec8fb643fae1fda1f6d0fe887f345ed967cc8fe68edb4f35c1fcd1eb6df2ca3f9a0fed13f65e6b2f9623f8f1fa70fd387e9c3f4e1fc683fb61fda1fcf0fe687f3c3f9a1eed0fb6c7f343f9a1fcd0fe687bb45dd927ee8f7687bb67e9a3f4e07f689fb2f3587caf9f978fe367e5b3f2d9f96cfcb6fd1b,0xfec07f607daef1df3f8d0df6c7db41fde1bec87f8077b41fdf1bed0bf847bb43f5a4fcd8df993f3cf3961fcd1eb6c7db41fd91eed1af6c7bb44fda1eed19f6c7bb479dc3db09db68edb075d93aec9d764ebb273da1eee9e764edb21fda1f6d87f683fb23bd91eee07f6c5fb23bda1faf87f603fb61fdd1dec8fd7c3fb21fdc0fed87f7077b43f60,0x3db007f703fb21fdb0fef97e643fb45ed80ff087f603fbe3bda1eed16f649fc67b6127ef13f7c3fc61fe31ded0fe6877b63eda17ed8f7685fb43dda17ee8df6877b87b5e17ec87f603faee5e33f8d0bf607db21fe117ec07f6c5fb46bdb1fad39e887bc6e5eb75cc0fe6877b43eda1bee0f7683fb23dda1bed1ed80ddb679dc0fed07f687db83f97,0x3dcc8fe68f5ba3eda35ed93f64dbb673d93ced9ed887db23ed81eec8f7647bb23dd91eed0fb643fb41fda0fed07f603fb41fdb0fed07f683fb41fda0fef07f643fb43ed91f6c8f7647bb23dd91eec8fb643fb62fdf3f8d0bf70edb01fe117ed0bf68dbb63bda4df20fd693f421fde0ff139e7477ba3f9a1def0fb683fba3dda0fee8df746fba3bdc,0x3dcd87f683fb41fda0fed07f687db61fda1fcd0fb6c3fb43f9a1f6d8bf687f3c3f9a1fcd0fe687f343f9a1fcd0fb6c7f343bd90fef8ef6877b43ddb39ec9cf70fcb675dd0fec8fb60f7361fda39ed13f6877ba37db1eed1f580f5b27adc7d4c8f76c3fb61fdb0fed07f603fb21fd80fec07f747f341fdb1f6c8ef689fb26dda1dec87f887eb41fdf,0xfee8ef683fbe37e13bb00f768e7b41fda0fed0f76c7f2e1fd81eeb87f74bf321fdb1f6c87f783fb41fdc1ded0f768bbb2775e27ee87f8c6fb43f9a1bed8fb683fb63bda0fef0ef685fba37da1bee9dd7c5fb21fd71dec8fb7877b43bda3cedb9798e7b23dd91f6c93f6cfcb81fda39ed13f65d3c4f1db3ece3e980f7367b9b3dcd9ee6cf7367f1a,0x1fcc0fe607f302fda0fed0fe607bb43f981bed0ef686fb43ddb3ced9f96c7db2779a0fee8df743fb83be31dec3c77cfac0f6971eec87f603fb83f9a0fee0fb6477b44fd91eec9d760eeb41fdf0fee0df687f3437dc1f6d07f803fb42fda1bed0df74eec01fd90fee87f6537b27f1a0fed8fb643fce1fda17ed0f7687eb49f9a5bcb8fe686fbc3eda,0x27ed8bf645fb237d91bed07f683fb41fd60fec07f643fb237d91bea8bf646fb237da0fee0bf643fb61fd91fac8df643fb237db0fed07f683fb237da0fed0bf786fb473da4dec8df687bb479db3f2e07f6967ae4fd93cee9ee69e3bef65c3bcd1de68ef34779a3f8c1de68ef341fda1eed07f687f301fda0fed07f607bb03edb1fce8fe607f303f98,0x1fcd07f603fb437db1dee8f7807dba3ddb0fed07f686fc25bd92eec9f96c3fb42fd91bed0ef74bdbe3f5b0fed07f683fbe3bda2eed1f9689fba1fda1fcd0fd685fb23f5a1fad0fb68bf321fda17ea8df6877ba5dda2f6d0f7703faa1fd70feb07f807f341fe01f6d0ef68bbb23f5a2fcd0fe68bdbc3eda27ec96f6cbbb6cf581bec8df549fb22fd9,0x4faf8fe65ceba6f9b1bed0fb6c77b63ed91fce8fd5c3fae3ed917ec8fd5c7eae1fd71eec0df587f3a3f571fab8fd5c6fac3bd81fce8fd5c7eae3f571fab87f5c5fb23f9d1fab8fd5c7eae3f571fab8f7607db02fd91dec0fe5c7f2e3f971fcb8fe5c7f2e4fd91ded1e768fcb81fda0fed8df6c77ba3ee11fad07f683fb84fd91ded1e76cfcb63eda,0x1fac0fd64e7ba76da79ab1dd683fbc3bd927ef17b5d9eac5f5717ec0bf609fb65bd73cf31eb61f2ba7b5a1eee8f761e3c075d866f31775c3fc23eda4fab8fd643fbc1fd90fef8ef651fb22fd90ff20f764cfc06ed973ac1bd646fb837d973ae1af649fba57d733ef9b7652fae37d93e709f679fc387e980ff28fe65e6b6779827f017e5df2bc7b9a,0xff00ef689fb45f9927ee97b643fc02fd927ee96f65f33c7b9b3cef9eb703fc03dd978f09d7649fbc5dd94fcb8fe683fbc3eda0fef07f6937ae3bda0ff00bf683fc63dda73cc1be6ccfc06edb0fef8df64cfc06bdb27ef15f65cbd26ddb4beb8df65fc387e9c3e6f9f96c3fc83f5a79ae1dd689fb45f597cb19ed713eba3f5a73af9bd6c3fd03ed9,0xfef8fb643fb81fd80fef8ef603fc02fd80ff18f760cfc06ed80fee8df61cec06bd827ee15f58cfb86dd80fee0df60f9c87d9d0ff20fe61e6ba779827f017e59f2c67b9a4fb08fe61cec26f9a3e731f9643fc23f5879ad9dd649fae5f567cb31ed693eba3f5873af9bd61fc427e9a0fed07f603fb21fdc0fee8fe683fc03eda79cb9de68e7be76da,0x39ed0ef5c7eba3ee00fee0df7477ba6bdb0feb87f5c7bac37d61f6f0bf7c3fc857de1bef27e8579ba9edd1fd09f3743fbc1fe60ff117b78e7ba1fdd78ed0df607f401fd91fce07f6477b03dd61faf8fb7c6fbe3bde1dee87f707bb41fd60ff08fb60e7be76d90ff00ef609fbc5ed60fee8bf5c9fba5bd63cf19eb603fbe3dd839ee9d7609fb25dd6,0x3e6e87f98df421fda0fed0fe7c7bb43de21f6c9d7747db45f5c1f6c9f58477b87ad92fb187f7c7db42fdc1f6e1f980fcc07e603f301f980fcc07e603eaf1fa80fd407e9d0ff087f685fb81fd80fed0fd803fb62fdb0fef07f6c3fb43f5d0fed2eb78edbc4fdf7cd33e381f1c8dba13e701e78cdec27ce133f0b8f78dbc63f9d0fec97764df346f9a,0x3f328fe5c7f2e3f971fcb87f787bb037df1eec13f783fb85dd61df09e7603fc03dd917ee0f7607bbc7e5c3f320fb6c3fbe3dda1bef0f7683fb43dda3baf8ef84f3b67b5d0fee8f7685fbc3dda1f701bb7dd9bce6e13b6f0bf783fbc2fde73d099f7dadbc7cdd0ff007f6c3fb63f9f1dec9db75e9bef2de0ff08bf84e7c21fdd1beebce74e7c23f5c,0xfec8fd607eb02fd61fac0fd607eb03f983e718bf787ec02fde0fed8bf783fb41fdb3dce1de70fe3c3ee00ff10fd686fba775a0ff00fd6877be3f5b0ff00fd685fb66f5b37ad9fc8cfcb87e5c3f2e1f970fcb87e5c3f8e0bf5c7db2775a1f6c87f60bdae7b5f1f6c8fd787db26f5d1f6c9fa883fb23f580fed87f6c3fb6fca00fef17d5df93c7e60,0x5f523f487ec3efd259f50bf487bc41d99d7c71fe181bacaf961f690be98739c1b95c6f8c1f581f4c27f223eaebe984beb27d5d7d30fe887f13c1fe01eec1cf806fba75db0fee0f76077b879d90fef0f764cfc22fdb36ed1f3947ec037df1bef07f643fba5f5c36ef0bf70fcb01fde3e7213f6cbeb83dd90fec07f603fb02fd51fac0bf5c3fb41fd9,0x1fcd0ef643fb63f9afc301f3bdf1c2fc6a7c70bb389f1c7e8e17c719f381e9c2bce37c6fef16df1c2dcdece6e6739769b8f4e8f86ffc39be1bef8de7c73be36bd1baf8dbdc6e1f38ef1b93ce0bc6e1f38979c2f4d9ba6f3736eb9bd3ce9bc6f37399f1c35cdd7c70bb379d9c5cea6ea6e9f37f59b8f8dcec6ebb36ad9b9f9233e773e687cd3de99d,0x1dee9f9807f343f9a3f8c0fb603fba3bd917ee0ef683fba3bda17ed0f76c6fb83bd91df01f970f3c677641ded8df74fe3a1fdb1fad1cf687eb44fdc1fad3a7887eb4f1da1fad1de69dcbc3f9a1fcd9be6cdeb66f5b37ad9bd6cdeb67f1a37ad87f683fb61fda0fed87f687db41fda1fcd0fb683fb63f9a1f6e8bf687f3c3f9a1fcd0fe687f343f9a,0x1dee1f970f3c66f671bed8ef7cafb81fd91eec8f76077b23bd91bec8ef6477b23dd91fad07f707eb437db1fad13f687eb473da1dee9f9807f343f9b1fad9fc687eb61fda0fed87f687db81fde1bed07f78e7b41fdd0fee8df685fc23ddb3ced1db78afc237de3f2e1cf88bece3f981bed16f893f4a3f5c0fee0fd686fba3f5a0ff08fd6877c63f5a,0x1fcc0fe607f301fda0fed8bf683fb43f9a0fed8f7683fb63f981eec87f683fb41fd90fed8f7687bb21fda1fcd07f683fb63ee00ff187f683fbc5bd92eed0bf8077b45dd917f087f78fcb65f9e17ef07f785fb22fdf1fad07f687eb437da1fad0ef746fb43bdd1f6e8fe687f343f5d1f7007f8877b237dc39ec9e76c3fba3bda1ded1e76ccfb675df,0xff08bf647bb63bda3cec8fb803fbe1fe23f2e0fe843fc41fdb1fb00df6c3fb43bdd1bed8ef747dc23f9a1fcd0fd8c7dba1fde1bed0df687bb43bda1eed07f806fbc7e5c39ee8fd8c6fba7f1c0fed8fd68f7344fda78ef1ed6567ae79dd7b2e0fe687f34779a3bad1fc687eb43f5b3bad1dd68eeb4775a3bad07f687db83dd91fce8fe607f303f98,0x73d09fa68df38bda42fd039e607f407b9c3bcf1fc7de734bda12fd239e78fe3e3ee01f6d1db68f6ba3eda1f6d8fb68ddb6775f3eae9ed78eebe7f1a0fed3cd649fb2f96279acbe588fe3c7e9c3f4e1fa70fd387e9c3f4e1fc683fb63f9e1fcd07f687f3c3f9a1fcf0fe687f3c3f9a1eed0fb6c7bb43edb1fcd0fe687f343f9a1fcd0fe687dc03bda,0x1fb04dd74eec03f6a2fb04fca4f6c1cf1a7acfb3d85baba3f6237aff1d69aeba9f6357af72dbdb6bb2f5937af8fd84fcc0e75d772e0fd88fcc077613f328fd8cfcc0cf5d6f2eff07df93ef9627e2f0fdc0fcc1e65d772e27d7d7cbdf2697b304f994fcc1ce616f2ebf185f93e3edb5ed017e88df3a3f603f8dbce64fd36f3971f6d8bf807ec07f1c,0x1bed19f80d7b64fde2becb979cdbb697d71becbf874fd387cde3f2d87f947eb6f35c3bad13f68beb2f9633dae27d787eb6e75f37ad87f6c7f341fdb0fee87f703fb83f693f500fda0fac1e719774e39d81dab877613bb027d857d3c9f625eaf0fda4bec09f615baf7cc89ed3ef3647ab09dd8cf6bfe36675ae27da176bd3f2076d08fd8cfac03f69,0xfec07f706fb01fd90fec07f643fb03dd80fec07f647db01fd71dec0df6077b01fd81bec0ef6077ac3ed71deb87f847f361fe11f6dbce64ef3473dd3b6d07f8077b64fdd2fcc93f74bdb21fe117ed13f74b7b2f9a03dcd9e774f5b81fe11eed3c780ebb24fdf2eeca7e787f361fdd1f6d07f843fb69bd91ded87f885fb61fe31eed99f78ddb61fdf,0x27f295f6197b85ed80fef8bf6197b05bd833f09b775f1be7adb1eee0f764e7ba75d927ee977603fc037d94f6c0fb643fba1fd90fef0ef643fc02fd94ef08f764cfbe6f9e7e4d1f6643fc23f9939ee1de649fbe5f987c6f9ee6d3db63f9933ee9bd6df8be7d591f718fd64e7c2775927ef97d60f3cc7b5b4f700fd65f8bc7e9e0fee07f703fb03bd8,0x27ee977603fc03ed90fef07f683fbe3bda0ff08bf683fc63dda33f21bb643fba37d933f01af649fb857d872f49b7652fae37d83e709f6803fc63f9a39ef1de689fc25f9874f21ee712fb63f9a73cd9be64f9ca7d5d0ff28fd68e7bc775a27ed17d60f3ca7b5c0ff18fd69cebe6f59772f9fa743fc037d81f6d8fb64cfca6bdc69ee1db643fba3bd9,0xfed0fb6c7dba1fdf1bf18f76c6fb673e40fec07f5ce7c6f1de78ef87f80cfc8f2e40ff01cf6cebbaf4dd2df2babb0f5bc37e01f7023f783fb43eda0fed07f6877b23dd91eed87f687db61fd817ec8bf807db84fe40ff00df683fbc3bd90fec07f5c3fc83eda39f11db683fc83bda27f197b603fbe2fd927ee96f60f3c67adb0ff10f768e7bc75d9,0x3af007f999bd81fdb1fce07f647bb63ddb1f6d0f7783fca97e70fee27e8c3fc8a7de4bef07f614fbc1fe41fcd87f606fb01fd81eec0fb743fba2fda17f08ef6c3fba2fdb33ed8bf6cf3b679db0fee0bf64cfbe2fde3f2e1bd9c3fb42fdc3af015f703fb037d717ec8df645fb237d91bec87f606fb2e5e11df21db94d7bce6ed3b6eb9bb83fc01fdb,0xfef8bf606fb02fdb17ee9bd69ced27ce10fef87f8c3fbc2fdb1beb8fd883fb4d76763ed95f7d8fbce3de63ef38f758fbcf55e71ee0df605fae37d717eb8df5c6fae1fd71eec0df603fba3dd91bee8fb643fbe3dd93e6f8ef64f5b85edf0fed8f764fcc83ddc3f2d8f77cbbbe75de1ef09e7787dd06de54df087f609fc4e7a636f4b9795cbd66ddd,0x1bec07f7077b25bda3bce8df6c6fbe3f5a2beb9cf643fb637d817ed0ef643fae37d917ed0f7643fb037d93dce1fc787dc07e9c0ff08fd6c6fba779a0ff00fd6c77ba3f9c0ff00fd6c5fb67d5f0ff207f79cec6776237af0efa83fc0e7a21fae07f607f3c1fd937ad9ed687eb61fda0fef0fe683fc61fde17ec8bf8877b41fdf17ed0bf7cdbb81fe1,0xe732373939cc4c7e37373b3d85cebdc762c3f463d915f3ae75fe5b1b9d769ebfc76667b27f09b9d441fe01eed1cf806fb876da0fef0f76877bc7adc0fee0f764f9c23ddd3f2e07f886fb03be633f387f783fb02fd81dec07f58f9c457e31fb00bf883fc02fe10fed87f703fc037d81df0a9f746fb69be20fed87f6c77b41fd90fec07f6c5fb03bd8,0x6770b1f9d97cad6e26e7319fbd97c2a7ed63f0abb95b9c667e963f138f8717c4c7e5e4f236b9795cae5de66f1b977b8bc987f9c6f119f968fbc6ee2a76fa9f7d4fc2e3dea5efc9f9e8fbe37db72efd377f99be67e463f071e9997c2a7e663f0f17c59bc327dea3efb1f8f9e4c67ec67d0fca838f40beaf7e927aa92fa4d3e9fa7cff1ea39b40c7e1,0x27ee96f65f3427b9c3cef1eb703fc23dd978f01d7649fc05dd94fcc8fe683fba3eda0fef07f6937ae3bda0ff00bf683fc83dda73cd1be6ccfbe6edb0fef8df64cfc06bdb27ef15f65cbd26ddb4beb8df65fc387e9c3e6f9f96c3fc83f5a79ae1dd689fb45f597cb21ed713eba3f5a73af9bd6c3fb43f9a0fed07f703fb61fdb6e7419fa98fc06ee8,0x17eca777c7bb267e535ec31f70ddb01fdf1becb1f70afac67dc36ec07f786fb273de3bcfbf268fb2e1fe41fcc93f80bf2cf8df3dcc27b7c7f3267dc37cc9cf78eeb8fc5b3eab87f947eb24fda2fab3e380f6b01fe51fac99f90deb0fc5b3f4d87f743fb21fda0fec0fb583fbe3f9a0ff00fb68e7b876da0fef0ef689fb85f9927ef17b643fc02fd9,0x1bec99f80d7b44fde2beb99f78dbb41fde1bec9f38cfb401fe41fccbce68ef304fe12fcbbc780f7349bdd1fcc99f78df367ce33eaf07f8c7eb2f35b3bac13f64beae79e33dad07f887eb267e437ad3d96cfd341fe41dec87f707db24fe12deb31f74bdac1fde17ec1cf88f3b0f8dc3d6c07f747bb24fd82eeb07f8877b49edb1f6c87f743fb21fe2,0xfee87f746fb45bdc17f099f6dcf4273e11bef1f970eebe3f991bed26f787bcc3de11bed87f7cbdbe9de11ef207f683fb63ddb1f6d0bf783fba1fdf1dee07f703fb41fe41f6c9cf8cedb01fdf1dec93f84bdae1fdf17ec13f6cb7ae79e13d6c87f807bb2f1dd3aeb93f6cbbae1fe01f6d07f7c3fb29bd81dec87f845fb21fe41eec99f94ddb41fdf,0x3e6e87f90df467e9b79af1ed78eeb83ddf79cd8fd643fb03f9b0fed07f6c7f341fe01bec8ef683fbe37d939f18df78f3b0f1e30ff08df6937c22fe233ed19f886fba3f9a1bee9dd61e6be1fdf1eec87f787bb2f4e01dee9eb60bdc41fda1eed87f6c5fb23f9817ed9b7647f367e611eee9f9607bba3edc0fee0df683fb837da3b6e8df70f3b479de,0x1fcc0fe60ef387f1e1f701fa703fc23f5a1bee87f807eb43bdd1fcd87f807eb42fdb37ad9d778ef3a1fdd73cc8fd907f383f9b1fcd8fe6c7f363f9b1fce1de707f367f181fcd87f7077ba1fd90fec87f7c3fb83f981dee87f703fb21fd90fef8ef707f303bdd0fee07f647f301fd90fee0ef703fb43bdd0fec87f643fb83bdc0fed0fe60faba75e2,0x17ee0ef64f73e3be01def0fd683fb63bd91def0ef68f3b873e41dee87f643fb41fdd1fcb87f643fb279dd1eee8ef79e744f1e13aec1e7807f361fd91f6c0f7703fc63be50feda7e9167bc1fdd39ee96f943fb63fa00fec8f765f934eba11ef207f88fe34e76279cf8bf706fbc6f9d0fed87f643fba1fd91fcc0fb747bbc3f9d1fcc0fe607f303f98,0x71ef68f75e3b7c5e071edd8f7dc7c3e71f79d639e83c743e59c5f56bf487e538fd26bd4fbf48ccfbe2fdd3f2e79c79c7bfe65d766ff9974e7d4e760f1b039d8b27bda75d79ad78d787db4f35cb3afbcd6f8ec0779c1f6f1fa77cd3a1fe21eec87f6c7bb23bdd3d6d07f747bb467e117ee9b76cf9c03dde3f2c87f6477b27ada1bed9e7603fba3bd9,0x4f6f1de61f8bc7d9e7f111fa643fb61fe00ff087f583fb43f980fee07f683fb2ece239f438f80e7d4e6e0f26e9cf91c7c0b3eb71f02db81d9bc73e769efacf91c7c0e3e6f0f03ab7fc5c473e772f07878fc3bd93e9d2ee9cf9ac7bc76e0b36f9cf8567c133e371f04cfa6a7bc37dc78ee59779a7d9e39f6b713ce79c7c037e139f238f8fa744e3e0,0x33ef1af643fbe3bd927ee95f5c3fbe2fd827ed96f5ccfc06dd90ff08f764e7b875d727ef1775c3fba37d90fef07f643fbc3bd90ff08bf643fc83dd933ee1fc707ecc3f9939ef9de619eba5f973cf11ee693ec03f9933f01ed687ec63f5939ee1dd659eac5f573cf11ed693eb877597f101fa64cfbe7b9b1f740fe64e7c43f9967ae97e64f3c86f9a,0x1eec87f8c7bb273da3aeb93f78bbb21fdd3aeb87f8c7bb267de1eec93f7cbbae67e036ec87f847f321fe51fcc9cf7cef30cedf2fcc9e774f734f8e537cd07f7ceeb21fe61fac9cf74eeb2cedc2fab9e788f6b4f9663dad3f880fd321fde3f8d87f9c7f3273e11fccb3b84bf2e79e237cdbe584f734fc5e3ecebf880fd323f980fee87f743fc037d9,0x1dec93f70bbae1fda1eecb9d787bb21fd836ec9cf74ebb04fd73f2c0fd907eb2f35a3bad3e390f6b44fde2fcb8fd887f3273e31fccbe38cdf36f35c3bcc1e784f7347ce63ecebf87cfd3257dc17eb07f647eb03f581fac0fd603fae2fd60ff107f583fb637d51bea8ef5477aa1fde0fec87f7477b21fe01dec87f845fb21fe217ed93f7cb7b21fe2,0x1fce87f643fb21fdb1fce07f6c7eb03f9d1fce07f6c7eb03f9d1fcd87f647f3a1fdf17ed07f7877b21fdd1dec93f74b7b21fe21eec99f787bb24fdf2eec99f84dbb273db3aeb87f847eb2cf562fac1cf70eeb2f9673dad07f907f3273e11fccb3d74bf32f8e437cd9cf7cef30f9613dcd1f398fb3afe203f4c8bf609fae4fdb2deb87f8477b21fde,0x1fac0bf547eb03f581fac0fe606fbe7b9f1fcf1de74fe3e3ede3ecf1fc7cfe3e7f1f3f8f9fc7cfe3e7f181eef0fe643fb8779867af0fe645fb23f993aec8fe6477b66f9a1fcb0fe587f2c3f961fcb0fe587f2c1fd91fac3cd5c7eb04fd71fac3e5807eb09f581fac39d687eb07ea13f2c9f964fcb27e593f2c9f964fe323f5d3f2c1fc7c3fb63f9c,0x1fae0fe743fb63f581fce8fd707eb44fd71bef0fd747dc23f611fae8fd607eba3f5d1fae8fd586fac3f5617eb0fd586fac3f561bea8fd58fcb02fd717ec0fb687f445f572f6b9f960fcb05ed72f6b9f960bdae7e582f6b87f647eb02fd61fac0fd607eb037d60fec8bf587eb03f581fac0fd603fac3f561fab0fd587eac3f580fec87f647eb03f58,0x3f509f964fcb01fdb1fac0fe747eb81fdc1fac9cf607eb2cf561fac9e7687eb2f9601facbf27df93e7e593f2c9f9643fb81fdb1fac07f747eb83f9d1f6e07f6c7eb83f5d1fac9cf607eb2cf561fac9e7687eb29f581facbf27df9407e593f2c9f964fcb27e591fae0fe743fb63f581fce8fd703fb41fda1fae0fd603fb63f9d1fae07f6c7eb01fd8,0x1f6c1cf807db04fdf2f6b1e77cddb273de3b6c1e76cf5b47d9d3f2f87f847f3273df1fcc93f78bf2e79e337cd07f7cef3067e03dcd1f674fe321fd81fcc1cf647f304fd61fcc1e7687f3073d81fcc1e7647f307ea11fcc1fa68fd347e9a3f4d1fa68fd347f1b0fec07f603fb2cf561fac9cf607eb2f9601fac9fa847eba3f5979ab8fd65f1bc3f59,0x39ec0fd609fac3f583cec9e764fd427ea11fac0fd607eb03f581fac0fd607eb01fe21dec19f8077b04fde2deb19f88dbb073db39eb9fc70cfb87f1c3cf19ed68f6b47b9a33ef9ee6c3fc23dd933ef0f7649fba5dd933f01b7643fba75d70fec0fd60e7b03f5827eb0fd60f3b23f5839ec0fd60fd427ea11fac0fd607eb03f581fac0fd607eb01fe4,0x39ec1e764fd423f581fac0fd607eb01fda0fed07f7c3fae5bd62eeb13f70bbae4fd83f2c1f960bf2c4fde2fcb8bf609fae4fdb2deb93f5c3fb03f5839ec1e764fd423f581fac0fd607eb01fde1bec07f7877b04fdb2beb0f760ebae1fdd3aeb8fe603fc23f9939ee1dd64eeb27f1b0fef1fc6c3fbc3bd90fee8ef643fc25bd70ff10f7643fb03f58,0xcf2b7995df8b27e617b2ccf96eecb19e5cdb2b7c981f8b23f583f2d3e96b9cbd7a58cf326e9587eb07e5bed2d7997bd4ae7e637e2ce7959f8b1e65a7e2cfc99df8b3f91f3f333f267ccbb7c98cf2eef25be4cbdc9bf32efb25fe4c3f49cfc2f7e26ff840fc9917eb87f7c5fb43bd80fef0ef647bb01fe21eec87f887eb23f591fcc07f8c7f324fd6,0x1eee87f5c3fba37d80fed8ef643fb837d91eee0f7743fb63dd81bee0f7603fb43dd81df19cf6ce7b03dde1fcc0f76c7bba77581eed0f77cef303dd80fee87f6877b02fdc1dec87f6c77b22fdb1eee8df6ce7b037dc0fee8f7606fb63dd80fee0f76077ba3dd81bed8f7607bb86f991eee8f780f6b43ddb1ef19ee687bba7e5d7e2ce7959f8b27e5d,0x5aee1d774f3c83dea3cef33798f3bc9de35cee33795b3bce5e374ed8f7a8f6bc9dde5dae7b181d6bbf46579af8f7b0f73ce5e33dcf277997738f1e66dceb978dd738f1e279d03e38bf13cfa62fc4e93f5877b23ddc0fee87f646fb43bdd1ef00fd607bc03de21fcc0f7743fba1fd81dec8f7703fba3dd81bec8ef6c3fb63dd92fab0f7687bc45f96,0x2eec8f7707bb4e3da1eed19f7cdbb473dc3aec13f80bf383de31fcc1cf7cef3079dd3dcd1cf907f30f8e537cc93f70beb61fe51fad1cf74eeb079e33dad1cf7ceeb4f8e33dadbb97cfd364fe32fcc87f987f34e3e11fcd1e78cdf3473de3bcd2e788f7347ce33ecf1f97cfd363de03cef0f774f3bc3de82eee9b774f3be3dea3aef0f784ebbc9de1,0x1fcd13f88bf30e9e33dce3c77c7f34f8e337cc87f84eeb41fe71fae13f68beb279e53dae1cf78eeb479e33dad1f980fd3a1fe41fcd07f947f38cde52fcc9e78cdf3873dd3bcd36790f7347ce33ece9f978fd363f980fec87f703fb61fe217ed87f94b7ae1fde1dec13f80bbae1fe01eec1cf6cebae4fdf2ded87f8c77b41fe11ded19f887bb04fd8,0x1ded8f764ebb83dda1eed1f378f3b83f5a3ed08fe84f3b41fda1f708ef603fb23eda39ed0fb689fb63eda1def0fb686fba3eda1f6e9fa747bc23f5a376c9bb643fb41fe20fee07f945fb81fe217ed87f88ebb41fe21eed13f80bbb01fe21dee0f77077b84fdf2dec99f907bb41fe21eee0f76c7bb6cddf2eecb97a0dbb8f1dd3aed07f78fe343de3,0xff01de64f7327da03e729f6703fb23f9839ec0fe609fac3f981ded8fe60ebb63f981eed0fe607dbe7b9a3dcd0f76cf9ce5ee41f6e9fc787ec03fa23ecc07f7c7f3237de1fcc87f8c7f323bdb37cd07f78ef306f9e1eee1f65c3fb02fd70fec87f603fb63ddc66ed8f770d7bc3ddc3aee0f770f3bc7cdb1ef08fd68fb425fa01eed0f769c7b03dda,0x37cc9be64df3237d837cc87f6c3fb41fd90fec9cf70fe3a3ddc1dee9f65c3fb82fd91bee0fe5c7f2e3f5b1fcb8fe5c7f2e3f970ff20f7606fbc3dd80fee8f76477c079da1bee9d7607bbc3ddc3f8e07f987dc43edd1ded0f7743fce3dd839f10f7609fc45dd63cf11e764e7ba75d83cf01f680faba7e5a0ff20fe64e7c43f9927f197e5cf3c66f9b,0xfef8df605fc23dd839ed9e764f3b23f9a1bf09dd606fc87b9a3f8d8df84afce1fd81eec1cf607bb04fd61eec1e7647bb07ce33eaf1f6847bb03dd81eec0f7607db03ed81f6c07f747bb037d91eec87f7c7bb03bdd3ced0df78ebb079e33eae8fb707f303dda0ff10fb707dbe6f990fed0fe60e7b43f9827ee0fe60f3ba73da1fcc1f980df326f99,0x1eec16f589fc03bda27ed17764bbb25f9c27ee8fe78beac4fdb1fad97e589fc45f990ff28bf6c3fd05bd70fec0f760e7b03dd81ded8df647bbc3dde3ed08f7607db01fdc1dec0df6c77b01fda1dec0ef606fca67dd1eee8bf745fba7b5a17ef9ee7cfe3a1fe50fec0f7609fac3dd839ec1f578fb423dd81eec0f7607db03ed80fee0df603fbe3bd8,0xfef9e768f3b23f9a0fef0fd603fc43f980fec9cf609fac79d939ec1f38cfabc7da11eec0f7607bb03dd81f6c0fb607db01fe41bec15f583fc85bd83aeb87f847bb63bd80ff10ef70cfc03ddc1eee1fc683fbc3f9b3bac07f887eb43f980ff28fe683fc43bda0fed0f7609fac3bdb1bed8f7847bc27da11eec0fb603fbe1fd727ee96f58bbac4fe0,0xe4f1f4774f3baf1da9cf23c76f33bef1dbe4f4bc76fc3baf1daf86f9e78db73539dde5cc6679f3733c9e3e9cef877eb72ff0e36dcd7c57de6b679e679adce78796b399dfd9adf279fa6bbe1dff1acfc39de6b7da5eed4e3e684f3d2f39b9cf13ec7733c8fb1d6ed1bec71db40fb1bf8d23ce6df34ff19c7d503ec7477b02fd71eec07f7c77b01fe1,0x3cf11be65e6b477570ff18fd603fc6775927ec97d58f3ce7b5c3cf11ed64fcc67e9b79ae1de5c3fc83f980ff18fe609fc05f963cf09be68f3be7b993e711f675ecb47e990fed07f6c3fb21fd93cee3c76e73b8f1db3cf32e76f33b6f1db3cf0b676a73c759dce4efbc76cf3c2e9db9cf0da76f33c7a9dbf0ecbc76cf3bcf1db9cf05c77333c1b1db,0x1ef017b5c7bb63f5c0fef0fb745fba3bd91bf407fa05fb81fd60fed8df683fb837d90fee8df605fb63ddd1bee1ed643fbc37dd0fee0ef6077bc3bd80fef87f609fb25bd60fef0bf5c3fc02fd835f0977603fbc3dd80fee9d7609fbc3dd739ed9d75c3fbe3dd90ff28f7609fb45dd633ee9b764edc25f980ff18fe5c3fc2779927f08fe5cf3c47b9c,0x17ee07f787bb037dc1eec07f747bb037db36ec0df7077c23ddc1df00ef707bba1fdb1bec07f6c77b21fda1bec0bf687bba3f590ff00ef605fba3bd827ed0ef60cfba3dd839ed9d75ce7b67ae23b709cf74e7b8775779ae1cf7c3fb837d81ded8df603fb057d635ed17760ebae1fdc1fac0df647eb04fd81fac0ef707eb037d91fac1bb747dc43f5c,0x17ed07f645fba37dc1dee8f76077bc3be41df18ef8477c63bdf0fed8bf605fb03dde39ec0fd643fba1fdc1dec07f78e7b875d71bee0ef8c7bb03be21df00ef7c77c23be51df007f743fb81fd80fed8ef647bba73d83f2e07f703fb81fd90fec0ef605fb23bd817ed8df6477b65dd61ded8ef7877b83bd91df08ef643fb62fd80fed8bf60e7b03f59,0x4df1acf71a7cc5ddd1df29d77267c475dd4df0ad77197ccd5e171f039774f3ce5f9d1df135e7937ca9f9e6cf236e81d5c65f9d78f173680e7baf3623cf69dd7477d4d7614df02dd6db3d4db61f1b0b9d75e3c6f35e6f3437a8477d0779e1df31de7537ccb79c6cf335e7fc6c0e79d78f07c681e9c7f1a1f3313da7c77b22fd71eee9cf5c7eb21fdb,0x17f087f687bbc3f971fcb8fd6c7f2e3f971fcb8fe5c3fb41fe10ff407f80e7ae1fde0ff187f887f321fdb0ff107f747db21fdb1f6c87f707db22fdb1f6cbc7707db273d81eee8fd647dbe7e9b0fee0ef80e7ba3bdd39ee8ef9c77ba3bde39ee96f78b7ba3be72dee96f70bbbe3bda17ef9777477c8d5e04df227778d7bae3dd1df19cf74e7c873dd,0xff08df64edc27f1e0fef8f7606fc275d80ff00f76077be3ddb39ef8ef80f3b43f981eef1f9687dc477981f718f77c7dc21fd91fcc1cf787f304fd71fcc1e775e3b87b973e718fe607f347e5e3bcc1de60ef3077983bcc1de60f3b21fdc0fec0f75c3fb21fd70fec87f6c6fae1fd80fed8f75c3fb21fd70fec8ef907f383ede1eec9fc6cfb2e37df,0x3cf11e768e7c679e13cec9f574f9c67d9f3ed01f6803fc83f990ff01de689fc25f9833f29ee747f3279e137cc87f687f3037dc0ff00fe6077c273db1f7087f70f7485fa239ec3d38c7ec63ddb3ecc9de7cfb321fe01fce07f74ef341fe01fce0bf74f73673e137cc87f643fbc3dd81bf09d7603fb23dd91df18f76077bc79da1dec1f38cfcc63ddc,0x33f097d80f6b42fe117ee8f7643fc037df0fee8ef605fbe3bd80fef0ef605fbe3dd83f8e1ed685fbe2fe01bf19d75c3fb43dda3cec0fb74fb3875d739ec1cf60e7b073d83ceb9e760f3b067d90fee87f703fb03f970fec0f7587bac3dd61eeb0fb587dae3bd80fec87f6c3fb21fd91fcb87f703fae3ed81f6c0f7683fc83dd839f01d7609fc45dd6,0x1f6c07f786fb037d81eec07f7877b21fd81eec07f90fe3677580ff28fe683fc01fd81eec13f58f3b27d5e3ed08f7607bb03dd81f6c0fb603fba1fd80fee16f58bbac2fe327ed8ef643fb65dd627ed8fe603fc25f560ff017e603fc22fd70ff207f607bb037dc1eec1e76477b67ce31eef0f7887bb03ed80ff08ef606fbc73d70ff096f583fb66dd8,0x7d8e2f3a1f63cdceb7d8f79380f735e1e27d8e7a56dd6b075e275ac4d77ad6b195dad5ab71786e6b7e55b75ac7878fc6b2faa27d8f7a668ebc2eb989aeedae5f2bc5ab96e2edf2e63cb36eb98f0f078e65f1cbe99bf52dfaa6877b01fe017eb8f7603fc03bd90fec0f7603fc03f980fed0fd603fca3f9a0ff20df803fb63be11dee9f38c7bc23de2,0xfed87f843fc61fde1dee1e771d3c81fe43f8d19f983fba6de10fec0fe607f303f5c1fcc0fe607f303f983aedba7626bb0e9d83af0ad7632bace9d83aeeb575e6bbb55d7caee9e768ebbee5d99aedd975b2bbfa5d63aee397626bb0e5d85aee39761abbee5d8f0eeba760ebbae9d89af15a75f2bc1a9d6e2f272763c3bce9d77c719d798f7347ce5,0x79cc9de78f3b279d91ded07f64ebbc3ddf35ee87f7477b41fdc0fed87f707eb037db1fac13f607eb03be01fac0ef707eb03ee43b700fd743fbe5ed71dec8fb783fbc1fe02fcf8fb74ddc073df0fef0df70edba1fd81fcd9f37cfe383f621fce0fe707f383f9c1fce0fe707f3837e01bec1bd60ef381fd80fec87f687f361fdb0fec07f683fb43f9b,0x1fac87f7477b01fdc39ed9d75c77b01fdc1bf10df7c77b037dd1bf10ef843fba1fdb0fec07f7077b23ddc2eed87f6cfcb81fdc0fec07f603fb037d80fec8ef605fb037d92deb0df706fb637df1bee8df646fc437db0fee8f7606fb63dd80fef0f7603fc237db1df28f78477c03bdd1eee8df787bb06bdf1eec13f6c7bb02fde1eec0ef6c7bba3be0,0x71f04f673d1cc6f9933ee39d806fd46f5c39f01dd692fbaaf599cf71ed7dc7c0e75cf4b2bad76dcc67e9d73d31be726dbe6f9c4bf12be6673cbc79c71f07967bc73eeb9e7671f967fccc2ee9d1dec8bf5c7bb879d93bac87f783fb43f970fec87f643fba1fd90fed07f645fb237da1dec0df786fba37e11bf10df806fc437de0fee87f605fb03ddd,0x1bed8ef707dbe3de01fb18f7603fc637e417ef07f6c7bb81fd81bf019f706fba3bdd1bed07f7477b837de33ee0df98afb837e72dee15f747bc637da0ff00f7706fb41fde3aeca5f7cbbb837e735ee0df8cd7b697e055ecf478c7bb867de74ee8df94dbb837e336ee25f755bb2e5dc1bed33775cbc2e5de1bf28fe70e7c0779a4bf097e70f3cd3ba1,0xfee0ef607bb03dd83bac07f7c7f321fdc0feb87f8c3fba3bd817ed0ef605fba3dd81bed8ef607f347b5a17ee07f746fbe1fd70fed0f7606fb43dd81def0f7603fc81fd80ff10f7606fbe75d827f00ef787bb837de1eec8ef84f3b43f981eed9f9683fc83ee20feb8fb807bba3ede0fec0fe606fb23bdb1bec8ef6c7bc43f982f6c8bf607bb03be0,0x3aeca77796bae75de3cec8f780f3b2cde13ceca777d73aecddf6cecb9771d3ae79db3dac9776cf6b29dd95dabb9771d6b2f1e479ad1e790bbc27b9976731ee653bccbb9778f1b6e69cbc0eb987ad23ce69f1c5b99b7d503ea683fba2fd717eb8ef607bb03f580ff10fe60e7b079d93eaf1f6847bb03dd81f6c0fb603fb21fd70fec87f5c3fb637d8,0x37ab0df587bb46f5637ab0bf586fac37d51faa8fd547eaa3f551faa8fd547eaa3f581f6d0fd607f3c3f581fac1bd58afae3f5817ed0fe787eb03f581fac1bd587eb03f580feb8df543fae1fd70feb8df547db43f5817ed0fd607eb03f5837ab0fd607eb03f581fcc07f5c3fae37d50feb87f5c6faa3dd93cec8f77cbbb0cddd3cec8f780ebb23dde,0x33eb0df783fbe4fd70fed8ef683fb85dda17ef17d703fb84fda2fae17d70beb83f5817eb0fd645fb04fd779ab1dd683fc43bd90fef0ef649fb85bd77caf9ed6c5fac3ddb1eed39d747bb24fdd2eeb87f64dbb4f1e23aec3f870fd301fe81fcc9cf887f324fe12fcbbe394df38f35b3bcc3c788f7367ce23ece8bf585fba3f582bec0df60ddba3f58,0x27f28ef6cdec41fdd17eca9f7c3faa2fd91fac1cf6c7eb079de1fac1f961fc387e583f2c1f960deae3ed927eb9dd60eeb4db5f3dadbf870fcb03ddc17ec07f643fb82fdb1bec87f645fb41fdc0fee87f609fb42fdf3f2c07f703fbc2fea0feb87f687eb03f581fac0fd605fb46ddd6f2b17d7c9fb467db2bee95f683fb27e561bed0df6c6fb82fda,0xdcb4aed7c3fde3fa159f30fe711fbf9da0dc762be8366c0b79bd8f1aee8179c59d9fdf102fa7077b25dd83f2c07f843fbe1fd917eb07f643fb22fd70fee87f6c3fba1fdf0ff187f843fb83bd80fee0ef605fba73db3aeb8df8877c237dc1bef8ef643fba2fd917ed0f7605fb63dd817ed8f7606fb63dd81dee0f76c77be3be31eee8bf703fbe4fd9,0x1f748fb98ef303ee81ef20fb986fb61fda1dee8df6877b83de21fcc0fb803fb83be23dd10fb807bbe3f621eec8df883fc63bde3bcd0bf843fba3de10fed87f811fb64fde47ed87f7077ba1feb1dee07f8c77b88fde4ded87f813bc44fd927ed977787bc1a7631eee23f813bba2fde0fee2b78763ceb5dc0fee2f9719ece3f5c47eda7d6f66b2b75d,0x75cc3c781e734f8e27ccf3e97df5343bd82eeb0bf80beac1fdf17eb87f7877b01fda2beb0f760ebae1fdc3bac07f84ef301fd70ff007f8c5fbc3bd80fee16f585fbc6dd81bee0ef60f6b42fe21eec0df706fc21fda2eeb0df787bb03be23ced07f647dc23ee30ff18df80ebb01fe22eeb0ef78f3b273df1eec8ef84f3b43f981eef9f9683fae3ee8,0x1fac1cf607eb03bdf1fac0fb8c7eb21fdd2fab8fd7c3fb23edf0ff107f843fc41fe41f7387f703fae3bd94eeb9e7647bbe5dd836ef1e7647bc475d91eef1d7653bb6b5d778ee1e7647bc079d966f09e7653bb6b9d766efb6765cbb8e9d77caf1ed64fac67b594eecaed5dcbb8eb5978f23cd68f3ca3dea3dccb978cf7329de15dcbbc78db734e5e0,0x1fb013f88beba73e83bb03e5ccf6c61fe53ed31cfb87f404fe72fcebe3b8df4673e13bd01ee90f74a7ce93ed43b9a8fd441fdb0fec93f60beac1fe217ed07f743fba3bd80fee8ef605fb873db3aeb8df8077c237dd1bef8ef603fba6bdb1eec13f647bb02fdb1eec1d7707bb03bdb1eee0ef8cf74477a03ced1e7645fb675d935ee07f683fae4fd8,0x1eec17e707bae7d6117ec1b760bec637dc3aec1cf747bb47cdf3f8f9f67cfb3e7d9f3ecf9f67cfb3e7d9f3ece9fa7c3fc21fda17ee1be643fb03f5f0fed07f6c5fb61fde1fce87f6c7eba1fda0fec87f849fba1fe727ee87f78e7c21fe81df007fa877c04fe52dee87f84f3ca3de71ef01afa47bc04fe72eeeb97dcdbc875ea3aef07f7cbeca1fea,0x1bef1d76877b879da7e2e9f965f8bc7e5f3ed08bf75f1b6e76279aebcd75cec47e5e7e3007f847bb237dc3aec17b8c7bb23bdf3ced9ed78f3b4fc5d3f2cbf178fcbe7da10feebd569e6bae76279aeb9d88fcbcfc5f0fef8f7646fb675d80fee0f76477ba79dc0fee1d761f8ba7e597e2f1f97c5fb879d973b13cd75e6bc7e5e7e300df907bae37db,0x3aec0ef70f3b43ddf3f2c9f3847ec01fe11eec19f84e7bc73e273708fd81f8c01fe11eec07f707bb03bdd3ced8df78ebb03bdc3ced3f174fcb2fc5e3f2f87f74ebb2e76279aeb9d80fcbcfc600ff08f7606fb875d81def9e7706fba75db1dee1e7647bbe7e593e708fd803fb83dd833f09cf78e7c467e31fb03f17c7ec43dd81fae9d760beb83dd8,0x7d50fc39fb33d3ce1f4cfd7375f54bf9233bce1ee6c7dba1fdc1f6d0df6c7db41fda1f6d0ef6cf5b61fdb1f6d0bf6c7db47f1b1eec0f761f34475d93aecbe68f39c0f9a27c6dbe36dcec4f9a27aad3d569e6baf9a23cec9e765f346faa2fc4f3ec8bf13df89efc4f7e27bf13df89efc4f4fc7be644fc9ffc900df70ebb01fdc1eec0ef7cf3b837de,0x1f6f3e68b39cbb99e1eec8df647db67e9a1f6e1fa7bd3403dda1dee0fb74fd3e3ed93f4efc680f9bafc5b3f501dda0fab7e71f3eada7da57abcf3686eb00fd99dabfcf267aafbb3b1f1c4ece57d512f3a1f545f0e6ec6f7967bd1bef5a27d53fe48ff83efa627d913b379cf34fc5f3ecf9e79de9bc779d7e2eb97783fc0fc717cd17a37df545bc5d,0x3aec0ef70f3b43ddd3f2d1f38c7ec41fde3aec1de68cfc673e263f19bd74f9c21fe01eec0df70ebb03bdd3ced0df70ebb03bdc3ced0f778fcb27ce01fb007f6c7bb067e239efb8f81c7c43f603e7087f7c7bb21fdf1eed07f707bb27cdb17ec1b76cbdba37dd3aec1f9887bbe7e593f2f1e76c7bc25ddd1eee0f77877be76dc3d6e0f7603fb83edb,0x3cee0df74f3b23dde3f2c3d36c7ebcf2dd3aebbd375e9baf4dd7a6ebb369e5b6e3df7d2eb3b683fc673e31fcc8fd89b9b6779d3dcd0df60fe3a1fdd1f6d8df747db61fdd1f6d8ef74df361fdc3bcd1ee707bbc7e9b3e743e68bcb38f9a2ce6fbe68be1cef9a2f2cfbe689f1cbfa243db03ec99f64e3f9bf8d287f8c7bb01fdd1eec0ef74f3b437db,0x17ec1b768f6ba3dd93f2f8f768fcb07e5c39ed9f574fb367d9b3eae9f66cfb36775d3ecd9f97cfb361fdd17ec07f74fcae1fda1fad07f6c3fb2f9a23e753d391b9d0f5a05e763d689b9c9f0df76737937bf245f85eee33bd691db427ba0f4766b370bdb86eea79d1b5b99eb3eaee97acfd6b93a7452edcf1cf87f847bb01fde3aec96f687bb02fdd,0x1fb01fa883fc23dd91bec9d7683fb83dd91dee9e7753db475d83ed00f770fcb6f4dc3bae0bf70f3b47cdf71f03cb6c3fc8b3dd3bcc27b747ec0bcdc1def8f7643fba3dda2ded8f7645fb86ddb796e9d760e7ba79da7c6e9f380fb40775c1eefbd95cf9be7d9e7a6e38f81e5b61fe459ee9de613eb8a7dd1fb00fd883fb23dd80feb8f764beb63dd8,0x3f2cbd370eeb81fde3aefb8f81e5b61fe33bcd27b794fbc3f605e6f07f787bb037dc3aec0ef74f3b437dd3aec0ef74f3b43dde3f2c9f3807ebe1fdc1eed1f378cfc273de0ff29cf80cfc43f605e6f0ef7c7bb21fdd3aed07f707bb273de3aec1cf74f3b4f8dd3e700f77cfcb27ce03e709dd705fb879dd3e6f9f678cfc273de3bcc07f9167baa7de,0x7cd11e774f3ba67e13bcc1de69f34479da3ced3e373e33cf8e37cd0bd95decaef4dc7d90fa67fd33fe99ff4cfbe681f63fe99ff4cffa67cef49379c778cf96706fb875d90fee0f76477bc79dc1bef9d76077ba79da1eef9f964f9c03f5f0ff00f768cfc273de39f129f7c7ec27ce00ff00f7683fb83dda1dee9e769e5b675d839ee9e768fb423ddf,0x1faf0f7607eb63dd92fae0f7606fb275d91dee8f76cfcc43ddb3f2d1f974cfba7d5e3ece1f670faba7d9c3ece1eb78fb387d9c0fee87f685fb87e560fec0fd703fb41fda7c72bd699d9c47ce77a722f39dd9c4dce5bc6ebe691f64bf85ebe317957df3433ce31f6d9db8c5fb81fda1ef00df74ef342fdc1eee8f7687bb4f9a23aef9d77df3479ce0,0x3cec8ef78f3b83de23f2e1f384f9c26f5d0ff09d769e73c67e13bcc3c785cbca3f613e7087f947bb437dc3aed07f787bb4f8e03ceca777cebb03de13f2e3b374deba2fdc3cefb9b81e73ef1e17c719de68f6c0f8e01bf18f7686fb23dda2bef8f769cdbe6dd939ee9d76877bc79dc3ed01bd747bbcee5b766eb9b81e73cf1df7cb19de69cbca7b5e,0x3e708fd743fc83dda33f0bce78e7c6f8e23bcc397947ec2f8df0ff18f7683fbc3dda7c6f9e765c7b875da1def1e7707bbc7e5c766e9bd743fb875d973703ce79f1c6779872f29ed79f1be1fe01eec0df70ebb23bdd3ced0df70ebb03bde3ced8f774fcb47ce11fb007f747bbc67e139f01cf84cfc63f607c7007f947bb637dc3aec87f847bb63bdf,0x7a713b39fc9bebce87a715d36cebba7cdf7aadbe691f647f85e1f6d3f174fabbf0e47c71bcb7df1d1e8de1eee0df707bbe1fda1bed9eb6c5fb63ddd1eed0f769f34475d93aecbe68b39c4f9a2f2ce1e77cf3beee5b772dbb375f641d99eeccf7667bb33dd99eeccf7667a5f37cd9f1bee1d7643fbc3dda1df01e765c7b875da1def1e7707bbc7e5c,0x5b6d1eb64f9d79d9e5e73bd39371c2ddafda70376b37344dda87d927e175bb569de33dd1673887dbc5eeb5b718bf5c5fb637dc1eef87f786fba1fd917ee0f7707bb01fda7cd13b395f34574e576735d6a1f1cdfa1f3db19f68d3bbe1fda1eec07f707bb02fd936ed0df60ebb676e11dec9e764fcc43ddc3f2c8fb789fbe3de20fee8fb707dbc7ce7,0x1f6f1f381ed38fc9efc91fe17b794cece53d6e9bb78e7e63fa21dee1de7cf7407f210fef8fb68edb41fdb1f6d0ef6cf5b61fdb3bcd0bf747bba7e9c3e743e68979caf1d93aeca9f7fcb3a3dda2fcf9de6bf4427b619ece87f787bb41fdf1eed3d3805fb66dd72f6f8df68ebb01fdb17ed0fe6077bc79db1fcd1f9847bbe7e583f2d87f707bc437da,0x1eed8bf786fbcf4e4ce6f7c378f9e6f4e37ad5be699f655f85e7e3b0f7a0f7423edd0fee0bf6cf7383ddf0fec8df743fb83bdc3bcd0bf707bbaece65e727c391d9cfb4e47c747e884f6c25de30fee0f7643fbe3dd93e6f8bf70dbb437db3aed0ef707bba7e631eee1f9787dc01fe01ef107f6c7dba3ede3e74bb389d9c5f0dfd6cf7937f6b4779a4,0x1eec87f747bb03bdc1eee0df74ebb07e5e1f6f9f38c7bc65de117ee8df7cebba7ada3f2cbf1787ec079e46ed11e77ccfbe67e13ed08fb907bb21fdd1eed17b947bb22fdb36ed9db78ebb27da43f2dbf170fcb03bda7c6ebf171f8bce75e3f2d87f783fb41fd90fec9be683fb273dd0feb9f3883fbe37e00fee07f709fb03f603f2cbf184fb423dde,0xfc90bc793e1cddc693e711f38df8bc7e623f343f17cfccafa5b7e2f71d903fbc3dd839ee0f7609fb43dd81dee0f760ebba3dd81eee1f674fd4af8dc7c6e3e370dbbeee5b3baf07f6c7bb81fde0fed87f683fb41fdc0fecbe389f2c6dce77cb13b39df2c59cdf7cb1796adf2c4ece87cb176a7bf0c0faa3f8afbd96be2bff862ecaf07f847bb037dc,0x1dee9f965f63c3f601eef0f76c6fbe2fdf3ed087f7c7bae1fde1eec17d6c7bae2fdc36ec1ed74f3b07da33f2ebf178fcac37d97aacbf169e6b2fc5e3f2f1f38c6fc41fdc1f6c8bf805fb83f603f2cbf180fb423de11eed9af88e7c05fa10fef87f743fb43f9b0fee1e7603fb4f4e3fc529f3a9e9c9dca47a71673bf69bddcae7c727b2a3c9bff920,0x71eff9576f8c47ce23e703f16cf9c47ce27e2e78d7c3fb83dd81bef0f7603fb83dd81df18f760e7b83dd879ad1f37cfcba3f5e1eef8fe6deab23f5d7b2c1ed6df1c4f9636e73be589d9d0f962ce6fbe589eb53e5a97d51fe183d53de95f772cfa577e8bb795d0ff00f7606fba3dd90fef0f76077bc3ddc1dee1e768fcc43edd3e7107f745fc037d9,0x3e7007f887bb037df3aec8ef80f3b21fda1eec9f38cfcaefc5e7e2f3f179f8ba73df33f08fd8cf9c41fe01f6c9cf806fba76d80fee0fb6477be7adb1f7207f747db467e417ef1bb6c7dc83f601eef1f960fcc27cdf3e711f38cbdbe3ddb33f11cf847dc0ece4fc301f3b5d9c57ca97a722f3af59bcf8e2f8713d981f8c4fc613f308fb8bf247f922,0x1fb01f3809fb63dd91bef1d760b7b679db3e728f778fcb01fe01eecb7379b9bcde5d39f099f887ec2dcdc0ff20f76c6fc075d80fee0f76c77c879da1def1e768f9c63de13f2e9f3807ec01fdf3aed9cf80cfc273e033f08fd8db9b81fe01eec0df70ebb01fdc1eec0ef7cf3b61fdc3aec0f778fcb8dcdc1fb00bf70f3ba67e239f099f90e7c03f60,0x3f2c9f99cf9c23ddf1eed8bf786fbcbce37c731f3af78c6f4e47c723ec911fba9dd75e74379c83fb43dd81bec8f76077b83dd81ef10f76c7bb22fe00fec0fb69f1c4f9621eec07f807bb2dcde6e6f3e58bc9c5f0eb7cb37e175f547b95e5f2bee57b72bdb95edcaf6e379b9cfb95d0ff00f7606fb875d81dee9e768f9c87ce16e6f1f388e7c267e2,0xde31f9381eb51f8617d51be588fcb2f962be333e5843fb83dd81bee0f76477ba79da1ef18fb7c3fc03dd81bee1d7603fb83dd81dee9e76877ba79da1eef1f964f9c23f600fee1d760e7c067e139f019f847ec07ce13f3313f7c7bb437e13aed0ef90f3b61fdd1eed0f78cfcb27ce97e313f184e7c43f613e7107f5c6fbc1fdd1dee8bf785fb83f60,0x3aec3f181f8c07e5e73b13cd74fcc87da173b2bcd78fcbcfc600fee07f60fcba3ede3f2e9f974fcba37de17ef0fd80f9d0f8e6ce6f5f1e5e9c5f0e37cd207fa0fac6fc707e38bf1a83fb23dd81bed0f76077bc3dd81ef10f7787bb23edd0ff10f75c6fbe75d71def9e7647bba7e57676f97759b9bcecde7730373799dba73e11fb137371f1c4f962,0x7c6e39d95ecbff25cfc307e17bf0bdf85efc2f1f37ff0bc1fdc1eec8df78ebb03bde3cee0f780e7c0e6e21fb03f1803fc43dd91bef1d76c77bc79dc3e709f398fcd073e033f18fd81f8be1fe21eec8df78ebb05ee31eec8ef78f3b67b5e3cedbf181f8c07e5e3ed0bcd79cec0f35d73b11f979f8be3f651eec8df74ebb45f5c1eec8ef70f3b83f5d,0x3b6c8ef74f9b23f611dee1eb6cf3c467e0796e99f8cf3c0abdc1fb09f3883fc23ed935f10ef70ddba1fdf1f6c8f774f9ba1fdc1f6d0bf74ddba3f6037710fb74fcb66ee233f0abb647bb43ee56b6d8bf68cfcef2e20fed3e3887bc879de7c712f384f3bcf8e536ef3a771f34c75de78ef8f764fcccfa591eec9f3997cb8fa597aacbcd79dcb7ea59,0x3cf1acf747ebe7ce20fef8f75cebb05dd91eeb8bf74f3b63ddf3f2c1ed6c6fb43ddc7c6d1e759f1b4f8da7c6d3e369f1b2fc5a736d9bd7cf9c41fde1f6c87f6c7db61fdf1f6c99f845fba6ed91bee1db5c77bc7cd97c709eb887dbc7e591fb01f66cf3c47ae21eeebba7c77b41fe379afbcb783fb41fe11f6c07f78f5b21fe11f6c0bf70f9b237da,0x5e6d87f887bb41fde1eed0ef74f3b637dd3aec0ef7cf3b43de03f2c9f3887ec41fdc36ed1f390cfc4f1de33f11cf887ec27ce30ff08f7646fb675d81ded9e7686fb875d81dee9e7687bbe7e593e710fd803fb63dd933f09cf80e7c467e11fb11f5883fc03dd80fee1e7603fba3dd81bee1d76077ba79da1eef9f964f9c43f6017ed9b76ccfc673e0,0xe671be38be1c4f4e2fa31f9673c9bee9d7f46ffa37fd1bfe8dff16ff667fe1bde4def62f55b703fbe3bd817ee8ef643fb63bd817ed9e76877b87e593d701f674eeb476e137d099f8ce7c06be033f08fd755db837db3aec87f707bb03bdc3cee8df74ebae3bde3cec9f38c7bba7e583e6fbe674eeb61fdf1eec1eb8579bc67e339f01cf894fbe3f5f,0x3dac9f3883fc237df1bee1f3683fba67d91fb00ef7877be3bde5ed18ef6ccfc237df0fed3b39bd3427cea76714f391e9c6bced76713c768ef38f8e4ed8ebe58fd640e3e0f0ee9f388f9c0f8da0fee8f7606fbe3dd80fef8f76077be3dd839ec8f770f5c23dde1fac0f784ef3e3be03ced0df65e9c4f8e21eec07f7c7bb0f8e2ea71be38b39c0f8e2,0x3e759bb943fb07ce23f331bb8c7bb64fd90febb738ba9c4f963ed90b1f9b93dc7ce23e743e36cf9c0f8dd0fee0f7609fb83dd83aef0f7607bc23ddf3d71ba778ebbaf4e27c723b3a9f1c59cde7c713b39fe8c6f5a1ea7036767e1c9d4de0ff00ef603fb63bd81bed9cf6077b83f591eef1f3783fbc3dd61eeb1d7587bb62fd81eed3e374f3acf8db,0x76733d6a1e9c7f4637ad1ad76d73aedce3c9f007f7c77b02fdb1dec8bf6c7bba37db39ec0ef7077bc7e591def0f7785fba2fdd3e7087f7c7bae1fde3aeb8bf74f3b237dd3aec0f77cfcb83f5d1ded9e7583fb23dda33ee9cf7dc7c23f5f3e7107f845fbe2fdf0fec0fe783fba73d939f08fd805fba2fe017ef8bf785fb667e11bee87f69b9c7d9a1,0x1eee87f6c9fb057e01fb00df7cfcb276e11bef0df6c5fbe37df0fed2f395f1ca7ce82f731f389d9c87ce22f72379a4bdc6bcee7a71be39369bf9cef7d91fe181f64e8fe14eee37394f9c47ce73e713b378cfb01fd73e7107f6c7bb037d91eec0ef707bb037db1eec0f7687bb63ddd1fac0f7907bbc3dda1bec3d389f1c43dd87c7137395f1c4dda7,0xfee8bf6c6fb23f9e37cd87f6c3fb83f5e1eed87f6de9c2f8e23e733e38b39bceda77672bd6a2e9b9f4617ad09d778f3b2bce3c5f107f7c77b01fe01dec0df70f3b437dd39ec0ef8877bc3f591eef0f77c3fc23ddb0fef8f76c5fc079db1bee1d75cf9bc3de03f2c9f37c7ec01fdc36ed0ef88f3ae3f9933eeb4f84eeb47cdf3e7107f806fba1fdf,0x6e717638bc9c0f4db3e70fe479f2c9799d63f2b577a79c4bcee6bcff1e8c3fb63dd80fef0f760e7b23dd81dec0df787bb03dda1eec8f77c7eb07ce33aec07f70edb03bdb1bed9e76cbeb837dc3dcc0ef803fbabe5e3f2d9de70ef307d5d1fcd1de60ef3077983bcc1de60f7363f9b3f4f07f687f3e37da0fee8bf6c3fb21fda0fed8fe787bb61fd9,0x3e6c9f38cf5cc3ee03f2c8fd80f3c47ae21ded07f90f6c07ae10fed07f807db01fdd3d6c87f7c7db02fdc3e6d0df68edb23bdc3e6c8fd8477bc7adb3cf299f88e7bc67e53cef9af7c7ec47ce20ff08fb64d7c23bdb376d87f847db23ddc3e6d07f707db62fdd376e0fd80ddc63ede3f2c9bb84cfc26ee317ed19f94e7c21fda6e737a670f9d4dce4,0x3e7419f88e7c079e639ef8fd74f9c41fe11eec0df70ebb01fdf1eec0ef74f3b63bdc3cec9f3887bb87e5a3e728fd7c3fb675d839f019f88e7c667e01faf9f388ebb03dda3ced0df78ebb03de21fb187f707bb6f8e03cecbe381f1c0f8e07c703e37ce7c0fc60736f8fd74f9c41fe11f6c87f747db61fe11f6c99f8c5fbe6eda39f00df70edae3bdc,0x35f099f887eb86ee30ff00f7603fbe3dd81df01e76c6fb875d81dee9e7687bbe7e5a3e710fd843fb86dd833f11cf80cfc273e11fb01f3883fc03dd81bee1d76077ba79db1bee1d76077b879d91eef1f964f9ca3f5f0fef8f760cfc473e039f199f807ebe7ce20ff00f7603fb879d80fef8f7606fb875d81dee1e7647bbc7e593e728fd7c5fba6ddb,0x1ef21f39df1caf4e2ce6f76399e9c67cf07cd13e589f3481fe21ef08df707bb01fdd1eec0ef707bb037db1eec0f7687bc23de11ef18df61e9caf8e2ea71e7394f3b437dd36ed99f8fc9c1f0df7a71fd1a9eb4af4e23cecbe389f1c4f8e27c710df7c7bb4f4e27e3135b845fb83bd90fef8ef605fba79da1bee9cf6077be7e593d730fd7ccfc073e0,0xce70ae789e3b7f0e86ceff4773cb42e9ddf0ecfc397f246f9a67cd39eb79f1c21fe41eee07f7c7bb83bdd3cee0df6cebb43be23e708f77cfcb87ce21fb09de61cbc4f1e079cf31f8cdeba7ce10ff08f7686fb875d81dee9e7686fb875da1dee0f780fcb4f8df1fb019f84e7bee3e21fb01f384fcbc3ddd1faf17b7c7dbc3edd17ee8df787bbe3f5a,0xfed8f765c7c273de33f08fd78f9c41fe21f6d87f6c5fc02fde1bf08f7746fbc37e31fb00df886fb61fe31bf08df803fb4f4e43d739d779eb403bde6af03d38877bc75dd7cd196f6fc9beeae172eefe179d9c61fe11eec07f70ebb21fda1eec0bf70f3b879da1eee9f960f9c23f5f3b6e19f8ce7c667e11fafb736cf9d479e678edf967273c0f9a0,0xfc303ec891fc49ddb3e7a07f687bb037db1eec0ef7c7bb03bdb1eec0f77c7bb43f581eef8f76c3fbc3bda76713e3887bb0f4e25e733d38ab9c4ece576d43b38fd8c2ece655ef2d75db9c58be10fef8df603fbc3bd917ee1e7686fb879da1bef1f9646fbc3bdd0fee87f743fbc3dd70fee9d75c77b879da1df09e75c7bb87e593e708fd7c6fb875d6,0x1deebb389f1c63dd80ff13d38979c7e5a9f6313b68ed5ba75d9f26f5ab783fbc37d80ff10df606fb879da1bef0fd6477ba1fe11eec87f747bb23bdd3ced0f770fcb41fd91eed3cb6cebaef2da3baf1f38c6fbe3ddd1f6d97e885fc02fde1fb00df7c6fc037e21bed8df84ebc21fda5e723e398f9d21fe03e711f3803fc47ceb7a71be39371bef9a3,0x1dec87f706fb02fdb3ced0df78f3b437de1fac8ef843fc075d90ff00f76477b679de3e720ef80f3b03de03f2c8fd786fbc75d80fef0f760e7c867e31faf9f3883fb21fe017ef0bf786fbe3ddd1bf08fd806fc037db0ff18df886fc41fda3e715e37cf9d67ce26e70de37df2c9eb1d0ff0cd7643fb83dd80ff00f760e7c03dd81ef00fd607bc277a4,0x5e742d779d3b05fa1f2709d769f1b4a7dffc319eb79f1ca1fdc1df18fe78fcc63ddf1faf0f7705fba37db17ef0fd787bbe7ce77c733d38b39bd78dff86fbe68bd2c0f9a50ff38f780f5d037de1eec07f687bb03bdd1eec0ef707bb03de41eef0fd607bbe3dde1ded3b389f1c574e35e71b7395d9ceeda57671fb189d9d06be33aecd738cd7c81fdc,0x27f09cf7c7ec2ecdc0ff18fb60afbc3ed86f320ef78f5b23dde3e6cb79903fb6ced66f31b1f68f3c073e11fb11f3883fc23ed92df00ef74bdb61fdf1f6c0f774f9b41fdf1f6d95f886fbc5edc1fb017b847dc07e592f7113f88bdc81fdc2fb117d8c3fb4ece21bf11b771e9c837de76710df78dbb979a47cd27e178f9dc75e174ec79678ebb569d7,0x2f720df78ebb03be03cec8f780fcae1fdd1eebb3b7cbbacdcde766f3b9859dba73e133f10fd883fc03dd91bee1d7603fc83dd91dee9e76877c079da1eef9f970f9c07ce21fb087f78bbb24fe039f11cf80cfc23f613e710df747bae37dd3aeb99f707bae3bdf3cec87f78f3aeece11eeebb959f2bcecdc766f8fd783fb85dd9766f1f388e7c279e2,0x1fb007f687bc079d9ce6fbb39ae9caf8e23d700f7643fba3edf1f6f8df7c5fb83f5d1eef1f3adf1c4f4e3dc717e175f3461fe61eef8df647bb03bdc1eec0f7647eb03de25e71be38b39bdb4e13ced0df70bbb257e13eac8fb74beb8fc60676d2f6971dbe5dd8ce6f07f7c7baf9cdee66f7398f1dba1fdd39ec07f70f3b41fdc3f2c96f80afc63f5d,0x19cde7a72fa6abf0bc7ce55e713b39f69c5f8613d7087f706fbe2fe11fb00f78f39bc5ee94eedbd3977347f85d5e7107f807bb23dd91bed9d76c77bc79dc3e72bf175b9c0fc5d7e2ebf170e7c667e4]⟩
def test := rowCheck gr hints true 7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b0_128 : Holds test 0 128 := slice_sound (a:=0) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b128_256 : Holds test 128 256 := slice_sound (a:=128) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b256_384 : Holds test 256 384 := slice_sound (a:=256) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b384_512 : Holds test 384 512 := slice_sound (a:=384) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b512_640 : Holds test 512 640 := slice_sound (a:=512) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b640_768 : Holds test 640 768 := slice_sound (a:=640) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b768_896 : Holds test 768 896 := slice_sound (a:=768) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b896_1024 : Holds test 896 1024 := slice_sound (a:=896) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1024_1152 : Holds test 1024 1152 := slice_sound (a:=1024) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1152_1280 : Holds test 1152 1280 := slice_sound (a:=1152) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1280_1408 : Holds test 1280 1408 := slice_sound (a:=1280) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1408_1536 : Holds test 1408 1536 := slice_sound (a:=1408) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1536_1664 : Holds test 1536 1664 := slice_sound (a:=1536) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1664_1792 : Holds test 1664 1792 := slice_sound (a:=1664) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1792_1920 : Holds test 1792 1920 := slice_sound (a:=1792) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b1920_2048 : Holds test 1920 2048 := slice_sound (a:=1920) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2048_2176 : Holds test 2048 2176 := slice_sound (a:=2048) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2176_2304 : Holds test 2176 2304 := slice_sound (a:=2176) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2304_2432 : Holds test 2304 2432 := slice_sound (a:=2304) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2432_2560 : Holds test 2432 2560 := slice_sound (a:=2432) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2560_2688 : Holds test 2560 2688 := slice_sound (a:=2560) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2688_2816 : Holds test 2688 2816 := slice_sound (a:=2688) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2816_2944 : Holds test 2816 2944 := slice_sound (a:=2816) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b2944_3072 : Holds test 2944 3072 := slice_sound (a:=2944) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b3072_3200 : Holds test 3072 3200 := slice_sound (a:=3072) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b3200_3328 : Holds test 3200 3328 := slice_sound (a:=3200) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b3328_3456 : Holds test 3328 3456 := slice_sound (a:=3328) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b3456_3584 : Holds test 3456 3584 := slice_sound (a:=3456) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b3584_3712 : Holds test 3584 3712 := slice_sound (a:=3584) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b3712_3840 : Holds test 3712 3840 := slice_sound (a:=3712) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b3840_3968 : Holds test 3840 3968 := slice_sound (a:=3840) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b3968_4096 : Holds test 3968 4096 := slice_sound (a:=3968) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b4096_4224 : Holds test 4096 4224 := slice_sound (a:=4096) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b4224_4352 : Holds test 4224 4352 := slice_sound (a:=4224) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b4352_4480 : Holds test 4352 4480 := slice_sound (a:=4352) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b4480_4608 : Holds test 4480 4608 := slice_sound (a:=4480) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b4608_4736 : Holds test 4608 4736 := slice_sound (a:=4608) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b4736_4864 : Holds test 4736 4864 := slice_sound (a:=4736) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b4864_4992 : Holds test 4864 4992 := slice_sound (a:=4864) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b4992_5120 : Holds test 4992 5120 := slice_sound (a:=4992) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b5120_5248 : Holds test 5120 5248 := slice_sound (a:=5120) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b5248_5376 : Holds test 5248 5376 := slice_sound (a:=5248) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b5376_5504 : Holds test 5376 5504 := slice_sound (a:=5376) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b5504_5632 : Holds test 5504 5632 := slice_sound (a:=5504) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b5632_5760 : Holds test 5632 5760 := slice_sound (a:=5632) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b5760_5888 : Holds test 5760 5888 := slice_sound (a:=5760) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b5888_6016 : Holds test 5888 6016 := slice_sound (a:=5888) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b6016_6144 : Holds test 6016 6144 := slice_sound (a:=6016) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b6144_6272 : Holds test 6144 6272 := slice_sound (a:=6144) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b6272_6400 : Holds test 6272 6400 := slice_sound (a:=6272) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b6400_6528 : Holds test 6400 6528 := slice_sound (a:=6400) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b6528_6656 : Holds test 6528 6656 := slice_sound (a:=6528) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b6656_6784 : Holds test 6656 6784 := slice_sound (a:=6656) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b6784_6912 : Holds test 6784 6912 := slice_sound (a:=6784) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b6912_7040 : Holds test 6912 7040 := slice_sound (a:=6912) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b7040_7168 : Holds test 7040 7168 := slice_sound (a:=7040) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b7168_7296 : Holds test 7168 7296 := slice_sound (a:=7168) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b7296_7424 : Holds test 7296 7424 := slice_sound (a:=7296) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b7424_7552 : Holds test 7424 7552 := slice_sound (a:=7424) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b7552_7680 : Holds test 7552 7680 := slice_sound (a:=7552) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b7680_7808 : Holds test 7680 7808 := slice_sound (a:=7680) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b7808_7936 : Holds test 7808 7936 := slice_sound (a:=7808) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b7936_8064 : Holds test 7936 8064 := slice_sound (a:=7936) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b8064_8192 : Holds test 8064 8192 := slice_sound (a:=8064) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b8192_8320 : Holds test 8192 8320 := slice_sound (a:=8192) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b8320_8448 : Holds test 8320 8448 := slice_sound (a:=8320) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b8448_8576 : Holds test 8448 8576 := slice_sound (a:=8448) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b8576_8704 : Holds test 8576 8704 := slice_sound (a:=8576) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b8704_8832 : Holds test 8704 8832 := slice_sound (a:=8704) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b8832_8960 : Holds test 8832 8960 := slice_sound (a:=8832) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b8960_9088 : Holds test 8960 9088 := slice_sound (a:=8960) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b9088_9216 : Holds test 9088 9216 := slice_sound (a:=9088) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b9216_9344 : Holds test 9216 9344 := slice_sound (a:=9216) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b9344_9472 : Holds test 9344 9472 := slice_sound (a:=9344) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b9472_9600 : Holds test 9472 9600 := slice_sound (a:=9472) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b9600_9728 : Holds test 9600 9728 := slice_sound (a:=9600) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b9728_9856 : Holds test 9728 9856 := slice_sound (a:=9728) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b9856_9984 : Holds test 9856 9984 := slice_sound (a:=9856) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b9984_10112 : Holds test 9984 10112 := slice_sound (a:=9984) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b10112_10240 : Holds test 10112 10240 := slice_sound (a:=10112) (k:=128) (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem b10240_10298 : Holds test 10240 10298 := slice_sound (a:=10240) (k:=58) (by decide +kernel)
theorem u0_256 : Holds test 0 256 := join_blocks b0_128 b128_256
theorem u256_512 : Holds test 256 512 := join_blocks b256_384 b384_512
theorem u512_768 : Holds test 512 768 := join_blocks b512_640 b640_768
theorem u768_1024 : Holds test 768 1024 := join_blocks b768_896 b896_1024
theorem u1024_1280 : Holds test 1024 1280 := join_blocks b1024_1152 b1152_1280
theorem u1280_1536 : Holds test 1280 1536 := join_blocks b1280_1408 b1408_1536
theorem u1536_1792 : Holds test 1536 1792 := join_blocks b1536_1664 b1664_1792
theorem u1792_2048 : Holds test 1792 2048 := join_blocks b1792_1920 b1920_2048
theorem u2048_2304 : Holds test 2048 2304 := join_blocks b2048_2176 b2176_2304
theorem u2304_2560 : Holds test 2304 2560 := join_blocks b2304_2432 b2432_2560
theorem u2560_2816 : Holds test 2560 2816 := join_blocks b2560_2688 b2688_2816
theorem u2816_3072 : Holds test 2816 3072 := join_blocks b2816_2944 b2944_3072
theorem u3072_3328 : Holds test 3072 3328 := join_blocks b3072_3200 b3200_3328
theorem u3328_3584 : Holds test 3328 3584 := join_blocks b3328_3456 b3456_3584
theorem u3584_3840 : Holds test 3584 3840 := join_blocks b3584_3712 b3712_3840
theorem u3840_4096 : Holds test 3840 4096 := join_blocks b3840_3968 b3968_4096
theorem u4096_4352 : Holds test 4096 4352 := join_blocks b4096_4224 b4224_4352
theorem u4352_4608 : Holds test 4352 4608 := join_blocks b4352_4480 b4480_4608
theorem u4608_4864 : Holds test 4608 4864 := join_blocks b4608_4736 b4736_4864
theorem u4864_5120 : Holds test 4864 5120 := join_blocks b4864_4992 b4992_5120
theorem u5120_5376 : Holds test 5120 5376 := join_blocks b5120_5248 b5248_5376
theorem u5376_5632 : Holds test 5376 5632 := join_blocks b5376_5504 b5504_5632
theorem u5632_5888 : Holds test 5632 5888 := join_blocks b5632_5760 b5760_5888
theorem u5888_6144 : Holds test 5888 6144 := join_blocks b5888_6016 b6016_6144
theorem u6144_6400 : Holds test 6144 6400 := join_blocks b6144_6272 b6272_6400
theorem u6400_6656 : Holds test 6400 6656 := join_blocks b6400_6528 b6528_6656
theorem u6656_6912 : Holds test 6656 6912 := join_blocks b6656_6784 b6784_6912
theorem u6912_7168 : Holds test 6912 7168 := join_blocks b6912_7040 b7040_7168
theorem u7168_7424 : Holds test 7168 7424 := join_blocks b7168_7296 b7296_7424
theorem u7424_7680 : Holds test 7424 7680 := join_blocks b7424_7552 b7552_7680
theorem u7680_7936 : Holds test 7680 7936 := join_blocks b7680_7808 b7808_7936
theorem u7936_8192 : Holds test 7936 8192 := join_blocks b7936_8064 b8064_8192
theorem u8192_8448 : Holds test 8192 8448 := join_blocks b8192_8320 b8320_8448
theorem u8448_8704 : Holds test 8448 8704 := join_blocks b8448_8576 b8576_8704
theorem u8704_8960 : Holds test 8704 8960 := join_blocks b8704_8832 b8832_8960
theorem u8960_9216 : Holds test 8960 9216 := join_blocks b8960_9088 b9088_9216
theorem u9216_9472 : Holds test 9216 9472 := join_blocks b9216_9344 b9344_9472
theorem u9472_9728 : Holds test 9472 9728 := join_blocks b9472_9600 b9600_9728
theorem u9728_9984 : Holds test 9728 9984 := join_blocks b9728_9856 b9856_9984
theorem u9984_10240 : Holds test 9984 10240 := join_blocks b9984_10112 b10112_10240
theorem u0_512 : Holds test 0 512 := join_blocks u0_256 u256_512
theorem u512_1024 : Holds test 512 1024 := join_blocks u512_768 u768_1024
theorem u1024_1536 : Holds test 1024 1536 := join_blocks u1024_1280 u1280_1536
theorem u1536_2048 : Holds test 1536 2048 := join_blocks u1536_1792 u1792_2048
theorem u2048_2560 : Holds test 2048 2560 := join_blocks u2048_2304 u2304_2560
theorem u2560_3072 : Holds test 2560 3072 := join_blocks u2560_2816 u2816_3072
theorem u3072_3584 : Holds test 3072 3584 := join_blocks u3072_3328 u3328_3584
theorem u3584_4096 : Holds test 3584 4096 := join_blocks u3584_3840 u3840_4096
theorem u4096_4608 : Holds test 4096 4608 := join_blocks u4096_4352 u4352_4608
theorem u4608_5120 : Holds test 4608 5120 := join_blocks u4608_4864 u4864_5120
theorem u5120_5632 : Holds test 5120 5632 := join_blocks u5120_5376 u5376_5632
theorem u5632_6144 : Holds test 5632 6144 := join_blocks u5632_5888 u5888_6144
theorem u6144_6656 : Holds test 6144 6656 := join_blocks u6144_6400 u6400_6656
theorem u6656_7168 : Holds test 6656 7168 := join_blocks u6656_6912 u6912_7168
theorem u7168_7680 : Holds test 7168 7680 := join_blocks u7168_7424 u7424_7680
theorem u7680_8192 : Holds test 7680 8192 := join_blocks u7680_7936 u7936_8192
theorem u8192_8704 : Holds test 8192 8704 := join_blocks u8192_8448 u8448_8704
theorem u8704_9216 : Holds test 8704 9216 := join_blocks u8704_8960 u8960_9216
theorem u9216_9728 : Holds test 9216 9728 := join_blocks u9216_9472 u9472_9728
theorem u9728_10240 : Holds test 9728 10240 := join_blocks u9728_9984 u9984_10240
theorem u0_1024 : Holds test 0 1024 := join_blocks u0_512 u512_1024
theorem u1024_2048 : Holds test 1024 2048 := join_blocks u1024_1536 u1536_2048
theorem u2048_3072 : Holds test 2048 3072 := join_blocks u2048_2560 u2560_3072
theorem u3072_4096 : Holds test 3072 4096 := join_blocks u3072_3584 u3584_4096
theorem u4096_5120 : Holds test 4096 5120 := join_blocks u4096_4608 u4608_5120
theorem u5120_6144 : Holds test 5120 6144 := join_blocks u5120_5632 u5632_6144
theorem u6144_7168 : Holds test 6144 7168 := join_blocks u6144_6656 u6656_7168
theorem u7168_8192 : Holds test 7168 8192 := join_blocks u7168_7680 u7680_8192
theorem u8192_9216 : Holds test 8192 9216 := join_blocks u8192_8704 u8704_9216
theorem u9216_10240 : Holds test 9216 10240 := join_blocks u9216_9728 u9728_10240
theorem u0_2048 : Holds test 0 2048 := join_blocks u0_1024 u1024_2048
theorem u2048_4096 : Holds test 2048 4096 := join_blocks u2048_3072 u3072_4096
theorem u4096_6144 : Holds test 4096 6144 := join_blocks u4096_5120 u5120_6144
theorem u6144_8192 : Holds test 6144 8192 := join_blocks u6144_7168 u7168_8192
theorem u8192_10240 : Holds test 8192 10240 := join_blocks u8192_9216 u9216_10240
theorem u0_4096 : Holds test 0 4096 := join_blocks u0_2048 u2048_4096
theorem u4096_8192 : Holds test 4096 8192 := join_blocks u4096_6144 u6144_8192
theorem u8192_10298 : Holds test 8192 10298 := join_blocks u8192_10240 b10240_10298
theorem u0_8192 : Holds test 0 8192 := join_blocks u0_4096 u4096_8192
theorem u0_10298 : Holds test 0 10298 := join_blocks u0_8192 u8192_10298
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def result : CoJunctionTarget4482.Certificate (Fin gr.size) init.toFinset :=
  certified (hints:=hints) (seeded:=true) (depth:=7) (by decide +kernel) (all_rows u0_10298)
end CoWholeRoot1

end PEqualNP.Outside.L_meta_4482_aux

open PEqualNP.Outside.L_meta_4482_aux

theorem PEqualNP.Outside.L_meta_4482 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : List PEqualNP.CircuitLowerBounds.Gate),   x2.length = (7 : ℕ) →     (∀ (x4 : ℕ) (x5 : x4 < x2.length), (x2[x4].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2[x4].op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x2[x4].inputs.length ≤ (2 : ℕ) ∧ ∀ x6 ∈ x2[x4].inputs, x6 < (10 : ℕ) + x4 ∨ x6 = (17 : ℕ)) →       have x5 : PEqualNP.CircuitLowerBounds.Circuit := { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (2 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };       ∀ x6 ⊆ (Finset.range (17 : ℕ)).erase (9 : ℕ), x6.card ≤ (6 : ℕ) → (∃ x9 ∈ x6, (10 : ℕ) ≤ x9) → ∃ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ) → Bool), x1 x10 ≠ x1 x11 ∧ ∀ x12 ∈ x6, (x5.wires (List.ofFn x10)).getD x12 Bool.false = (x5.wires (List.ofFn x11)).getD x12 Bool.false := by
  exact CoPortRoots4482.conditional (CoJunctionTarget4482.both CoWholeRoot0.result CoWholeRoot1.result)
