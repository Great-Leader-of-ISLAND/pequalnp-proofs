import PEqualNP.Co4358ColorSplit

import PEqualNP.Co4358CornerPost

import PEqualNP.Co4358BicolorBaseWords

import PEqualNP.Co4358PerfectJumps

import PEqualNP.Co4358OrbitData

namespace CoNum4358.Tiny.Reflection
open CoAO3143
set_option maxRecDepth 65536

def order : Fin 15 → Fin 15 := ![7,4,5,6,1,2,3,0,8,14,11,10,12,13,9]
def reverseK (w : K) : K :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 15 => w.getLsbD (order i).val))).cast List.length_ofFn

theorem reverse_bit (w : K) (i : Fin 15) : (reverseK w).getLsbD i.val=w.getLsbD (order i).val := by
  rw [reverseK,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  have bd : i.val<(List.ofFn (fun j : Fin 15 => w.getLsbD (order j).val)).length := by simpa using i.isLt
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bd]
  exact List.getElem_ofFn bd

theorem invol (w : K) : reverseK (reverseK w)=w := by
  have inv : ∀i : Fin 15,order (order i)=i := by decide +kernel
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 15 := ⟨j,hj⟩
  change (reverseK (reverseK w)).getLsbD i.val=w.getLsbD i.val
  rw [reverse_bit,reverse_bit,inv]

theorem injK : Function.Injective reverseK := Function.LeftInverse.injective invol

theorem op (d : Bool) (a b : K) : reverseK (makeKW d a b)=makeKW d (reverseK a) (reverseK b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 15 := ⟨j,hj⟩
  change (reverseK (makeKW d a b)).getLsbD i.val=(makeKW d (reverseK a) (reverseK b)).getLsbD i.val
  cases d <;> simp only [reverse_bit,makeKW,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,BitVec.getLsbD_or]

theorem constants : reverseK 0=0 ∧ reverseK 32767=32767 ∧ reverseK 255=255 ∧ reverseK 7442=7442 := by
  decide +kernel

theorem raw_fixed : (bare.map reverseK).toFinset=bare.toFinset := by decide +kernel

def wire (w : W) : W := (reverseK w.1,(w.2.2,w.2.1))
theorem wire_invol (w : W) : wire (wire w)=w := by
  rcases w with ⟨s,a,b⟩
  change (reverseK (reverseK s),(a,b))=(s,(a,b))
  rw [invol]
theorem wire_inj : Function.Injective wire := Function.LeftInverse.injective wire_invol

theorem combine (d : Bool) (a b : W) : wire (make d a b)=make d (wire a) (wire b) :=
  Prod.ext (op d a.1 b.1) rfl

private theorem read_fee (w : K) : (reverseK w==7442)=(w==7442) := by
  by_cases eq : w=7442
  · subst w
    exact (beq_iff_eq.mpr constants.2.2.2).trans (beq_iff_eq.mpr rfl).symm
  · have m : reverseK w≠7442 := fun z => eq (injK (z.trans constants.2.2.2.symm))
    have a : (reverseK w==7442)=false := Bool.eq_false_iff.mpr (fun h => m (beq_iff_eq.mp h))
    have b : (w==7442)=false := Bool.eq_false_iff.mpr (fun h => eq (beq_iff_eq.mp h))
    exact a.trans b.symm
theorem price (d : Bool) (u v : W) : pay d (wire u) (wire v)=pay d u v := by
  simp only [pay,wire,read_fee]

def Represented (a : Sig) := ∃t : K,wide t=a
noncomputable def renameSig (a : Sig) := wide (reverseK (Function.invFun wide a))

theorem rename_wide (a : K) : renameSig (wide a)=wide (reverseK a) := by
  rw [renameSig,Function.leftInverse_invFun wide_inj a]

private theorem faithful {a b : Sig} (ma : Represented a) (mb : Represented b)
    (eq : renameSig a=renameSig b) : a=b := by
  obtain ⟨x,rfl⟩ := ma
  obtain ⟨y,rfl⟩ := mb
  rw [rename_wide,rename_wide] at eq
  exact congrArg wide (injK (wide_inj eq))

private theorem preserves_proper {a : Sig} (ma : Represented a) (h : proper a) : proper (renameSig a) := by
  have ez : renameSig zero=zero := by rw [←zero_value,rename_wide,constants.1]
  have eo : renameSig one=one := by rw [←one_value,rename_wide,constants.2.1]
  exact ⟨fun eq => h.1 (faithful ma ⟨0,zero_value⟩ (eq.trans ez.symm)),
    fun eq => h.2 (faithful ma ⟨32767,one_value⟩ (eq.trans eo.symm))⟩

private theorem preserves_bin (d : Bool) {a b : Sig} (ma : Represented a) (mb : Represented b) :
    Represented (bin d a b) ∧ renameSig (bin d a b)=bin d (renameSig a) (renameSig b) := by
  obtain ⟨x,rfl⟩ := ma
  obtain ⟨y,rfl⟩ := mb
  exact ⟨⟨makeKW d x y,wide_bin d x y⟩,by rw [←wide_bin,rename_wide,rename_wide,rename_wide,op,wide_bin]⟩

theorem mirror_live {k t S} (h : Live k t S) (hz : t=0) (all : ∀v∈S,Represented v) :
    Live k 0 (S.image renameSig) := by
  induction h with
  | stop =>
    have fixed : renameSig target=target := by rw [←target_value,rename_wide,constants.2.2.1]
    simpa [fixed] using (Live.stop : Live 0 0 {target})
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb ne fresh tail ih =>
    have ma : Represented a := all _ (by simp)
    have mb : Represented b := all _ (by simp)
    have bz := preserves_bin d ma mb
    have mu (u : Sig) (hu : u∈U) : Represented u := all u (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    have child := ih hz (fun u hu => by
      obtain eq|old := Finset.mem_insert.mp hu
      · rw [eq]; exact bz.1
      · exact mu u old)
    simp only [Finset.image_insert,bz.2] at child ⊢
    apply Live.binary (preserves_proper ma ha) (preserves_proper mb hb)
      (fun e => ne (faithful ma mb e)) _ child
    intro bad
    rw [←bz.2,←Finset.image_insert,←Finset.image_insert] at bad
    obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp bad
    exact fresh (by simpa only [faithful (all _ hv) bz.1 eq] using hv)

theorem good {k : Nat} {S : Finset W} (h : Good k S) : Good k (S.image wire) := by
  constructor
  · have live := mirror_live h.live rfl (fun v hv => by
      obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨w.1,rfl⟩)
    have sets : (S.image (fun w => wide w.1)).image renameSig=(S.image wire).image (fun w=>wide w.1) := by
      simp only [Finset.image_image,Function.comp_def,wire,rename_wide]
    rwa [←sets]
  · intro s
    obtain ⟨w,hw,hits⟩ := h.caps (!s)
    exact ⟨wire w,Finset.mem_image_of_mem _ hw,by cases s <;> exact hits⟩

theorem trace {k q S} (h : Trace k q S) : Trace k q (S.image wire) := by
  induction h with
  | done q w a b c =>
    simp only [Finset.image_singleton]
    exact Trace.done q (wire w) (by change reverseK w.1=255; rw [a,constants.2.2.1]) c b
  | @step k q U d a b ne budget clean unused raw facts child ih =>
    have ori : ∀t : K,reverseK t∈bare → t∈bare := by
      intro t ht
      have m : reverseK (reverseK t)∈(bare.map reverseK).toFinset := by
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨reverseK t,ht,rfl⟩)
      simpa only [invol,raw_fixed,List.mem_toFinset] using m
    have eq : (make d (wire a) (wire b)).1=reverseK (make d a b).1 :=
      congrArg Prod.fst (combine d a b).symm
    have source := good facts
    simp only [Finset.image_insert] at source ⊢
    simp only [Finset.image_insert,combine] at ih
    apply Trace.step d (wire a) (wire b) (fun h => ne (wire_inj h)) (by rwa [price]) _ _ _
      source (by simpa only [price] using ih)
    · rw [eq]
      exact ⟨fun e=>clean.1 (injK (e.trans constants.1.symm)),
        fun e=>clean.2 (injK (e.trans constants.2.1.symm))⟩
    · intro bad
      rw [eq,←Finset.image_insert,←Finset.image_insert] at bad
      obtain ⟨w,hw,ev⟩ := Finset.mem_image.mp bad
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact unused (Finset.mem_image.mpr ⟨v,hv,injK ev⟩)
    · rw [eq]
      exact fun e=>raw (ori _ e)

#print axioms trace
end CoNum4358.Tiny.Reflection

namespace CoNum4358.Tiny.ShareGrid.Forest
open CoAO3143
set_option maxRecDepth 65536

theorem mask_opposite {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    {a b : K} (ha : a∈xs) (hb : b∈xs)
    (ok : Corners.pair (prof a (Corners.exclusive xs)) (prof b (Corners.exclusive xs))=true) :
    decide (a∈A)≠decide (b∈A) := by
  unfold Corners.pair at ok
  split at ok
  · contradiction
  · rename_i r hr
    simp only [Bool.and_eq_true] at ok
    let w : Rect := ⟨a,b,r.p,r.q₁,r.q₂,r.n,r.m₁,r.m₂⟩
    have right : validRect xs w=true := by
      change ((a != b) && forced xs r.p r.m₁ a && forced xs r.q₁ r.n a &&
        forced xs r.p r.m₂ b && forced xs r.q₂ r.n b)=true
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨ok.1.1.1.1,Corners.owns ha _ _ ok.1.1.1.2⟩,Corners.owns ha _ _ ok.1.1.2⟩,
        Corners.owns hb _ _ ok.1.2⟩,Corners.owns hb _ _ ok.2⟩
    exact opposite dis good union same w right

def maskEdges : List Prof → List (K×K)
  | [] => []
  | a::r => (r.filterMap (fun b => if Corners.pair a b then some (a.wire,b.wire) else none))++maskEdges r

theorem maskEdges_valid {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    (items : List Prof) (mk : ∀v∈items,∃x∈xs,v=prof x (Corners.exclusive xs))
    (e : K×K) (mem : e∈maskEdges items) : decide (e.1∈A)≠decide (e.2∈A) := by
  induction items with
  | nil => simp [maskEdges] at mem
  | cons a r ih =>
    rcases List.mem_append.mp mem with h|h
    · obtain ⟨b,hb,yes⟩ := List.mem_filterMap.mp h
      by_cases ok : Corners.pair a b=true
      · have eq : (a.wire,b.wire)=e := by simpa [ok] using yes
        obtain ⟨x,hx,ex⟩ := mk a List.mem_cons_self
        obtain ⟨y,hy,ey⟩ := mk b (List.mem_cons_of_mem _ hb)
        rw [←eq,ex,ey]
        change decide (x∈A)≠decide (y∈A)
        exact mask_opposite (a:=x) (b:=y) dis good union same hx hy (by simpa only [ex,ey] using ok)
      · simp [ok] at yes
    · exact ih (fun v hv => mk v (List.mem_cons_of_mem _ hv)) h

inductive Bundle where
  | empty
  | more (left right total : Nat) (leftUsed rightUsed : Bool) (tail : Bundle)

def Bundle.total : Bundle → Nat
  | .empty => 0
  | .more _ _ u _ _ _ => u

def bundle : List Block → Bundle
  | [] => .empty
  | g::gs =>
    let rest := bundle gs
    let l := cov g.lhs
    let r := cov g.rhs
    .more l r (l ||| (r ||| rest.total)) (!g.lhs.isEmpty) (!g.rhs.isEmpty) rest

def ground : Bundle → Nat → Nat → Bool → Bool
  | .empty,a,b,used => used && !(uncoveredProduct a b (estimateProduct b))
  | .more x y u cx cy tail,a,b,used =>
    let ca := a ||| u
    let cb := b ||| u
    !(uncoveredProduct ca cb (estimateProduct cb)) &&
      (ground tail (x|||a) (y|||b) (cx||used) || ground tail (y|||a) (x|||b) (cy||used))

theorem cov_append (xs ys : List K) : cov (xs++ys)=cov xs ||| cov ys := by
  induction xs with
  | nil => simp [cov,Corners.counts]
  | cons x xs ih =>
    change cells x ||| cov (xs++ys)=(cells x ||| cov xs) ||| cov ys
    rw [ih,Nat.or_assoc]

theorem full_bundle (gs : List Block) : (bundle gs).total=cov (pool gs) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change cov g.lhs ||| (cov g.rhs ||| (bundle gs).total)=cov (g.lhs++(g.rhs++pool gs))
    rw [ih,cov_append,cov_append]

theorem used_append (a b : List K) : (a++b).isEmpty.not=(a.isEmpty.not || b.isEmpty.not) := by
  cases a <;> cases b <;> rfl

theorem bundle_eq (gs : List Block) (a b : List K) :
    ground (bundle gs) (cov a) (cov b) (!a.isEmpty)=solve gs a b := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    simp only [ground,bundle,solve,pool,cov_append,full_bundle]
    have h1 := ih (g.lhs++a) (g.rhs++b)
    have h2 := ih (g.rhs++a) (g.lhs++b)
    simp only [cov_append,used_append] at h1 h2
    rw [h1,h2]

def quickPossible (xs : List K) :=
  let unique := Corners.exclusive xs
  let pairs := maskEdges (xs.map fun x => prof x unique)
  (compile pairs (seed xs)).any (fun ls => ground (bundle (blocks ls)) 0 0 false)
theorem quick_yes {k : Nat} {xs : List K} (live : Live k 0 (xs.map wide).toFinset)
    (size : xs.toFinset.card=k) : quickPossible xs=true := by
  have eq : (xs.map wide).toFinset=up xs.toFinset := by ext w; simp [up]
  have l : Live k 0 (up xs.toFinset) := by rw [←eq]; exact live
  obtain ⟨A,sub,na,good⟩ := tight_plus_one l size
  let B := xs.toFinset\A
  have union : A∪B=xs.toFinset := by
    ext x
    change x∈A∪(xs.toFinset\A) ↔ _
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro (ha|⟨hx,_⟩)
      · exact sub ha
      · exact hx
    · intro hx
      by_cases ha : x∈A
      · exact .inl ha
      · exact .inr ⟨hx,ha⟩
  have dis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  have cv : ∀p n,∃w∈A∪B,directed w p n=true := by
    intro p n
    rw [union]
    have cov : unionSep false (xs.map wide)=top := live_cover live rfl
    have bd : p.val*7+n.val<160 := by omega
    have yes : (unionSep false (xs.map wide)).getLsbD (p.val*7+n.val)=true := by
      rw [cov]; simp only [top,BitVec.getLsbD_allOnes,bd,decide_true]
    obtain ⟨w,hw,hy⟩ := (reports_one xs p n).mp yes
    exact ⟨w,List.mem_toFinset.mpr hw,hy⟩
  let c := fun x : K => decide (x∈A)
  let pairs := maskEdges (xs.map fun x => prof x (Corners.exclusive xs))
  obtain ⟨ls,got,valid,words⟩ := compile_ok c pairs (seed xs) (seed_ok _ _) (fun e h =>
    maskEdges_valid dis good cv union.symm _ (fun v hv => by
      obtain ⟨x,hx,ex⟩ := List.mem_map.mp hv
      exact ⟨x,hx,ex.symm⟩) e h)
  have covers (v : K) (h : v∈A∪B) : v∈pool (blocks ls) := by
    apply pack_all
    rw [words]
    simpa [seed,union] using h
  have left : A⊆([]++pool (blocks ls)).toFinset := fun _ hv =>
    List.mem_toFinset.mpr (covers _ (Finset.mem_union_left _ hv))
  have right : B⊆([]++pool (blocks ls)).toFinset := fun _ hv =>
    List.mem_toFinset.mpr (covers _ (Finset.mem_union_right _ hv))
  have ok := solve_ok na dis good.1 _ [] [] (bands_painted c valid) left right
  change (compile pairs (seed xs)).any _=true
  have g := bundle_eq (blocks ls) [] []
  change ground (bundle (blocks ls)) 0 0 false=solve (blocks ls) [] [] at g
  simpa only [got,Option.any_some,g] using ok

#print axioms quick_yes
end CoNum4358.Tiny.ShareGrid.Forest

namespace CoNum4358.Tiny.ShareGrid.Forest
open CoAO3143

structure Indicator where
  wire : K
  rows : Nat
  cols : Nat

def rowSpread (u : Nat) :=
  let x := u ||| (u>>>1)
  let y := x ||| (x>>>2)
  (y ||| (y>>>3)) &&& columnMask &&& fullMask

def colSpread (u : Nat) :=
  let x := u ||| (u>>>7)
  let y := x ||| (x>>>14)
  (y ||| (y>>>28)) &&& 127

def indicator (only : Nat) (w : K) :=
  let u := cells w &&& only
  Indicator.mk w (rowSpread u) (colSpread u)

def contrary (a b : Indicator) :=
  a.wire != b.wire && (a.rows &&& b.rows) != 0 && (a.cols &&& b.cols) != 0

def simpleEdges : List Indicator → List (K×K)
  | [] => []
  | a::r => (r.filterMap (fun b => if contrary a b then some (a.wire,b.wire) else none))++simpleEdges r

def cheapPossible (xs : List K) :=
  let unique := Corners.exclusive xs
  let pairs := simpleEdges (xs.map (indicator unique))
  (compile pairs (seed xs)).any (fun ls => ground (bundle (blocks ls)) 0 0 false)


private theorem has_bit {m : Nat} (no : m≠0) : ∃i,m.testBit i=true := by
  by_contra fail
  apply no
  apply Nat.eq_of_testBit_eq
  intro i
  have zero : m.testBit i=false := Bool.eq_false_iff.mpr (fun hit => fail ⟨i,hit⟩)
  simp [zero]

private theorem grid_column : ∀i : Fin 56,columnMask.testBit i.val=true → ∃p : Fin 8,p.val*7=i.val := by
  decide +kernel

private theorem row_cell {u : Nat} {p : Fin 8} (hit : (rowSpread u).testBit (p.val*7)=true) :
    ∃n : Fin 7,u.testBit (p.val*7+n.val)=true := by
  simp only [rowSpread,Nat.testBit_and,Bool.and_eq_true] at hit
  have h := hit.1.1
  simp only [Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true] at h
  have from_bit (i) (yes : u.testBit i=true) (j : Fin 7) (eq : p.val*7+j.val=i) :
      ∃n : Fin 7,u.testBit (p.val*7+n.val)=true := ⟨j,by rwa [eq]⟩
  rcases h with ((h|h)|(h|h))|((h|h)|(h|h))
  · exact from_bit _ h ⟨0,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨1,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨2,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨3,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨3,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨4,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨5,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨6,by decide⟩ (by dsimp <;> omega)
private theorem col_cell {u : Nat} {n : Fin 7} (hit : (colSpread u).testBit n.val=true) :
    ∃p : Fin 8,u.testBit (p.val*7+n.val)=true := by
  simp only [colSpread,Nat.testBit_and,Bool.and_eq_true] at hit
  have h := hit.1
  simp only [Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true] at h
  have from_bit (i) (yes : u.testBit i=true) (j : Fin 8) (eq : j.val*7+n.val=i) :
      ∃p : Fin 8,u.testBit (p.val*7+n.val)=true := ⟨j,by rwa [eq]⟩
  rcases h with ((h|h)|(h|h))|((h|h)|(h|h))
  · exact from_bit _ h ⟨0,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨1,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨2,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨3,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨4,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨5,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨6,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨7,by decide⟩ (by dsimp <;> omega)
private theorem meet_rows {u v : Nat} (h : rowSpread u &&& rowSpread v≠0) :
    ∃p : Fin 8,∃i j : Fin 7,u.testBit (p.val*7+i.val)=true ∧ v.testBit (p.val*7+j.val)=true := by
  obtain ⟨z,hit⟩ := has_bit h
  rw [Nat.testBit_and,Bool.and_eq_true] at hit
  have data := hit.1
  simp only [rowSpread,Nat.testBit_and,Bool.and_eq_true] at data
  have m : fullMask.testBit z=decide (z<56) := Nat.testBit_two_pow_sub_one 56 z
  have small : z<56 := by simpa only [m,decide_eq_true_eq] using data.2
  obtain ⟨p,eq⟩ := grid_column ⟨z,small⟩ data.1.2
  have eq' : p.val*7=z := eq
  obtain ⟨i,hi⟩ := row_cell (p:=p) (by simpa only [eq'] using hit.1)
  obtain ⟨j,hj⟩ := row_cell (p:=p) (by simpa only [eq'] using hit.2)
  exact ⟨p,i,j,hi,hj⟩

private theorem meet_cols {u v : Nat} (h : colSpread u &&& colSpread v≠0) :
    ∃n : Fin 7,∃i j : Fin 8,u.testBit (i.val*7+n.val)=true ∧ v.testBit (j.val*7+n.val)=true := by
  obtain ⟨z,hit⟩ := has_bit h
  rw [Nat.testBit_and,Bool.and_eq_true] at hit
  have data := hit.1
  simp only [colSpread,Nat.testBit_and,Bool.and_eq_true] at data
  have m : (127 : Nat).testBit z=decide (z<7) := Nat.testBit_two_pow_sub_one 7 z
  have small : z<7 := by simpa only [m,decide_eq_true_eq] using data.2
  let n : Fin 7 := ⟨z,small⟩
  obtain ⟨i,hi⟩ := col_cell (n:=n) hit.1
  obtain ⟨j,hj⟩ := col_cell (n:=n) hit.2
  exact ⟨n,i,j,hi,hj⟩

theorem contrary_opposite {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    {a b : K} (ha : a∈xs) (hb : b∈xs)
    (ok : contrary (indicator (Corners.exclusive xs) a) (indicator (Corners.exclusive xs) b)=true) :
    decide (a∈A)≠decide (b∈A) := by
  simp only [contrary,indicator,Bool.and_eq_true,bne_iff_ne] at ok
  obtain ⟨p,i,j,pi,pj⟩ := meet_rows ok.1.2
  obtain ⟨n,s,t,ns,nt⟩ := meet_cols ok.2
  let r : Rect := ⟨a,b,p,s,t,n,i,j⟩
  apply opposite dis good union same r
  change ((a != b) && forced xs p i a && forced xs s n a && forced xs p j b && forced xs t n b)=true
  simp only [Bool.and_eq_true,bne_iff_ne]
  exact ⟨⟨⟨⟨ok.1.1,Corners.owns ha _ _ pi⟩,Corners.owns ha _ _ ns⟩,Corners.owns hb _ _ pj⟩,Corners.owns hb _ _ nt⟩
theorem simpleEdges_valid {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    (items : List Indicator) (mk : ∀v∈items,∃x∈xs,v=indicator (Corners.exclusive xs) x)
    (e : K×K) (mem : e∈simpleEdges items) : decide (e.1∈A)≠decide (e.2∈A) := by
  induction items with
  | nil => simp [simpleEdges] at mem
  | cons a r ih =>
    rcases List.mem_append.mp mem with h|h
    · obtain ⟨b,hb,yes⟩ := List.mem_filterMap.mp h
      by_cases ok : contrary a b=true
      · have eq : (a.wire,b.wire)=e := by simpa [ok] using yes
        obtain ⟨x,hx,ex⟩ := mk a List.mem_cons_self
        obtain ⟨y,hy,ey⟩ := mk b (List.mem_cons_of_mem _ hb)
        rw [←eq,ex,ey]
        change decide (x∈A)≠decide (y∈A)
        exact contrary_opposite (a:=x) (b:=y) dis good union same hx hy (by simpa only [ex,ey] using ok)
      · simp [ok] at yes
    · exact ih (fun v hv => mk v (List.mem_cons_of_mem _ hv)) h

theorem cheap_yes {k : Nat} {xs : List K} (live : Live k 0 (xs.map wide).toFinset)
    (size : xs.toFinset.card=k) : cheapPossible xs=true := by
  have eq : (xs.map wide).toFinset=up xs.toFinset := by ext w; simp [up]
  have l : Live k 0 (up xs.toFinset) := by rw [←eq]; exact live
  obtain ⟨A,sub,na,good⟩ := tight_plus_one l size
  let B := xs.toFinset\A
  have union : A∪B=xs.toFinset := by
    ext x
    change x∈A∪(xs.toFinset\A) ↔ _
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro (ha|⟨hx,_⟩)
      · exact sub ha
      · exact hx
    · intro hx
      by_cases ha : x∈A
      · exact .inl ha
      · exact .inr ⟨hx,ha⟩
  have dis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  have cv : ∀p n,∃w∈A∪B,directed w p n=true := by
    intro p n
    rw [union]
    have cov : unionSep false (xs.map wide)=top := live_cover live rfl
    have bd : p.val*7+n.val<160 := by omega
    have yes : (unionSep false (xs.map wide)).getLsbD (p.val*7+n.val)=true := by
      rw [cov]; simp only [top,BitVec.getLsbD_allOnes,bd,decide_true]
    obtain ⟨w,hw,hy⟩ := (reports_one xs p n).mp yes
    exact ⟨w,List.mem_toFinset.mpr hw,hy⟩
  let c := fun x : K => decide (x∈A)
  let pairs := simpleEdges (xs.map (indicator (Corners.exclusive xs)))
  obtain ⟨ls,got,valid,words⟩ := compile_ok c pairs (seed xs) (seed_ok _ _) (fun e h =>
    simpleEdges_valid dis good cv union.symm _ (fun v hv => by
      obtain ⟨x,hx,ex⟩ := List.mem_map.mp hv
      exact ⟨x,hx,ex.symm⟩) e h)
  have covers (v : K) (h : v∈A∪B) : v∈pool (blocks ls) := by
    apply pack_all
    rw [words]
    simpa [seed,union] using h
  have left : A⊆([]++pool (blocks ls)).toFinset := fun _ hv =>
    List.mem_toFinset.mpr (covers _ (Finset.mem_union_left _ hv))
  have right : B⊆([]++pool (blocks ls)).toFinset := fun _ hv =>
    List.mem_toFinset.mpr (covers _ (Finset.mem_union_right _ hv))
  have ok := solve_ok na dis good.1 _ [] [] (bands_painted c valid) left right
  change (compile pairs (seed xs)).any _=true
  have g := bundle_eq (blocks ls) [] []
  change ground (bundle (blocks ls)) 0 0 false=solve (blocks ls) [] [] at g
  simpa only [got,Option.any_some,g] using ok

#print axioms cheap_yes
end CoNum4358.Tiny.ShareGrid.Forest

namespace CoNum4358.Tiny.Splice
open CoAO3143
open WordRows
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def stamp (q : Nat) (ws : List W) :=
  (ws.foldl (fun s w => let x := emit w; s+(x ^^^ (x>>>7))*(x+89587)) (q*17+ws.length*467))%65536

def stored (k i : Nat) := let row := WordRows.row (BicolorBase.tier k) i; (row.1,row.2.map read)

def bank (parent i k : Nat) : Table :=
  ⟨(BicolorBase.tier k).total,stored k,fun q ws => FastJump.lookup (FastJump.tier parent) i (stamp q ws)⟩

def shadeBound (k : Nat) (cs : List K) := cs.length==k && !(ShareGrid.Forest.shadePossible cs)

theorem source_ok {k cs} (nd : cs.Nodup) (run : Live k 0 (cs.map wide).toFinset) :
    shadeBound k cs=false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [shadeBound,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at bad
  have card := List.toFinset_card_of_nodup nd
  have cap := ShareGrid.Forest.shade_yes run (card.trans bad.1)
  exact Bool.false_ne_true (bad.2.symm.trans cap)

def post (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false &&
    (if k==0 then ws.any isGoal else
      !(Corners.limit k (ws.map Prod.fst) || matched T q ws || shadeBound k (ws.map Prod.fst)))

theorem sound : MaskFast.SoundPost post := by
  intro k q T ws val nd h
  have narrow : Live k 0 ((ws.map Prod.fst).map wide).toFinset := by
    have E : ((ws.map Prod.fst).map wide).toFinset=ws.toFinset.image (fun w=>wide w.1) := by ext; simp
    rw [E]; exact (good_of h).live
  have old := Corners.sound val nd h
  have ma := matched_false val h
  have li := Corners.limit_no nd narrow
  have sh := source_ok nd narrow
  simpa only [Corners.post,post,li,ma,sh,Bool.false_or] using old

def entry (k i : Nat) :=
  let r := stored (k+1) i
  MaskFast.nodeWith post k r.1 (bank (k+1) i k) r.2

def Layer (k : Nat) := ∀i<(BicolorBase.tier k).total,¬Trace k (stored k i).1 (stored k i).2.toFinset

theorem one_layer {k : Nat} (prev : Layer k) (entries : ∀i<(BicolorBase.tier (k+1)).total,entry k i=true) :
    Layer (k+1) := by
  intro i hi
  apply MaskFast.nodeWith_ok post sound (T:=bank (k+1) i k) _ (entries _ hi)
  exact prev

def segment (k g : Nat) (b : Fin 8) :=
  let i := (g*8+b.val)*16
  CoAO3143.Memo.allAt (entry k) i (min 16 ((BicolorBase.tier (k+1)).total-i))

theorem collect {k} (prior : Layer k) (groups : Nat)
    (cover : (BicolorBase.tier (k+1)).total≤groups*8*16)
    (parts : ∀ a : Fin groups,∀ b : Fin 8,segment k a.val b=true) :
    Layer (k+1) := by
  apply one_layer prior
  intro i hi
  have row : i/16<groups*8 := by omega
  let a : Fin groups := ⟨i/16/8,by omega⟩
  let b : Fin 8 := ⟨i/16%8,Nat.mod_lt _ (by decide)⟩
  have place : a.val*8+b.val=i/16 := by dsimp [a,b]; omega
  have yes := parts a b
  unfold segment at yes
  rw [place] at yes
  apply CoAO3143.Memo.allAt_get yes i (by omega)
  omega

#print axioms one_layer
end CoNum4358.Tiny.Splice

namespace CoNum4358.Tiny.Splice
open CoAO3143
open CoNum4358.WordRows
set_option maxRecDepth 65536

def orbitItem (check : Nat → Nat → Bool) (k i : Nat) :=
  let ref := (Orbits.tier (k+1)).val i
  if ref==0 then check k i else
    let j := ref-1
    let source := stored (k+1) i
    let target := stored (k+1) j
    decide (j<i) && source.1==target.1 && (source.2.map Reflection.wire).isPerm target.2

theorem orbit_complete {k : Nat} {check : Nat → Nat → Bool}
    (actual : ∀ i,check k i=true → ¬Trace (k+1) (stored (k+1) i).1 (stored (k+1) i).2.toFinset)
    (data : ∀i<(BicolorBase.tier (k+1)).total,orbitItem check k i=true) : Layer (k+1) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have checked := data i hi
    unfold orbitItem at checked
    dsimp only at checked
    split at checked
    · exact actual i checked
    · simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.isPerm_iff] at checked
      obtain ⟨⟨before,quota⟩,per⟩ := checked
      have no := ih _ before (by omega)
      intro h
      have reflected := Reflection.trace h
      have identical : ((stored (k+1) i).2.toFinset.image Reflection.wire)=
          (stored (k+1) ((Orbits.tier (k+1)).val i-1)).2.toFinset := by
        ext x
        have p := per.mem_iff (a:=x)
        simpa only [Finset.mem_image,List.mem_toFinset,List.mem_map] using p
      exact no (by rw [←quota,←identical]; exact reflected)

theorem orbit_layer {k : Nat} (prior : Layer k)
    (data : ∀i<(BicolorBase.tier (k+1)).total,orbitItem entry k i=true) : Layer (k+1) := by
  apply orbit_complete _ data
  intro i ok
  exact MaskFast.nodeWith_ok post sound (T:=bank (k+1) i k) prior ok

def orbitSegment (k g : Nat) (b : Fin 8) :=
  let i := (g*8+b.val)*16
  CoAO3143.Memo.allAt (orbitItem entry k) i (min 16 ((BicolorBase.tier (k+1)).total-i))

theorem orbitCollect {k} (prior : Layer k) (groups : Nat)
    (cover : (BicolorBase.tier (k+1)).total≤groups*8*16)
    (parts : ∀ a : Fin groups,∀ b : Fin 8,orbitSegment k a.val b=true) :
    Layer (k+1) := by
  apply orbit_layer prior
  intro i hi
  have row : i/16<groups*8 := by omega
  let a : Fin groups := ⟨i/16/8,by omega⟩
  let b : Fin 8 := ⟨i/16%8,Nat.mod_lt _ (by decide)⟩
  have place : a.val*8+b.val=i/16 := by dsimp [a,b]; omega
  have yes := parts a b
  unfold orbitSegment at yes
  rw [place] at yes
  apply CoAO3143.Memo.allAt_get yes i (by omega)
  omega

#print axioms orbit_layer
end CoNum4358.Tiny.Splice

namespace CoNum4358.Tiny.Splice
open CoAO3143
open CoNum4358.WordRows
open ShareGrid.Forest (cheapPossible cheap_yes)

def bitPost (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false && (if k==0 then ws.any isGoal else
    !(Corners.limit k (ws.map Prod.fst) || matched T q ws ||
      (ws.length==k && !(cheapPossible (ws.map Prod.fst)))))

theorem bit_sound : MaskFast.SoundPost bitPost := by
  intro k q T ws val nd h
  have narrow : Live k 0 ((ws.map Prod.fst).map wide).toFinset := by
    have E : ((ws.map Prod.fst).map wide).toFinset=ws.toFinset.image (fun w=>wide w.1) := by ext; simp
    rw [E]; exact (good_of h).live
  have old := Corners.sound val nd h
  have ma := matched_false val h
  have li := Corners.limit_no nd narrow
  have sh : (ws.length==k && !(cheapPossible (ws.map Prod.fst)))=false := by
    apply Bool.eq_false_iff.mpr
    intro bad
    simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at bad
    have count : (ws.map Prod.fst).toFinset.card=k := by rw [List.toFinset_card_of_nodup nd,List.length_map,bad.1]
    exact Bool.false_ne_true (bad.2.symm.trans (cheap_yes narrow count))
  simpa only [Corners.post,bitPost,ma,li,sh,Bool.false_or] using old

def bitEntry (k i : Nat) :=
  let r := stored (k+1) i
  MaskFast.nodeWith bitPost k r.1 (bank (k+1) i k) r.2

theorem bit_layer {k : Nat} (prior : Layer k)
    (data : ∀i<(BicolorBase.tier (k+1)).total,orbitItem bitEntry k i=true) : Layer (k+1) := by
  apply orbit_complete _ data
  intro i ok
  exact MaskFast.nodeWith_ok bitPost bit_sound (T:=bank (k+1) i k) prior ok

def bitSegment (k g : Nat) (b : Fin 8) :=
  let i := (g*8+b.val)*16
  CoAO3143.Memo.allAt (orbitItem bitEntry k) i (min 16 ((BicolorBase.tier (k+1)).total-i))

theorem bitCollect {k} (prior : Layer k) (groups : Nat)
    (cover : (BicolorBase.tier (k+1)).total≤groups*8*16)
    (parts : ∀ a : Fin groups,∀ b : Fin 8,bitSegment k a.val b=true) :
    Layer (k+1) := by
  apply bit_layer prior
  intro i hi
  have row : i/16<groups*8 := by omega
  let a : Fin groups := ⟨i/16/8,by omega⟩
  let b : Fin 8 := ⟨i/16%8,Nat.mod_lt _ (by decide)⟩
  have place : a.val*8+b.val=i/16 := by dsimp [a,b]; omega
  have yes := parts a b
  unfold bitSegment at yes
  rw [place] at yes
  apply CoAO3143.Memo.allAt_get yes i (by omega)
  omega

#print axioms bit_layer
end CoNum4358.Tiny.Splice
