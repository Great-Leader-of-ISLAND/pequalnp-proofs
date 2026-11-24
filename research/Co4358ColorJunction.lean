import PEqualNP.Co4358OneShareCotree

import PEqualNP.Co4358CornerPost

import PEqualNP.Co4358BicolorWords

namespace CoNum4358.Tiny.ShareGrid
open CoAO3143
open CoAO3143.ProtocolProof (Forced separates)

def up (X : Finset K) : Finset Sig := X.image wide
def FreeCell (X : Finset K) (p : Fin 8) (n : Fin 7) := ∀a∈X,directed a p n=false
def Required (X : Finset K) (p : Fin 8) (n : Fin 7) :=
  (∃m,FreeCell X p m) ∧ (∃q,FreeCell X q n)
def Owner (X : Finset K) (p : Fin 8) (n : Fin 7) (a : K) := ∀b∈X,directed b p n=true → b=a

def Arc (X : Finset K) (D : Fin 8→Fin 7→Prop) (d : Bool) (a b : K) := if d then
  ∃ (p : Fin 8) (i j : Fin 7), D p i ∧ Owner X p i a ∧ D p j ∧ Owner X p j b
  else ∃ (n : Fin 7) (i j : Fin 8), D i n ∧ Owner X i n a ∧ D j n ∧ Owner X j n b

def Linked (r : K → K → Prop) (s : Finset K) :=
  ∀ c : K→Bool, (∀x∈s,∀y∈s,r x y → c x=c y) → ∀x∈s,∀y∈s,c x=c y

def Compatible (X : Finset K) (D : Fin 8→Fin 7→Prop) :=
  ∀ s⊆X, (∀d,Linked (Arc X D d) s) → ∀a∈s,∀b∈s,a=b

def Feasible (A B : Finset K) :=
  (∀p n,Required B p n → ∃w∈A,directed w p n=true) ∧
    Compatible A (Required B) ∧ Compatible B (FreeCell A)

theorem separates_iff (a : K) (p : Fin 8) (n : Fin 7) :
    separates (pos p) (negRow n) (wide a) ↔ directed a p n=true := by
  simp only [separates,pos_bit,neg_bit,directed,Bool.and_eq_true,Bool.not_eq_true']

theorem free_cell {X : Finset K} {p n} (h : FreeCell X p n) :
    OneShare.Miss (up X) (pos p) (negRow n) := by
  intro w hw yes
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hw
  exact Bool.false_ne_true ((h a ha).symm.trans ((separates_iff a p n).mp yes))

theorem required_grid {X : Finset K} {p n} (h : Required X p n) :
    OneShare.InGrid (up X) (pos p) (negRow n) := by
  obtain ⟨⟨m,hm⟩,⟨q,hq⟩⟩ := h
  exact ⟨⟨negRow m,free_cell hm⟩,⟨pos q,free_cell hq⟩⟩

theorem owner_forced {X : Finset K} {p n a} (h : Owner X p n a) :
    Forced (up X) (pos p) (negRow n) (wide a) := by
  intro w hw yes
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hw
  exact congrArg wide (h b hb ((separates_iff _ _ _).mp yes))

theorem restrict_graph {X : Finset K} {large : Row→Row→Prop} {D : Fin 8→Fin 7→Prop}
    (old : OneShare.Compatible (up X) large) (ok : ∀p n,D p n→large (pos p) (negRow n)) :
    Compatible X D := by
  have arcs (d : Bool) {a b} (edge : Arc X D d a b) : OneShare.Edge (up X) large d (wide a) (wide b) := by
    cases d
    · obtain ⟨n,i,j,hi,oi,hj,oj⟩ := edge
      exact ⟨negRow n,pos i,pos j,ok _ _ hi,owner_forced oi,ok _ _ hj,owner_forced oj⟩
    · obtain ⟨p,i,j,hi,oi,hj,oj⟩ := edge
      exact ⟨pos p,negRow i,negRow j,ok _ _ hi,owner_forced oi,ok _ _ hj,owner_forced oj⟩
  intro s sub all a ha b hb
  apply wide_inj
  apply old (up s) (Finset.image_mono wide sub) _ (wide a) (Finset.mem_image_of_mem _ ha)
    (wide b) (Finset.mem_image_of_mem _ hb)
  intro d color mono x hx y hy
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
  apply all d (fun a => color (wide a)) _ v hv w hw
  intro r hr t ht arc
  exact mono _ (Finset.mem_image_of_mem _ hr) _ (Finset.mem_image_of_mem _ ht) (arcs d arc)

theorem tight_plus_one {k : Nat} {X : Finset K} (run : Live k 0 (up X)) (size : X.card=k) :
    ∃ A⊆X, A.Nonempty ∧ Feasible A (X\A) := by
  classical
  have count : (up X).card=k := (Finset.card_image_of_injective _ wide_inj).trans size
  obtain ⟨T,U,tn,both,dis,cover,inner,outer⟩ := OneShare.single_share_necessary run count
  let A := X.filter fun a => wide a∈T
  have sub : A⊆X := Finset.filter_subset _ _
  have tt : up A=T := by
    ext w
    constructor
    · intro hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hv).2
    · intro hw
      have all : w∈up X := both ▸ Finset.mem_union_left U hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp all
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hv,hw⟩)
  have uu : up (X\A)=U := by
    ext w
    constructor
    · intro hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨vx,va⟩ := Finset.mem_sdiff.mp hv
      have all : wide v∈T∪U := by rw [both]; exact Finset.mem_image_of_mem _ vx
      exact (Finset.mem_union.mp all).resolve_left (fun vt => va (Finset.mem_filter.mpr ⟨vx,vt⟩))
    · intro hw
      have all : w∈up X := both ▸ Finset.mem_union_right T hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp all
      apply Finset.mem_image_of_mem
      apply Finset.mem_sdiff.mpr
      exact ⟨hv,fun va => Finset.disjoint_left.mp dis (Finset.mem_filter.mp va).2 hw⟩
  rw [←tt,←uu] at cover inner outer
  have na : A.Nonempty := by
    obtain ⟨v,hv⟩ := tn
    rw [←tt] at hv
    obtain ⟨x,hx,_⟩ := Finset.mem_image.mp hv
    exact ⟨x,hx⟩
  refine ⟨A,sub,na,?_,restrict_graph inner (fun _ _ h => required_grid h),
    restrict_graph outer (fun _ _ h => free_cell h)⟩
  intro p n need
  obtain ⟨v,hv,yes⟩ := cover (pos p) (negRow n) (required_grid need)
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
  exact ⟨a,ha,(separates_iff _ _ _).mp yes⟩

#print axioms tight_plus_one
end CoNum4358.Tiny.ShareGrid


namespace CoNum4358.Tiny.ShareGrid
open CoAO3143
set_option maxRecDepth 65536

def Covered (X : Finset K) (D : Fin 8 → Fin 7 → Prop) :=
  ∀p n,D p n → ∃w∈X,directed w p n=true

theorem outer_covered {A B : Finset K} (all : ∀p n,∃w∈A∪B,directed w p n=true) :
    Covered B (FreeCell A) := by
  intro p n miss
  obtain ⟨a,am,hit⟩ := all p n
  refine ⟨a,(Finset.mem_union.mp am).resolve_left ?_,hit⟩
  intro ha
  exact Bool.false_ne_true ((miss a ha).symm.trans hit)

private theorem two_linked {R : K→K→Prop} {a b : K} (edge : R a b) :
    Linked R ({a,b} : Finset K) := by
  intro c mono x hx y hy
  have eq := mono a (by simp) b (by simp) edge
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with xa|xb <;> rcases hy with ya|yb <;> simp_all only

/-- On a viable local domain, two distinct locally forced leaves cannot
share both a positive input row and a negative input column. -/
theorem no_rectangle {X : Finset K} {D : Fin 8→Fin 7→Prop}
    (apart : Compatible X D) (cover : Covered X D) (r : Rect)
    (pA : D r.p r.m₁) (aP : Owner X r.p r.m₁ r.a)
    (nA : D r.q₁ r.n) (aN : Owner X r.q₁ r.n r.a)
    (pB : D r.p r.m₂) (bP : Owner X r.p r.m₂ r.b)
    (nB : D r.q₂ r.n) (bN : Owner X r.q₂ r.n r.b) : r.a=r.b := by
  have exists_owner (p n a) (h : D p n) (o : Owner X p n a) : a∈X := by
    obtain ⟨w,hw,yes⟩ := cover _ _ h
    simpa only [o w hw yes] using hw
  have ma := exists_owner _ _ _ pA aP
  have mb := exists_owner _ _ _ pB bP
  have sub : ({r.a,r.b} : Finset K)⊆X := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    obtain hv|hv := hv
    · simpa only [hv] using ma
    · simpa only [hv] using mb
  apply apart _ sub _ _ (by simp) _ (by simp)
  intro d
  apply two_linked
  cases d
  · exact ⟨r.n,r.q₁,r.q₂,nA,aN,nB,bN⟩
  · exact ⟨r.p,r.m₁,r.m₂,pA,aP,pB,bP⟩

theorem free_shrink {X Y : Finset K} (sub : X⊆Y) {p n} (h : FreeCell Y p n) :
    FreeCell X p n := fun a ha => h a (sub ha)

theorem required_shrink {X Y : Finset K} (sub : X⊆Y) {p n} (h : Required Y p n) :
    Required X p n := by
  obtain ⟨⟨m,hm⟩,⟨q,hq⟩⟩ := h
  exact ⟨⟨m,free_shrink sub hm⟩,⟨q,free_shrink sub hq⟩⟩

theorem owner_shrink {X Y : Finset K} (sub : X⊆Y) {p n a} (h : Owner Y p n a) :
    Owner X p n a := fun b hb => h b (sub hb)

def cov (xs : List K) := (Corners.counts xs).1
def noBit (s : Nat) (p : Fin 8) (n : Fin 7) := !s.testBit (p.val*7+n.val)

theorem noBit_free {xs : List K} {p n} (h : noBit (cov xs) p n=true) : FreeCell xs.toFinset p n := by
  intro a ha
  apply Bool.eq_false_iff.mpr
  intro yes
  have sep := Corners.seen (List.mem_toFinset.mp ha) (p.val*7+n.val) (by rwa [Masks.cells_bit])
  have no : (cov xs).testBit (p.val*7+n.val)=false := by simpa only [noBit,Bool.not_eq_true'] using h
  exact Bool.false_ne_true (no.symm.trans sep)

/-- The bit arithmetic proposes two witnesses. Their membership in the true
pair domain is checked using the actual row/column coordinates. -/
def productBit (s : Nat) (p : Fin 8) (n : Fin 7) : Bool :=
  let uncovered := fullMask ^^^ s
  let m := Fin.ofNat 7 (((uncovered >>> (p.val*7)) &&& 127).log2)
  let q := Fin.ofNat 8 (((uncovered &&& (columnMask <<< n.val)).log2)/7)
  noBit s p m && noBit s q n

theorem productBit_required {xs : List K} {p n} (h : productBit (cov xs) p n=true) :
    Required xs.toFinset p n := by
  let mask := fullMask ^^^ cov xs
  let m := Fin.ofNat 7 (((mask >>> (p.val*7)) &&& 127).log2)
  let q := Fin.ofNat 8 (((mask &&& (columnMask <<< n.val)).log2)/7)
  change (noBit (cov xs) p m && noBit (cov xs) q n)=true at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hp,hn⟩ := h
  exact ⟨⟨m,noBit_free hp⟩,⟨q,noBit_free hn⟩⟩

theorem forced_owner {xs : List K} {p n a} (h : forced xs p n a=true) :
    Owner xs.toFinset p n a := by
  intro b hb yes
  have eq := List.all_eq_true.mp h b (List.mem_toFinset.mp hb)
  obtain ⟨hp,hn⟩ := Bool.and_eq_true.mp yes
  have no := by simpa only [noBit,Bool.not_eq_true'] using hn
  simpa [hp,no] using eq

def rectBit (xs : List K) (dom : Fin 8→Fin 7→Bool) (r : Rect) :=
  validRect xs r && dom r.p r.m₁ && dom r.q₁ r.n && dom r.p r.m₂ && dom r.q₂ r.n

theorem rectBit_false {X : Finset K} {xs : List K} (sub : X⊆xs.toFinset)
    {D : Fin 8→Fin 7→Prop} (apart : Compatible X D) (cover : Covered X D)
    {dom : Fin 8→Fin 7→Bool} (valid : ∀p n, dom p n=true → D p n) (r : Rect) :
    rectBit xs dom r=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [rectBit,validRect,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ne,ap⟩,an⟩,bp⟩,bn⟩,pa⟩,na⟩,pb⟩,nb⟩ := h
  exact ne (no_rectangle apart cover r (valid _ _ pa) (owner_shrink sub (forced_owner ap))
    (valid _ _ na) (owner_shrink sub (forced_owner an))
    (valid _ _ pb) (owner_shrink sub (forced_owner bp))
    (valid _ _ nb) (owner_shrink sub (forced_owner bn)))

#print axioms rectBit_false
end CoNum4358.Tiny.ShareGrid


namespace CoNum4358.Tiny.ShareGrid
open CoAO3143
set_option maxRecDepth 65536

def estimateProduct (used : Nat) :=
  let u := fullMask ^^^ used
  let high := columnMask<<<6
  let low := fullMask ^^^ high
  let p := ((u ||| ((u&&&low)+low)) &&& high)>>>6
  let z := u ||| (u>>>7)
  let z := z ||| (z>>>14)
  let z := z ||| (z>>>28)
  p*(z%128)

def uncoveredProduct (left right prod : Nat) :=
  let missing := prod &&& (fullMask ^^^ left)
  if missing==0 then false else
    let i := missing.log2
    let p := Fin.ofNat 8 (i/7)
    let n := Fin.ofNat 7 i
    productBit right p n && noBit left p n

theorem product_no {A B : Finset K} {xs ys : List K} (left : A⊆xs.toFinset) (right : B⊆ys.toFinset)
    (guarantee : Covered A (Required B)) (mask : Nat) : uncoveredProduct (cov xs) (cov ys) mask=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  unfold uncoveredProduct at h
  dsimp only at h
  split at h
  · contradiction
  · rw [Bool.and_eq_true] at h
    obtain ⟨hp,hn⟩ := h
    obtain ⟨w,hw,yes⟩ := guarantee _ _ (required_shrink right (productBit_required hp))
    exact Bool.false_ne_true ((noBit_free hn w (left hw)).symm.trans yes)

/-- Projection and firstHit propose a contradiction. rectBit rechecks the
four exact cells and the owner's identity in the larger candidate side. -/
def localRect (xs : List K) (mask : Nat) (dom : Fin 8→Fin 7→Bool) :=
  let only := Corners.exclusive xs &&& mask
  (firstHit (xs.map fun a => prof a only)).any (rectBit xs dom)

theorem local_no {X : Finset K} {xs : List K} (sub : X⊆xs.toFinset)
    {D : Fin 8→Fin 7→Prop} (apart : Compatible X D) (cover : Covered X D)
    {dom : Fin 8→Fin 7→Bool} (valid : ∀p n,dom p n=true → D p n) (mask : Nat) :
    localRect xs mask dom=false := by
  unfold localRect
  dsimp only
  generalize firstHit _ = hint
  cases hint with
  | none => rfl
  | some r => exact rectBit_false sub apart cover valid r

def partialBlock (left right : List K) :=
  let ca := cov left
  let cb := cov right
  let p := estimateProduct cb
  uncoveredProduct ca cb p || localRect left p (productBit cb) ||
    localRect right (fullMask ^^^ ca) (noBit ca)

theorem partial_no {A B : Finset K} {xs ys : List K} (left : A⊆xs.toFinset) (right : B⊆ys.toFinset)
    (good : Feasible A B) (union : ∀p n,∃w∈A∪B,directed w p n=true) :
    partialBlock xs ys=false := by
  have pa := product_no left right good.1 (estimateProduct (cov ys))
  have pb := local_no left good.2.1 good.1 (fun _ _ h => required_shrink right (productBit_required h))
    (estimateProduct (cov ys))
  have pc := local_no right good.2.2 (outer_covered union) (fun _ _ h => free_shrink left (noBit_free h))
    (fullMask ^^^ cov xs)
  simp only [partialBlock,pa,pb,pc,Bool.false_or]

def possible : List K → List K → List K → Bool
  | a,b,[] => !a.isEmpty && !(partialBlock a b)
  | a,b,h::rs =>
    !(partialBlock (a++h::rs) (b++h::rs)) &&
      (possible (h::a) b rs || possible a (h::b) rs)

theorem possible_yes {A B : Finset K} (na : A.Nonempty) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true)
    (left right rest : List K) (al : A⊆(left++rest).toFinset) (br : B⊆(right++rest).toFinset)
    (dis : Disjoint A B) : possible left right rest=true := by
  induction rest generalizing left right with
  | nil =>
    simp only [List.append_nil] at al br
    have lne : left≠[] := by
      obtain ⟨a,ha⟩ := na
      intro e
      have bad := al ha
      simp [e] at bad
    simp [possible,lne,partial_no al br good union]
  | cons h rs ih =>
    have ok := partial_no al br good union
    simp only [possible,ok,Bool.not_false,Bool.true_and,Bool.or_eq_true]
    by_cases ha : h∈A
    · left
      apply ih (h::left) right
      · intro x hx
        have old := al hx
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at old ⊢
        tauto
      · intro x hx
        have old := br hx
        have ne : x≠h := by
          intro eq
          exact Finset.disjoint_left.mp dis ha (by simpa only [eq] using hx)
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at old ⊢
        tauto
    · right
      apply ih left (h::right)
      · intro x hx
        have old := al hx
        have ne : x≠h := fun eq => ha (by simpa only [eq] using hx)
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at old ⊢
        tauto
      · intro x hx
        have old := br hx
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at old ⊢
        tauto

theorem reports_one (xs : List K) (p : Fin 8) (n : Fin 7) :
    (unionSep false (xs.map wide)).getLsbD (p.val*7+n.val)=true ↔
      ∃a∈xs,directed a p n=true := by
  induction xs with
  | nil => simp [unionSep]
  | cons a xs ih =>
    simp only [List.map_cons,unionSep,BitVec.getLsbD_or,joint_bit,Bool.or_eq_true,ih,List.mem_cons]
    constructor
    · rintro (h|⟨b,hb,byes⟩)
      · exact ⟨a,.inl rfl,h⟩
      · exact ⟨b,.inr hb,byes⟩
    · rintro ⟨b,(ba|bs),yes⟩
      · subst b; exact .inl yes
      · exact .inr ⟨b,bs,yes⟩

theorem single_possible {k : Nat} {xs : List K} (live : Live k 0 (xs.map wide).toFinset)
    (size : xs.toFinset.card=k) : possible [] [] xs=true := by
  have eq : (xs.map wide).toFinset=up xs.toFinset := by ext w; simp [up]
  have l : Live k 0 (up xs.toFinset) := by rw [←eq]; exact live
  obtain ⟨a,sub,ne,feasible⟩ := tight_plus_one l size
  have full : a∪(xs.toFinset\a)=xs.toFinset := by
    ext x
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro (ha|⟨hx,_⟩)
      · exact sub ha
      · exact hx
    · intro hx
      by_cases ha : x∈a
      · exact .inl ha
      · exact .inr ⟨hx,ha⟩
  have cov : unionSep false (xs.map wide)=top := live_cover live rfl
  have dis : Disjoint a (xs.toFinset\a) := by
    rw [Finset.disjoint_left]
    intro x ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  apply possible_yes ne feasible _ [] [] xs (by simpa using sub) (by simpa using (Finset.sdiff_subset : xs.toFinset\a⊆xs.toFinset)) dis
  intro p n
  rw [full]
  have bd : p.val*7+n.val<160 := by omega
  have bit : (unionSep false (xs.map wide)).getLsbD (p.val*7+n.val)=true := by
    rw [cov]; simp only [top,BitVec.getLsbD_allOnes,bd,decide_true]
  obtain ⟨w,hw,yes⟩ := (reports_one xs p n).mp bit
  exact ⟨w,List.mem_toFinset.mpr hw,yes⟩

#print axioms possible_yes
#print axioms single_possible
end CoNum4358.Tiny.ShareGrid


namespace CoNum4358.Tiny.ShareGrid
open CoAO3143
set_option maxRecDepth 65536

theorem owned_miss {A B : Finset K} {a p n} (own : Owner (A∪B) p n a) (na : a∉B) :
    FreeCell B p n := by
  intro b mb
  apply Bool.eq_false_iff.mpr
  intro hit
  have eq := own b (Finset.mem_union_right _ mb) hit
  exact na (by simpa only [eq] using mb)

private theorem own_miss_left {A B : Finset K} {a p n} (own : Owner (A∪B) p n a) (na : a∉A) :
    FreeCell A p n := by
  intro b mb
  apply Bool.eq_false_iff.mpr
  intro hit
  have eq := own b (Finset.mem_union_left _ mb) hit
  exact na (by simpa only [eq] using mb)

private theorem free_req {A : Finset K} {p n} (no : FreeCell A p n) : Required A p n :=
  ⟨⟨n,no⟩,⟨p,no⟩⟩

theorem opposite {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    (r : Rect) (h : validRect xs r=true) : decide (r.a∈A)≠decide (r.b∈A) := by
  simp only [validRect,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨⟨⟨⟨ne,ap⟩,an⟩,bp⟩,bn⟩ := h
  have lift {p n v} (h : forced xs p n v=true) : Owner (A∪B) p n v := by rw [←same]; exact forced_owner h
  have aP := lift ap
  have aN := lift an
  have bP := lift bp
  have bN := lift bn
  intro eq
  by_cases ma : r.a∈A
  · have mb : r.b∈A := by simpa [ma] using eq.symm
    have high : A⊆A∪B := Finset.subset_union_left
    have noA : r.a∉B := fun h => Finset.disjoint_left.mp dis ma h
    have noB : r.b∉B := fun h => Finset.disjoint_left.mp dis mb h
    exact ne (no_rectangle good.2.1 good.1 r
      (free_req (owned_miss aP noA)) (owner_shrink high aP)
      (free_req (owned_miss aN noA)) (owner_shrink high aN)
      (free_req (owned_miss bP noB)) (owner_shrink high bP)
      (free_req (owned_miss bN noB)) (owner_shrink high bN))
  · have mb : r.b∉A := by simpa [ma] using eq.symm
    have high : B⊆A∪B := Finset.subset_union_right
    exact ne (no_rectangle good.2.2 (outer_covered union) r
      (own_miss_left aP ma) (owner_shrink high aP)
      (own_miss_left aN ma) (owner_shrink high aN)
      (own_miss_left bP mb) (owner_shrink high bP)
      (own_miss_left bN mb) (owner_shrink high bN))

/-- Compile a certified pair of contrary input colors, using the global rather
than local unique-cell masks. The synthetic coordinates are always rechecked. -/
def shade (xs : List K) (a b : Prof) :=
  match propose a b with
  | none => false
  | some r => r.a==a.wire && r.b==b.wire && validRect xs r

theorem shade_opposite {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    {a b : Prof} (ok : shade xs a b=true) : decide (a.wire∈A)≠decide (b.wire∈A) := by
  unfold shade at ok
  split at ok
  · contradiction
  · rename_i r hr
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    have neq := opposite dis good union same r ok.2
    simpa only [ok.1.1,ok.1.2] using neq

end CoNum4358.Tiny.ShareGrid

namespace CoNum4358.Tiny.ShareGrid.Forest
open CoAO3143

structure Label where
  wire : K
  root : K
  flip : Bool
deriving DecidableEq, Repr

def Correct (color : K→Bool) (ls : List Label) := ∀v∈ls,color v.wire=xor (color v.root) v.flip

def seed (xs : List K) := xs.map fun w => Label.mk w w false
theorem seed_ok (c : K→Bool) (xs : List K) : Correct c (seed xs) := by
  intro l hl
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp hl
  simp

def locate (ls : List Label) (x : K) := ls.find? fun v => v.wire==x

private theorem located {ls : List Label} {x l} (h : locate ls x=some l) : l∈ls ∧ l.wire=x := by
  have hit : (fun v : Label => v.wire==x) l=true := List.find?_some (p:=fun v : Label => v.wire==x) (a:=l) h
  exact ⟨List.mem_of_find?_eq_some h,beq_iff_eq.mp hit⟩

def rebase (a b : Label) (v : Label) :=
  if v.root=b.root then ⟨v.wire,a.root,xor v.flip (!(xor a.flip b.flip))⟩ else v

private theorem xor_rebase {a b x y z : Bool} (different : xor a x≠xor b y) :
    xor b z=xor a (xor z (!(xor x y))) := by
  cases a <;> cases b <;> cases x <;> cases y <;> cases z <;> simp_all

private theorem rebase_ok (c : K→Bool) {ls} (valid : Correct c ls) {a b : Label}
    (ma : a∈ls) (mb : b∈ls) (ne : c a.wire≠c b.wire) : Correct c (ls.map (rebase a b)) := by
  intro l hl
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hl
  have e : xor (c a.root) a.flip≠xor (c b.root) b.flip := by rwa [←valid a ma,←valid b mb]
  by_cases h : v.root=b.root
  · rw [show rebase a b v=⟨v.wire,a.root,xor v.flip (!(xor a.flip b.flip))⟩ from if_pos h]
    change c v.wire=xor (c a.root) (xor v.flip (!(xor a.flip b.flip)))
    rw [valid v hv,h]
    exact xor_rebase (z:=v.flip) e
  · simpa only [rebase,if_neg h] using valid v hv

def link (x y : K) (ls : List Label) : Option (List Label) := do
  let some a := locate ls x | return ls
  let some b := locate ls y | return ls
  if a.root=b.root then
    if a.flip=b.flip then none else return ls
  else return ls.map (rebase a b)

theorem link_ok (c : K→Bool) {ls} (valid : Correct c ls) {x y} (ne : c x≠c y) :
    ∃ rs,link x y ls=some rs ∧ Correct c rs ∧ rs.map Label.wire=ls.map Label.wire := by
  cases ha : locate ls x with
  | none => exact ⟨ls,by simp [link,ha],valid,rfl⟩
  | some a =>
    cases hb : locate ls y with
    | none => exact ⟨ls,by simp [link,ha,hb],valid,rfl⟩
    | some b =>
      obtain ⟨am,ax⟩ := located ha
      obtain ⟨bm,byy⟩ := located hb
      have diff : c a.wire≠c b.wire := by simpa only [ax,byy] using ne
      by_cases same : a.root=b.root
      · have flip : a.flip≠b.flip := by
          intro h
          apply diff
          rw [valid a am,valid b bm,same,h]
        exact ⟨ls,by simp [link,ha,hb,same,flip],valid,rfl⟩
      · refine ⟨_,by simp [link,ha,hb,same],rebase_ok c valid am bm diff,?_⟩
        rw [List.map_map]
        apply List.map_congr_left
        intro v hv
        by_cases e : v.root=b.root <;> simp [Function.comp_def,rebase,e]

def edges (xs : List K) : List Prof → List (K×K)
  | [] => []
  | a::r => (r.filterMap (fun b => if shade xs a b then some (a.wire,b.wire) else none))++edges xs r

theorem edges_valid {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    (items : List Prof) (e : K×K) (mem : e∈edges xs items) :
    decide (e.1∈A)≠decide (e.2∈A) := by
  induction items with
  | nil => simp [edges] at mem
  | cons a r ih =>
    rcases List.mem_append.mp mem with h|h
    · obtain ⟨b,_,yes⟩ := List.mem_filterMap.mp h
      by_cases ok : shade xs a b=true
      · have heq : (a.wire,b.wire)=e := by simpa [ok] using yes
        rw [←heq]
        exact shade_opposite dis good union same ok
      · simp [ok] at yes
    · exact ih h

def compile : List (K×K) → List Label → Option (List Label)
  | [],ls => some ls
  | e::es,ls => (link e.1 e.2 ls).bind (compile es)

theorem compile_ok (c : K→Bool) (es : List (K×K)) (ls : List Label) (valid : Correct c ls)
    (ne : ∀e∈es,c e.1≠c e.2) : ∃rs,compile es ls=some rs ∧ Correct c rs ∧ rs.map Label.wire=ls.map Label.wire := by
  induction es generalizing ls with
  | nil => exact ⟨ls,rfl,valid,rfl⟩
  | cons e es ih =>
    obtain ⟨mid,eq,gm,wm⟩ := link_ok c valid (ne e List.mem_cons_self)
    obtain ⟨rs,out,gr,wr⟩ := ih mid gm (fun v hv => ne v (List.mem_cons_of_mem _ hv))
    exact ⟨rs,by simp [compile,eq,out],gr,wr.trans wm⟩

end CoNum4358.Tiny.ShareGrid.Forest


namespace CoNum4358.Tiny.ShareGrid.Forest
open CoAO3143
set_option maxRecDepth 65536

structure Block where
  key : K
  lhs : List K
  rhs : List K
deriving Repr

def band (ls : List Label) (r : K) (b : Bool) :=
  (ls.filter (fun l => l.root==r && l.flip==b)).map Label.wire

def blocks (ls : List Label) := (ls.map Label.root).eraseDups.map fun r => Block.mk r (band ls r false) (band ls r true)

def pool : List Block → List K
  | [] => []
  | g::gs => g.lhs ++ (g.rhs ++ pool gs)

theorem in_pool {gs : List Block} {g x} (mem : g∈gs) (h : x∈g.lhs ∨ x∈g.rhs) : x∈pool gs := by
  induction gs with
  | nil => simp at mem
  | cons v vs ih =>
    rcases List.mem_cons.mp mem with e|m
    · rw [e] at h
      simp only [pool,List.mem_append]
      tauto
    · exact List.mem_append_right _ (List.mem_append_right _ (ih m))

theorem pack_all {ls : List Label} {x} (h : x∈ls.map Label.wire) : x∈pool (blocks ls) := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
  let g := Block.mk v.root (band ls v.root false) (band ls v.root true)
  apply in_pool (g:=g)
  · apply List.mem_map.mpr
    have m : v.root∈ls.map Label.root := List.mem_map.mpr ⟨v,hv,rfl⟩
    exact ⟨v.root,by simpa using m,rfl⟩
  · have hm : v.wire∈band ls v.root v.flip := by
      apply List.mem_map.mpr
      exact ⟨v,List.mem_filter.mpr ⟨hv,by simp⟩,rfl⟩
    cases e : v.flip
    · left; simpa only [g,e] using hm
    · right; simpa only [g,e] using hm

def Painted (c : K→Bool) (gs : List Block) := ∀g∈gs,
  (∀x∈g.lhs,c x=c g.key) ∧ (∀x∈g.rhs,c x= !(c g.key))

theorem bands_painted (c : K→Bool) {ls} (ok : Correct c ls) : Painted c (blocks ls) := by
  intro g hg
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hg
  have part (b : Bool) (x : K) (hx : x∈band ls r b) : c x=xor (c r) b := by
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hx
    obtain ⟨m,test⟩ := List.mem_filter.mp hl
    simp only [Bool.and_eq_true,beq_iff_eq] at test
    simpa only [test.1,test.2] using ok l m
  constructor
  · intro x hx; simpa using part false x hx
  · intro x hx; simpa using part true x hx

def solve : List Block → List K → List K → Bool
  | [],a,b => !a.isEmpty && !(uncoveredProduct (cov a) (cov b) (estimateProduct (cov b)))
  | g::gs,a,b =>
    let anySide := pool (g::gs)
    let cA := cov (a++anySide)
    let cB := cov (b++anySide)
    !(uncoveredProduct cA cB (estimateProduct cB)) &&
      (solve gs (g.lhs++a) (g.rhs++b) || solve gs (g.rhs++a) (g.lhs++b))

private theorem advance {T : Finset K} {used yes no rest : List K}
    (old : T⊆(used++(yes++(no++rest))).toFinset) (exclude : ∀v∈no,v∉T) :
    T⊆((yes++used)++rest).toFinset := by
  intro v hv
  have m := old hv
  simp only [List.mem_toFinset,List.mem_append] at m ⊢
  have out : v∉no := fun h => exclude v h hv
  tauto

private theorem swap_lists {T : Finset K} {used xs ys zs : List K}
    (old : T⊆(used++(xs++(ys++zs))).toFinset) :
    T⊆(used++(ys++(xs++zs))).toFinset := by
  intro v h
  have m := old h
  simp only [List.mem_toFinset,List.mem_append] at m ⊢
  tauto

theorem solve_ok {A B : Finset K} (na : A.Nonempty) (dis : Disjoint A B)
    (guarantee : Covered A (Required B)) (gs : List Block) (a b : List K)
    (good : Painted (fun x => decide (x∈A)) gs)
    (left : A⊆(a++pool gs).toFinset) (right : B⊆(b++pool gs).toFinset) :
    solve gs a b=true := by
  induction gs generalizing a b with
  | nil =>
    simp only [pool,List.append_nil] at left right
    have lne : a≠[] := by
      intro e
      obtain ⟨v,hv⟩ := na
      have bad := left hv
      simp [e] at bad
    simp [solve,lne,product_no left right guarantee]
  | cons g gs ih =>
    have prod := product_no left right guarantee (estimateProduct (cov (b++pool (g::gs))))
    have parts := good g List.mem_cons_self
    have gr : Painted (fun x => decide (x∈A)) gs := fun v hv => good v (List.mem_cons_of_mem _ hv)
    simp only [solve,prod,Bool.not_false,Bool.true_and,Bool.or_eq_true]
    by_cases key : g.key∈A
    · left
      have noR (x) (h : x∈g.rhs) : x∉A := by simpa [key] using parts.2 x h
      have noL (x) (h : x∈g.lhs) : x∉B := by
        have xa : x∈A := by simpa [key] using parts.1 x h
        exact fun xb => Finset.disjoint_left.mp dis xa xb
      exact ih _ _ gr (advance left noR) (advance (swap_lists right) noL)
    · right
      have noL (x) (h : x∈g.lhs) : x∉A := by simpa [key] using parts.1 x h
      have noR (x) (h : x∈g.rhs) : x∉B := by
        have xa : x∈A := by simpa [key] using parts.2 x h
        exact fun xb => Finset.disjoint_left.mp dis xa xb
      exact ih _ _ gr (advance (swap_lists left) noL) (advance right noR)

def shadePossible (xs : List K) :=
  let unique := Corners.exclusive xs
  let pairs := edges xs (xs.map fun x => prof x unique)
  (compile pairs (seed xs)).any (fun ls => solve (blocks ls) [] [])

theorem shade_yes {k : Nat} {xs : List K} (live : Live k 0 (xs.map wide).toFinset)
    (size : xs.toFinset.card=k) : shadePossible xs=true := by
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
  let pairs := edges xs (xs.map fun x => prof x (Corners.exclusive xs))
  obtain ⟨ls,got,valid,words⟩ := compile_ok c pairs (seed xs) (seed_ok _ _) (fun e h =>
    edges_valid dis good cv union.symm _ e h)
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
  simp only [got,Option.any_some,ok]

#print axioms shade_yes
end CoNum4358.Tiny.ShareGrid.Forest

namespace CoNum4358.Tiny.Splice
open CoAO3143
open WordRows
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def stamp (q : Nat) (ws : List W) :=
  (ws.foldl (fun s w => let x := emit w; s+(x ^^^ (x>>>7))*(x+89587)) (q*17+ws.length*467))%65536

def stored (k i : Nat) := let row := WordRows.row (Bicolor.tier k) i; (row.1,row.2.map read)

def bank (parent i k : Nat) : Table :=
  ⟨(Bicolor.tier k).total,stored k,fun q ws => WordRows.findHash (Bicolor.tier parent) i (stamp q ws)⟩

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

def Layer (k : Nat) := ∀i<(Bicolor.tier k).total,¬Trace k (stored k i).1 (stored k i).2.toFinset

theorem one_layer {k : Nat} (prev : Layer k) (entries : ∀i<(Bicolor.tier (k+1)).total,entry k i=true) :
    Layer (k+1) := by
  intro i hi
  apply MaskFast.nodeWith_ok post sound (T:=bank (k+1) i k) _ (entries _ hi)
  exact prev

def segment (k g : Nat) (b : Fin 8) :=
  let i := (g*8+b.val)*16
  CoAO3143.Memo.allAt (entry k) i (min 16 ((Bicolor.tier (k+1)).total-i))

theorem collect {k} (prior : Layer k) (groups : Nat)
    (cover : (Bicolor.tier (k+1)).total≤groups*8*16)
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
