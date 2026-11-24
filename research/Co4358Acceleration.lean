import PEqualNP.Co4358ColorJunction

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
        exact mask_opposite dis good union same hx hy (by simpa only [ex,ey] using ok)
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
  | cons g gs ih => simp only [bundle,Bundle.total,pool,cov_append,ih]

theorem used_append (a b : List K) : !(a++b).isEmpty=(!a.isEmpty || !b.isEmpty) := by
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
  rcases h with ((h|h)|(h|h))|((h|h)|(h|h)) <;> first
    | exact from_bit _ h 0 (by norm_num <;> omega)
    | exact from_bit _ h 1 (by norm_num <;> omega)
    | exact from_bit _ h 2 (by norm_num <;> omega)
    | exact from_bit _ h 3 (by norm_num <;> omega)
    | exact from_bit _ h 4 (by norm_num <;> omega)
    | exact from_bit _ h 5 (by norm_num <;> omega)
    | exact from_bit _ h 6 (by norm_num <;> omega)
private theorem col_cell {u : Nat} {n : Fin 7} (hit : (colSpread u).testBit n.val=true) :
    ∃p : Fin 8,u.testBit (p.val*7+n.val)=true := by
  simp only [colSpread,Nat.testBit_and,Bool.and_eq_true] at hit
  have h := hit.1
  simp only [Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true] at h
  have from_bit (i) (yes : u.testBit i=true) (j : Fin 8) (eq : j.val*7+n.val=i) :
      ∃p : Fin 8,u.testBit (p.val*7+n.val)=true := ⟨j,by rwa [eq]⟩
  rcases h with ((h|h)|(h|h))|((h|h)|(h|h)) <;> first
    | exact from_bit _ h 0 (by norm_num <;> omega)
    | exact from_bit _ h 1 (by norm_num <;> omega)
    | exact from_bit _ h 2 (by norm_num <;> omega)
    | exact from_bit _ h 3 (by norm_num <;> omega)
    | exact from_bit _ h 4 (by norm_num <;> omega)
    | exact from_bit _ h 5 (by norm_num <;> omega)
    | exact from_bit _ h 6 (by norm_num <;> omega)
    | exact from_bit _ h 7 (by norm_num <;> omega)
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
        exact contrary_opposite dis good union same hx hy (by simpa only [ex,ey] using ok)
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
