import PEqualNP.Co4358ColorForest
import PEqualNP.Co4358ShareSearch

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
    exact ⟨v.root,by simpa using List.mem_map_of_mem Label.root hv,rfl⟩
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
  have dis : Disjoint A B := by simp [B]
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
