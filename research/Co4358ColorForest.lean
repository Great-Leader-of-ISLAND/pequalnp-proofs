import PEqualNP.Co4358ShareColor
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
  exact ⟨List.mem_of_find?_eq_some h,beq_iff_eq.mp (List.find?_some h)⟩

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
  · simp only [rebase,if_pos h,valid v hv,h]
    exact xor_rebase e
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
