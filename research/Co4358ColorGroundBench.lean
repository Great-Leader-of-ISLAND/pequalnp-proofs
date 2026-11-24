import PEqualNP.Co4358ColorGround
namespace CoNum4358.Tiny.ShareGrid.Forest
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 30
theorem sample1 : shadePossible [1956,5700,7442,8715,22568,22829,24784]=false := by decide +kernel
theorem sample2 : shadePossible [6116,7442,8715,13903,18725,22568,24784]=false := by decide +kernel
theorem sample3 : shadePossible [208,1952,5700,7442,8715,18693,22568]=true := by decide +kernel
theorem sample4 : shadePossible [6116,7442,8715,13903,18693,22568,24816]=true := by decide +kernel
theorem sample5 : shadePossible [1952,5700,7442,8715,9739,18693,22568,24784]=false := by decide +kernel
theorem sample6 : shadePossible [1952,5700,7442,8715,18693,19717,22568,24784]=false := by decide +kernel
theorem sample7 : shadePossible [1952,5700,7442,8182,8715,18693,22568,24784]=true := by decide +kernel
theorem sample8 : shadePossible [5700,6116,7442,8715,18693,22568,24784,24816]=true := by decide +kernel
theorem sample9 : shadePossible [1024,1536,1952,5700,7442,8715,18693,22568,24784]=false := by decide +kernel
theorem sample10 : shadePossible [1536,1952,5700,7442,7954,8715,18693,22568,24784]=false := by decide +kernel
theorem sample11 : shadePossible [1952,5700,6116,7442,8022,8715,18693,22568,24784]=true := by decide +kernel
theorem sample12 : shadePossible [1952,5700,6116,7442,8114,8715,18693,22568,24784]=true := by decide +kernel
end CoNum4358.Tiny.ShareGrid.Forest

namespace CoNum4358.Tiny.Splice
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 30
theorem layer7row : entry 6 0=true := by decide +kernel
theorem layer8row : entry 7 0=true := by decide +kernel
theorem layer9row : entry 8 0=true := by decide +kernel
theorem rootRow : entry 10 0=true := by decide +kernel
end CoNum4358.Tiny.Splice
namespace CoNum4358.Tiny.ShareGrid.Forest

open CoAO3143

def Correct (color : K→Bool) (ls : List Label) := ∀v∈ls,color v.wire=xor (color v.root) v.flip

theorem seed_ok (c : K→Bool) (xs : List K) : Correct c (seed xs) := by
  intro l hl
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp hl
  simp

private theorem located {ls : List Label} {x l} (h : locate ls x=some l) : l∈ls ∧ l.wire=x := by
  exact ⟨List.mem_of_find?_eq_some h,beq_iff_eq.mp (List.find?_some h)⟩

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

theorem compile_ok (c : K→Bool) (es : List (K×K)) (ls : List Label) (valid : Correct c ls)
    (ne : ∀e∈es,c e.1≠c e.2) : ∃rs,compile es ls=some rs ∧ Correct c rs ∧ rs.map Label.wire=ls.map Label.wire := by
  induction es generalizing ls with
  | nil => exact ⟨ls,rfl,valid,rfl⟩
  | cons e es ih =>
    obtain ⟨mid,eq,gm,wm⟩ := link_ok c valid (ne e List.mem_cons_self)
    obtain ⟨rs,out,gr,wr⟩ := ih mid gm (fun v hv => ne v (List.mem_cons_of_mem _ hv))
    exact ⟨rs,by simp [compile,eq,out],gr,wr.trans wm⟩

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

#print axioms compile_ok

#print axioms bands_painted

end CoNum4358.Tiny.ShareGrid.Forest

