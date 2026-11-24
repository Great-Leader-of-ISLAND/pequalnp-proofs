import PEqualNP.CoStarFamily3443

namespace CoStarLegal3443
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core CoStarFamily3443

theorem tip_before {n : ℕ} (hn : 1<n) (k : ℕ) : tip n k<n+k := by
  cases k with
  | zero => simpa [tip] using hn
  | succ k => simp [tip] <;> omega

private def headGate (n j : ℕ) : Gate := ⟨.or,[tip n j,j+2]⟩

theorem chain_at (n k j : ℕ) (hj : j<k) (fallback : Gate) :
    (chain n k).getD j fallback=headGate n j := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases old : j<k
    · have lt : j<(chain n k).length := by simpa using old
      simpa only [chain,List.getD_eq_getElem?_getD,List.getElem?_append_left lt] using ih old
    · have eq : j=k := by omega
      subst j
      simp [chain,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp : (chain n k).length≤k),headGate]

private theorem shapes (n k : ℕ) (g : Gate) (hg : g∈chain n k) :
    (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 := by
  induction k with
  | zero => simp [chain] at hg
  | succ k ih =>
    rcases List.mem_append.mp hg with old|last
    · exact ih old
    · obtain rfl := List.mem_singleton.mp last
      exact ⟨Or.inr rfl,rfl⟩

private theorem suffix_shapes (f u m : ℕ) (g : Gate) (h : g∈suffix f u m) :
    (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 := by
  simp only [suffix,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl <;> first | exact ⟨Or.inl rfl,rfl⟩ | exact ⟨Or.inr rfl,rfl⟩

private theorem suffix_before (n k u m t : ℕ) (hn : 0<n) (hu : u<n+k) (hm : m<n)
    (ht : t<4) (d : Gate) (w : ℕ) (hw : w∈((suffix (n+k) u m).getD t d).inputs) :
    w<n+(k+t) := by
  interval_cases t <;> simp [suffix,List.getD_eq_getElem?_getD] at hw <;> omega

theorem legal (q mark : ℕ) (hq : 1≤q) (hm : mark≤q) :
    IsAO2 (q+1) (circuit q mark) := by
  let n := q+1
  let k := q-1
  have hn : 1<n := by dsimp [n]; omega
  have shape (g : Gate) (hg : g∈(circuit q mark).gates) :
      (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 := by
    rcases List.mem_append.mp hg with h|h
    · exact shapes _ _ g h
    · exact suffix_shapes _ _ _ g h
  refine ⟨(fun g hg => (shape g hg).1),?_,(fun g hg => (shape g hg).2)⟩
  intro j bound w hw
  change j<(chain n k ++ suffix (n+k) (tip n k) mark).length at bound
  change w∈((chain n k ++ suffix (n+k) (tip n k) mark).getD j _).inputs at hw
  change w<n+j
  simp only [List.length_append,chain_length] at bound
  change j<k+4 at bound
  by_cases first : j<k
  · have lt : j<(chain n k).length := by simpa using first
    rw [List.getD_append _ _ _ _ lt,chain_at _ _ _ first] at hw
    change w∈[tip n j,j+2] at hw
    rcases (show w=tip n j ∨ w=j+2 by simpa using hw) with rfl|rfl
    · exact tip_before hn j
    · dsimp [n,k] at *
      omega
  · have le : (chain n k).length≤j := by simp; omega
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right le,chain_length] at hw
    have result := suffix_before n k (tip n k) mark (j-k) (by omega) (tip_before hn k)
      (by dsimp [n]; omega) (by omega) _ w hw
    omega

private def onWire (n : ℕ) (cs : List (List ℕ)) (w j : ℕ) : Prop :=
  n≤w ∧ w<n+cs.length ∧ (j=w-n ∨ j∈cs.getD (w-n) [])

private theorem cone_size (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).length=cs.length+1 := by simp [coneStep]

private theorem on_new (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    onWire n (coneStep n cs g) (n+cs.length) cs.length := by
  refine ⟨by omega,by rw [cone_size]; omega,Or.inl (by omega)⟩

private theorem on_old {n cs w j} (g : Gate) (old : onWire n cs w j) :
    onWire n (coneStep n cs g) w j := by
  rcases old with ⟨a,b,h⟩
  refine ⟨a,by rw [cone_size]; omega,?_⟩
  rcases h with eq|hit
  · exact Or.inl eq
  · right
    simpa only [coneStep,List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega : w-n<cs.length)] using hit

private theorem pass {n cs w j} (g : Gate) (pin : w∈g.inputs) (old : onWire n cs w j) :
    onWire n (coneStep n cs g) (n+cs.length) j := by
  rcases old with ⟨a,b,h⟩
  refine ⟨by omega,by rw [cone_size]; omega,Or.inr ?_⟩
  rw [show n+cs.length-n=cs.length by omega]
  simp only [coneStep,List.getD_eq_getElem?_getD,List.getElem?_append_right (le_refl cs.length),
    Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
  apply List.mem_flatMap.mpr
  refine ⟨w,List.mem_filter.mpr ⟨pin,decide_eq_true ⟨a,b⟩⟩,?_⟩
  exact List.mem_cons.mpr h

private theorem extends_root {n : ℕ} {cs : List (List ℕ)} {w : ℕ} (g : Gate) (read : w∈g.inputs)
    (root : ∀j<cs.length,onWire n cs w j) :
    ∀j<(coneStep n cs g).length,onWire n (coneStep n cs g) (n+cs.length) j := by
  intro j h
  rw [cone_size] at h
  by_cases prev : j<cs.length
  · exact pass g read (root j prev)
  · have eq : j=cs.length := by omega
    exact eq ▸ on_new n cs g

private def block (n k : ℕ) := (chain n k).foldl (coneStep n) []
private theorem prefix_covers (n k : ℕ) : (block n k).length=k ∧
    ∀j<k,onWire n (block n k) (tip n k) j := by
  induction k with
  | zero => exact ⟨rfl,by omega⟩
  | succ k ih =>
    let g := headGate n k
    have next : block n (k+1)=coneStep n (block n k) g := by simp [block,chain,g,headGate,List.foldl_append]
    rw [next,cone_size,ih.1]
    refine ⟨rfl,?_⟩
    intro j hj
    have result := extends_root (n:=n) (cs:=block n k) g (w:=tip n k) (by simp [g,headGate])
      (fun v hv => ih.2 v (ih.1 ▸ hv)) j (by rw [cone_size,ih.1]; exact hj)
    simpa only [ih.1,tip] using result

private theorem joined {n : ℕ} (cs : List (List ℕ)) (w m : ℕ)
    (root : ∀j<cs.length,onWire n cs w j) :
    let f := n+cs.length
    let last := (suffix f w m).foldl (coneStep n) cs
    ∀j<last.length,onWire n last (f+3) j := by
  let f := n+cs.length
  let Z : Gate := ⟨.and,[w,m]⟩
  let A : Gate := ⟨.and,[0,f]⟩
  let B : Gate := ⟨.and,[0,w]⟩
  let O : Gate := ⟨.or,[f+1,f+2]⟩
  let z := coneStep n cs Z
  let a := coneStep n z A
  let b := coneStep n a B
  let o := coneStep n b O
  have zlen : z.length=cs.length+1 := cone_size _ _ _
  have alen : a.length=cs.length+2 := by dsimp only [a]; rw [cone_size,zlen]
  have blen : b.length=cs.length+3 := by dsimp only [b]; rw [cone_size,alen]
  have olen : o.length=cs.length+4 := by dsimp only [o]; rw [cone_size,blen]
  have rz : ∀j<z.length,onWire n z f j := extends_root Z (by simp [Z]) root
  have ra0 := extends_root A (show f∈A.inputs by simp [A]) rz
  have ra : ∀j<a.length,onWire n a (f+1) j := by
    intro j hj
    have out := ra0 j hj
    have ek : n+z.length=f+1 := by dsimp [f]; omega
    simpa only [ek] using out
  change ∀j<o.length,onWire n o (f+3) j
  intro j hj
  have endwire : f+3=n+b.length := by dsimp [f]; omega
  rw [endwire]
  by_cases early : j<a.length
  · exact pass O (show f+1∈O.inputs by simp [O]) (on_old B (ra j early))
  · by_cases middle : j<b.length
    · have eq : j=a.length := by omega
      have wire : f+2=n+a.length := by dsimp [f]; omega
      apply pass O (w:=f+2) (by simp [O])
      rw [eq,wire]
      exact on_new n a B
    · have eq : j=b.length := by omega
      exact eq ▸ on_new n b O

theorem all_live (q mark : ℕ) (j : ℕ) (hj : j<(circuit q mark).gates.length) :
    InOutputCone (q+1) (circuit q mark) j := by
  let n := q+1
  let k := q-1
  let cs := block n k
  have len : cs.length=k := (prefix_covers n k).1
  have root : ∀v<cs.length,onWire n cs (tip n k) v := fun v hv => (prefix_covers n k).2 v (len ▸ hv)
  let current := (suffix (n+cs.length) (tip n k) mark).foldl (coneStep n) cs
  have same : cones n (circuit q mark)=current := by
    change (chain n k ++ suffix (n+k) (tip n k) mark).foldl (coneStep n) []=_
    rw [List.foldl_append]
    change (suffix (n+k) (tip n k) mark).foldl (coneStep n) cs =
      (suffix (n+cs.length) (tip n k) mark).foldl (coneStep n) cs
    rw [len]
  have sz : current.length=k+4 := by
    simp only [current,suffix,List.foldl_cons,List.foldl_nil,cone_size,len]
  have before : j<k+4 := by simpa [circuit,k,chain_length,suffix] using hj
  have res := joined cs (tip n k) mark root j (by change j<current.length; omega)
  change onWire n current (n+cs.length+3) j at res
  rcases res with ⟨start,_,root'|inside⟩
  · exact ⟨hj,Or.inl (by change n+k+3=n+j; omega)⟩
  · refine ⟨hj,Or.inr ⟨by change n≤n+k+3; omega,?_⟩⟩
    change j∈(cones n (circuit q mark)).getD (n+k+3-n) []
    simpa only [same,len] using inside

#print axioms CoStarLegal3443.legal
#print axioms CoStarLegal3443.all_live
end CoStarLegal3443
