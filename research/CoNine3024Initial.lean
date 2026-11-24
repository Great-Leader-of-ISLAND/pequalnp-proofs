import PEqualNP.CoPhysical3024
namespace CoNine3024Initial
open CoThetaNine CoThetaFreeCore CoAO3143Restriction CoAllRaw3024

noncomputable section
local instance {α : Type} : DecidableEq (Wire α) := Classical.decEq _

private theorem signed_cone {t S} (c : Cone ans t S) {h pool} (pre : Free vertices h pool)
    (known : ∀ w∈S,norm (row 0) w∈pool) :
    ∃ ys, Free vertices (h+t) ys ∧ norm (row 0) ans∈ys := by
  induction c generalizing h pool with
  | stop => exact ⟨pool,pre,known _ (by simp)⟩
  | @gate k U d a b fresh tail ih =>
    let g := normalizedKind d (a (row 0)) (b (row 0))
    have pa := known a (Finset.mem_insert_self _ _)
    have pb := known b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have next := Free.binary pre g pa pb
    obtain ⟨ys,program,out⟩ := ih next (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl|old
      · change norm (row 0) (fun r => base d (a r) (b r))∈_
        rw [normalize_binary]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (known w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old))))
    exact ⟨ys,(by simpa only [show h+1+k=h+(k+1) by omega] using program),out⟩

theorem unseeded (L : SignedLower) {k S} (c : Cone ans k S)
    (known : ∀ w∈S,norm (row 0) w∈vertices) : 14≤k := by
  obtain ⟨ys,run,hit⟩ := signed_cone c (Free.start (raw:=vertices)) known
  have same : norm (row 0) ans=ans := by
    have z : ans (row 0)=false := by decide
    funext r; simp [CoThetaFreeCore.norm,phase,z]
  rw [same] at hit
  obtain ⟨gs,len,reg,eq⟩ := trace_of_free run
  have price := any_nine_lower L (gs:=gs) ⟨reg,eq ▸ hit⟩
  omega

theorem ans_varies : ¬Constant ans := by
  rintro ⟨b,e⟩
  have a := congrFun e (row 0)
  have u := congrFun e (row 3)
  have h0 : ans (row 0)=false := by decide
  have h3 : ans (row 3)=true := by decide
  change ans _=b at a u
  exact Bool.false_ne_true (h0.symm.trans (a.trans (u.symm.trans h3)))

theorem options (p : Fin 11) {k S} (clean : CoClean3024.Clean ans k S)
    (lab : ∀ w∈S,∃ j,w=label p j) (w) (hw : w∈S) :
    (∃ i : Fin 9,w=vtx i) ∨ w=seed ∨ w=inverse p := by
  obtain ⟨j,rfl⟩ := lab w hw
  by_cases raw : j.val<9
  · exact Or.inl ⟨⟨j.val,raw⟩,by simp [label,raw]⟩
  by_cases s : j.val=9
  · exact Or.inr (Or.inl (by simp [label,raw,s]))
  by_cases n : j.val=10
  · exact Or.inr (Or.inr (by simp [label,raw,s,n]))
  exact (CoClean3024.inputs_vary clean ans_varies _ hw ⟨decide (j.val=12),by simp [label,raw,s,n]⟩).elim

private theorem norm_raw (i : Fin 9) : norm (row 0) (vtx i)∈vertices := by
  have zero : ∀ i : Fin 9, vtx i (row 0)=false := by decide
  have eq : norm (row 0) (vtx i)=vtx i := by
    funext r; simp [CoThetaFreeCore.norm,phase,zero]
  rw [eq]; exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem must_use_seed (L : SignedLower) (p : Fin 11) {k S} (small : k≤13)
    (clean : CoClean3024.Clean ans k S) (lab : ∀ w∈S,∃ j,w=label p j) :
    seed∈S ∨ (p=9 ∧ inverse p∈S) := by
  by_contra nope
  have lower := unseeded L (CoClean3024.toCone clean) (by
    intro w hw
    rcases options p clean lab w hw with ⟨i,rfl⟩|rfl|rfl
    · exact norm_raw i
    · exact (nope (Or.inl hw)).elim
    · by_cases little : p.val<9
      · have eq : norm (row 0) (inverse p)=norm (row 0) (vtx ⟨p.val,little⟩) := by
          funext r
          simp only [inverse,dif_pos little,CoThetaFreeCore.norm]
          cases vtx ⟨p.val,little⟩ (row 0) <;> cases vtx ⟨p.val,little⟩ r <;> rfl
        rw [eq]; exact norm_raw _
      by_cases q : p.val=9
      · exact (nope (Or.inr ⟨Fin.ext q,hw⟩)).elim
      · have const : Constant (inverse p) := ⟨true,by simp [inverse,little,q]⟩
        exact (CoClean3024.inputs_vary clean ans_varies _ hw const).elim)
  omega

#print axioms CoNine3024Initial.must_use_seed
end
end CoNine3024Initial
