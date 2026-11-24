import PEqualNP.CoThetaOriginal
namespace PEqualNP.Research.SignTheta
open CoThetaFreeCore CoThetaNine

def signed {R : Type} (f : Nat → R → Bool) (a : Nat × Bool) (r : R) := f a.1 r ^^ a.2

theorem supply_lit {R : Type} (raw : List (R→Bool)) {n xs} (run : Ordinary raw n xs)
    (f : Nat → R→Bool) (a : Nat × Bool) (h : f a.1∈xs) :
    ∃ ys, Ordinary raw n ys ∧ signed f a ∈ ys ∧ ∀ v∈xs, v∈ys := by
  rcases a with ⟨j,b⟩
  cases b with
  | false =>
    refine ⟨xs,run,?_,fun _ mem => mem⟩
    have eq : signed f (j,false) = f j := by funext r; simp [signed]
    rwa [eq]
  | true =>
    refine ⟨_,Ordinary.inv run h,?_,fun v hv => List.mem_cons_of_mem _ hv⟩
    have eq : signed f (j,true) = fun r => !(f j r) := by funext r; simp [signed]
    rw [eq]
    exact List.mem_cons_self

theorem toOrdinary {R : Type} (raw : List (R→Bool)) (f : Nat → R→Bool) (n m : Nat)
    (root : ∀ j<n, f j∈raw) (a b : Fin m → Nat × Bool) (op : Fin m→Bool)
    (order : ∀ i, (a i).1<n+i.val ∧ (b i).1<n+i.val)
    (gates : ∀ i, f (n+i.val) = (fun r => base (op i) (signed f (a i) r) (signed f (b i) r))) :
    ∀ t≤m, ∃ xs, Ordinary raw t xs ∧ ∀ j<n+t, f j∈xs := by
  intro t
  induction t with
  | zero => intro _; exact ⟨raw,Ordinary.start,by simpa using root⟩
  | succ t ih =>
    intro ht
    obtain ⟨xs,run,old⟩ := ih (by omega)
    let i : Fin m := ⟨t,by omega⟩
    obtain ⟨ys,first,l,sub1⟩ := supply_lit raw run f (a i) (old _ (order i).1)
    obtain ⟨zs,both,r,sub2⟩ := supply_lit raw first f (b i) (sub1 _ (old _ (order i).2))
    refine ⟨_, Ordinary.binary both (op i) (sub2 _ l) r,?_⟩
    intro j hj
    by_cases fresh : j=n+t
    · subst j
      rw [show n+t=n+i.val from rfl,gates i]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub2 _ (sub1 _ (old _ (by omega))))

theorem tight (cert : CoThetaBits.certifiedSearch 10 CoThetaBits.raw=false)
    (f : Nat → Input→Bool) (m : Nat) (a b : Fin m → Nat × Bool) (op : Fin m→Bool) (out : Nat×Bool)
    (root : ∀ j<10, f j∈vertices)
    (order : ∀ i, (a i).1<10+i.val ∧ (b i).1<10+i.val) (hout : out.1<10+m)
    (gates : ∀ i, f (10+i.val) = (fun r => base (op i) (signed f (a i) r) (signed f (b i) r)))
    (correct : signed f out=ans) : 14≤m := by
  obtain ⟨xs,run,old⟩ := toOrdinary vertices f 10 m root a b op order gates m (le_refl _)
  obtain ⟨ys,complete,mem,_⟩ := supply_lit vertices run f out (old _ hout)
  obtain ⟨zs,free,cover⟩ := simulate_all_wires (row 0) complete
  rw [correct] at mem
  have final := cover _ mem
  have zero : ans (row 0)=false := by decide
  have normed : norm (row 0) ans=ans := by funext r; simp [CoThetaFreeCore.norm,phase,zero]
  rw [normed] at final
  obtain ⟨gs,len,reg,eq⟩ := trace_of_free free
  have roots : ∀ v ∈ vertices.map (norm (row 0)), v∈vertices := by
    intro v mem
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp mem
    have z : q (row 0)=false := by
      rcases List.mem_cons.mp hq with rfl | source
      · rfl
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp source
        simp [vtx,row]
    have ne : norm (row 0) q=q := by funext r; simp [CoThetaFreeCore.norm,phase,z]
    rwa [ne]
  have sub := trace_subset gs roots
  have actual : sufficient vertices ans gs := ⟨sub.1 reg, sub.2 _ (eq ▸ final)⟩
  have bound := any_nine_lower cert actual
  omega
end PEqualNP.Research.SignTheta
