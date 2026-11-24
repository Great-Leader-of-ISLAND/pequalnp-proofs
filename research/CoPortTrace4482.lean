import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace CoPortTrace4482

variable {W X : Type} [DecidableEq W]

def Distinguishes (eval : W → X → Bool) (label : X → Bool) (S : Finset W) : Prop :=
  ∀ x y, label x ≠ label y → ∃ w ∈ S, eval w x ≠ eval w y

inductive Bank (join : Bool → W → W → W) (root : Finset W) : Nat → Finset W → Prop
  | initial : Bank join root 0 root
  | skip {n T} (before : Bank join root n T) : Bank join root (n+1) T
  | gate {n T} (before : Bank join root n T) (d : Bool) (a b : W) (ha : a∈T) (hb : b∈T) :
      Bank join root (n+1) (insert (join d a b) T)

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
      · exact (absent (eq ▸ hx)).elim
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
      exact new ((idem d a).symm ▸ ha)
    have fresh : z∉insert a (insert b U) := fun h => new (back h)
    have after : insert z U=S := Finset.insert_erase hz
    have p : Path join terminal (k+1) (insert a (insert b U)) :=
      Path.step d a b distinct fresh (after.symm ▸ tail)
    obtain ⟨j,hj,A,hA,hp⟩ := ih back p
    exact ⟨j,by omega,A,hA,hp⟩

theorem separated {join : Bool → W → W → W} (eval : W → X → Bool) (label : X → Bool)
    (app : ∀ d a b x, eval (join d a b) x =
      if d then eval a x || eval b x else eval a x && eval b x)
    {limit k S} (path : Path join (fun U => U.card≤limit ∧ Distinguishes eval label U) k S) :
    Distinguishes eval label S := by
  induction path with
  | final _ h => exact h.2
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
