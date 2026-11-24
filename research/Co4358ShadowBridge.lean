import PEqualNP.Co4358Shadow

namespace CoNum4358
open CoAO3143

def augAt (bk : List Sig) (ts : List PairFlag) (i : Nat) : AugWire :=
  (lookupKW bk i,ts.getD i default)

def augProject (bk : List Sig) (ts : List PairFlag) (S : Finset Nat) : Finset AugWire :=
  S.image (augAt bk ts)

private theorem first_image (bk : List Sig) (ts : List PairFlag) (S : Finset Nat) :
    (augProject bk ts S).image Prod.fst=project bk S := by
  simp [augProject,project,augAt,Finset.image_image,Function.comp_def]

private theorem first_mem {k S bk} (live : Live k 0 (project bk S)) {i : Nat} (hi : i∈S) :
    i<bk.length := by
  by_contra! h
  have pr := live_proper live (lookupKW bk i) (Finset.mem_image_of_mem (lookupKW bk) hi)
  have e : lookupKW bk i=zero := by
    simp [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_eq_none h]
  exact pr.1 e

private theorem read_in {bk : List Sig} {i : Nat} (hi : i<bk.length) : lookupKW bk i∈bk := by
  simp only [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

private theorem read_snoc {α : Type} (xs : List α) (v d : α) (i : Nat) :
    (xs++[v]).getD i d = if i=xs.length then v else xs.getD i d := by
  induction xs generalizing i with
  | nil => cases i <;> simp
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ j => simpa using ih j

/-- Identify the paid raw source by its original signature, even after growing the bank. -/
structure HasRootTags (bk : List Sig) : Prop where
  present : ∀ a∈rawKW,a∈bk
  long : 2<bk.length
  label : ∀ i, i<bk.length → (lookupKW bk i=twoKW ↔ i=2)

private theorem initialTags : HasRootTags rawKW := by
  refine ⟨fun _ h => h,by decide +kernel,?_⟩
  intro i hi
  have test : ∀ j : Fin 7, lookupKW rawKW j.val=twoKW ↔ j.val=2 := by decide +kernel
  exact test ⟨i,hi⟩

private theorem extend_tags {bk : List Sig} (roots : HasRootTags bk) {z : Sig} (fresh : z∉bk) :
    HasRootTags (bk++[z]) := by
  refine ⟨fun a h => List.mem_append_left _ (roots.present a h),by
    simp only [List.length_append,List.length_cons,List.length_nil]
    have := roots.long
    omega,?_⟩
  have zne : z≠twoKW := by
    intro eq
    exact fresh (eq ▸ roots.present twoKW (by decide +kernel))
  intro i hi
  change ((bk++[z]).getD i zero=twoKW ↔ i=2)
  rw [read_snoc]
  by_cases e : i=bk.length
  · rw [if_pos e]
    have neq : i≠2 := by have := roots.long; omega
    simp [zne,neq]
  · rw [if_neg e]
    have lt : i<bk.length := by simp only [List.length_append,List.length_cons,List.length_nil] at hi; omega
    exact roots.label i lt

private theorem tag_bool {bk : List Sig} (roots : HasRootTags bk) {i : Nat} (hi : i<bk.length) :
    (lookupKW bk i==twoKW)=(i==2) := by
  by_cases e : lookupKW bk i=twoKW
  · have eq := (roots.label i hi).mp e
    subst i
    simp [e]
  · have ne : i≠2 := fun h => e ((roots.label i hi).mpr h)
    simp [e,ne]

private theorem project_inputs (bk : List Sig) (ts : List PairFlag) (g : Gate) (U : Finset Nat) :
    augProject bk ts (insert g.a (insert g.b U))=
      insert (augAt bk ts g.a) (insert (augAt bk ts g.b) (augProject bk ts U)) := by
  simp [augProject]

private theorem project_next (bk : List Sig) (ts : List PairFlag) (g : Gate) (U : Finset Nat)
    (len : ts.length=bk.length) (bound : ∀ i∈U,i<bk.length) :
    augProject (bk++[g.kw bk]) (ts++[g.pair ts]) (insert bk.length U) =
      insert (augGate g.isOr (augAt bk ts g.a) (augAt bk ts g.b)) (augProject bk ts U) := by
  unfold augProject
  rw [Finset.image_insert]
  have top : augAt (bk++[g.kw bk]) (ts++[g.pair ts]) bk.length =
      augGate g.isOr (augAt bk ts g.a) (augAt bk ts g.b) := by
    simp [augAt,augGate,Gate.kw,Gate.pair,lookupKW,read_snoc,len]
  rw [top]
  congr 1
  apply Finset.image_congr
  intro i hi
  have hb := bound i hi
  have ht : i<ts.length := by simpa only [len] using hb
  simp only [augAt,lookupKW,List.getD_eq_getElem?_getD,
    List.getElem?_append_left hb,List.getElem?_append_left ht]

theorem shadow_of_walk {k q bk bs S} (walk : Walk k q bk bs S) (ts : List PairFlag)
    (tracks : Tracks ts bs) (len : ts.length=bk.length) (roots : HasRootTags bk) :
    Shadow k q (augProject bk ts S) := by
  induction walk generalizing ts with
  | done q bk bs i orig raised =>
    have pair := tracks.lookup i 3 raised
    have h := Shadow.done q (augAt bk ts i) orig (pair.1.2 rfl rfl) (pair.2.2 rfl rfl)
    simpa [augProject] using h
  | @step k q bk bs U g sorted budget fresh live child ih =>
    let S := insert g.a (insert g.b U)
    have pin (i) (hi : i∈S) : i<bk.length := first_mem live hi
    have ha := pin g.a (by simp [S])
    have hb := pin g.b (by simp [S])
    have ub (i) (hi : i∈U) : i<bk.length := pin _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi))
    have old : g.kw bk∉bk := by
      intro h
      simp [gateAvailable,h] at fresh
    have properZ : proper (g.kw bk) := by
      constructor <;> intro h <;> simp [gateAvailable,h] at fresh
    have apart : augAt bk ts g.a ≠ augAt bk ts g.b := by
      intro eq
      have same : lookupKW bk g.a=lookupKW bk g.b := congrArg Prod.fst eq
      have zz : g.kw bk=lookupKW bk g.b := by
        unfold Gate.kw
        rw [same]
        rcases lookupKW bk g.b with ⟨x,y⟩
        cases g.isOr <;> simp [bin]
      exact old (zz ▸ read_in hb)
    have pay : augPay g.isOr (augAt bk ts g.a) (augAt bk ts g.b)=charge g := by
      simp only [augPay,augAt,tag_bool roots ha,tag_bool roots hb,charge]
    have lf : Local (k+1) (augProject bk ts S) := by
      constructor
      · rw [first_image]
        exact live
      · intro d
        obtain ⟨i,hi,can⟩ := live_capability (Walk.step g sorted budget fresh live child) d ts tracks len
        exact ⟨augAt bk ts i,Finset.mem_image_of_mem _ hi,can⟩
    have absent : (augGate g.isOr (augAt bk ts g.a) (augAt bk ts g.b)).1 ∉
        (augProject bk ts S).image Prod.fst := by
      rw [first_image]
      intro mem
      obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp mem
      change lookupKW bk i=g.kw bk at eq
      apply old
      rw [←eq]
      exact read_in (pin i hi)
    have newRaw : (augGate g.isOr (augAt bk ts g.a) (augAt bk ts g.b)).1 ∉ rawKW :=
      fun hm => old (roots.present _ hm)
    have next := ih (ts++[g.pair ts]) (tracks.gate g) (by simp [len]) (extend_tags roots old)
    rw [project_next bk ts g U len ub,←pay] at next
    change Local (k+1) (augProject bk ts (insert g.a (insert g.b U))) at lf
    rw [project_inputs] at lf
    change (augGate g.isOr (augAt bk ts g.a) (augAt bk ts g.b)).1 ∉
      (augProject bk ts (insert g.a (insert g.b U))).image Prod.fst at absent
    rw [project_inputs] at absent
    rw [project_inputs]
    exact Shadow.step _ _ _ apart (pay ▸ budget) properZ absent newRaw lf next

theorem shadow_root (walk : Walk 11 1 rawKW rawLoose (Finset.range 7)) :
    Shadow 11 1 augRoots.toFinset := by
  have eq : augProject rawKW rawPair (Finset.range 7)=augRoots.toFinset := by decide +kernel
  rw [←eq]
  exact shadow_of_walk walk rawPair raw_tracks (by decide +kernel) initialTags

end CoNum4358
