import PEqualNP.Co4358Clean
import PEqualNP.Co4358Search

namespace CoNum4358.Routes
open CoAO3143

theorem trail_bounded {off gs S} (t : DirTrail off gs S) (pos : 0<off) :
    ∀ i∈S, i<off := by
  induction t with
  | done => simp only [Finset.mem_singleton]; intro i eq; omega
  | @step off gs U g sane notIn tail ih =>
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|h
    · exact sane.1
    rcases Finset.mem_insert.mp h with rfl|h
    · exact sane.2.1
    have b := ih (by omega) i (Finset.mem_insert_of_mem h)
    have ne : i ≠ off := fun eq => notIn (eq ▸ h)
    omega

private theorem at_pin {bk : List Sig} {i : Nat} (hi : i < bk.length) :
    lookupKW bk i ∈ bk := by
  simp only [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

private theorem before {bk : List Sig} {i : Nat} (hi : i < bk.length) (z : Sig) :
    lookupKW (bk++[z]) i=lookupKW bk i := by
  simp [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_append,hi]

private theorem after (bk : List Sig) (z : Sig) : lookupKW (bk++[z]) bk.length=z := by
  simp [lookupKW,List.getD_eq_getElem?_getD]

private theorem projected {bk : List Sig} {off : Nat} {U : Finset Nat}
    (len : bk.length=off) (bound : ∀ i∈U, i<off) (z : Sig) :
    project (bk++[z]) (insert off U) = insert z (project bk U) := by
  subst off
  unfold project
  rw [Finset.image_insert,after]
  congr 1
  exact Finset.image_congr fun i hi => before (bound i hi) z

private theorem projected_old (bk : List Sig) (g : Gate) (U : Finset Nat) :
    project bk (insert g.a (insert g.b U)) =
      insert (lookupKW bk g.a) (insert (lookupKW bk g.b) (project bk U)) := by
  simp [project,Finset.image_insert]

theorem extract {off gs S} (trace : DirTrail off gs S) (pos : 0<off)
    (bk : List Sig) (bs : List LiftSet) (q : Nat)
    (len : bk.length=off) (regular : ∀ w∈bk,proper w)
    (clean : Clean bk gs) (ordered : ∀ g∈gs,g.a≤g.b)
    (limit : (gs.map charge).sum≤q)
    (hit : lookupKW (bankKW bk gs) (off+gs.length-1)=CoAO3143.target)
    (lifted : (3 : LiftVal)∈(bankLoose bs gs).getD (off+gs.length-1) []) :
    Live gs.length 0 (project bk S) ∧ Walk gs.length q bk bs S := by
  induction trace generalizing bk bs q with
  | @done off =>
    have yes : lookupKW bk (off-1) = CoAO3143.target := by simpa [bankKW] using hit
    have mem : (3 : LiftVal)∈bs.getD (off-1) [] := by simpa [bankLoose] using lifted
    exact ⟨by simpa [project,yes] using (Live.stop),Walk.done q bk bs (off-1) yes mem⟩
  | @step off gs U g sane noff tail ih =>
    let next := bk++[g.kw bk]
    have cap : next.length=off+1 := by simp [next,len]
    have fresh := clean.2.1
    have pr : proper (g.kw bk) := ⟨fun h => fresh (Or.inl h),fun h => fresh (Or.inr (Or.inl h))⟩
    have nonmember : g.kw bk∉bk := fun h => fresh (Or.inr (Or.inr h))
    have good (w) (h : w∈next) : proper w := by
      rcases List.mem_append.mp h with m|e
      · exact regular _ m
      · exact List.mem_singleton.mp e ▸ pr
    have eq : off+1+gs.length-1 = off+(g::gs).length-1 := by simp only [List.length_cons]; omega
    have cost : charge g + (gs.map charge).sum≤q := by simpa only [List.map_cons,List.sum_cons] using limit
    obtain ⟨small,walk⟩ := ih (by omega) next (bs++[g.loose bs]) (q-charge g) cap good clean.2.2
      (fun t h => ordered t (List.mem_cons_of_mem _ h)) (by omega) (eq.symm ▸ hit) (eq.symm ▸ lifted)
    have earlier (i) (hi : i∈U) : i<off := by
      have h := trail_bounded tail (by omega) i (Finset.mem_insert_of_mem hi)
      have n : i≠off := fun eq => noff (eq ▸ hi)
      omega
    have s : project next (insert off U) = insert (g.kw bk) (project bk U) := projected len earlier _
    rw [s] at small
    have ma := at_pin (bk:=bk) (i:=g.a) (len ▸ sane.1)
    have mb := at_pin (bk:=bk) (i:=g.b) (len ▸ sane.2.1)
    have diff : lookupKW bk g.a ≠ lookupKW bk g.b := by
      intro same
      have z : g.kw bk = lookupKW bk g.b := by
        dsimp [Gate.kw]
        rw [same]
        rcases lookupKW bk g.b with ⟨x,y⟩
        cases g.isOr <;> simp [CoAO3143.bin]
      exact nonmember (z ▸ mb)
    have unused : g.kw bk ∉ insert (lookupKW bk g.a) (insert (lookupKW bk g.b) (project bk U)) := by
      intro m
      rcases Finset.mem_insert.mp m with e|m
      · exact nonmember (e ▸ ma)
      rcases Finset.mem_insert.mp m with e|m
      · exact nonmember (e ▸ mb)
      obtain ⟨i,hi,e⟩ := Finset.mem_image.mp m
      exact nonmember (e ▸ at_pin (bk:=bk) (len ▸ earlier _ hi))
    have live : Live (g::gs).length 0 (project bk (insert g.a (insert g.b U))) := by
      rw [projected_old]
      exact Live.binary (regular _ ma) (regular _ mb) diff unused small
    have ga : gateAvailable bk (g.kw bk)=true := by simp [gateAvailable,nonmember,pr.1,pr.2]
    have order := ordered g List.mem_cons_self
    have w : Walk (gs.length+1) q bk bs (insert g.a (insert g.b U)) :=
      Walk.step g (by have := sane.2.2; omega) (by omega) ga live (by simpa only [len] using walk)
    exact ⟨live,w⟩

end CoNum4358.Routes
