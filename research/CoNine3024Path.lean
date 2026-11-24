import PEqualNP.CoNine3024PaidState
import PEqualNP.CoNine3024Transition
import PEqualNP.CoClean3024
import PEqualNP.CoNine3024Guard

namespace CoNine3024Path
open CoNine3024 CoNine3024Rows CoNine3024Transition CoNine3024PaidState
open CoAO3143Restriction CoClean3024 CoThetaNine

noncomputable section
local instance : DecidableEq (Wire Input) := Classical.decEq _

private theorem clock_width {s : State} {k S} (c : Cone ans k S)
    (img : (s.wires.map value).toFinset=S) (nd : (s.wires.map value).Nodup) :
    s.wires.length≤k+1 := by
  have n := List.toFinset_card_of_nodup nd
  rw [img,List.length_map] at n
  simpa only [←n] using card_le c

private theorem end_live (p : Fin 11) (s : State) (img : (s.wires.map value).toFinset={ans})
    (nd : (s.wires.map value).Nodup) : live (geom p) s=true := by
  have n := List.toFinset_card_of_nodup nd
  rw [img,Finset.card_singleton,List.length_map] at n
  cases h : s.wires with
  | nil => simp [h] at n
  | cons a as =>
    cases as with
    | cons b bs => simp [h] at n
    | nil =>
      have hh : value a=ans := by
        have eq := congrArg (fun F : Finset (Wire Input) => value a∈F) img
        simpa [h] using eq
      have word : a.full=targetWord := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        change value a ⟨i,hi⟩=_
        rw [hh,←truth_goal]
      simp [live,h,word,geom]

def SoundGuard (p : Fin 11) (keep : Nat → State → Bool) : Prop :=
  ∀ {k cap S} (s : State), k≤cap → Cone ans k S → (s.wires.map value).toFinset=S →
    (s.wires.map value).Nodup → (∀ w∈s.wires,Good p w) → keep cap s=true

private theorem gate_step (L : SignedLower) (p : Fin 11) (keep : Nat → State → Bool) (guard : SoundGuard p keep) {k cap : Nat} (kc : k≤cap)
    (s : State) (U : Finset (Wire Input)) (d : Bool) (a b : Atom)
    (ha : a∈s.wires) (hb : b∈s.wires) (ab : value a≠value b)
    (pair : (a,b)∈pairs s.wires)
    (nc : ¬Constant (op d (value a) (value b)))
    (left : op d (value a) (value b)≠value a) (right : op d (value a) (value b)≠value b)
    (fresh : op d (value a) (value b)∉U)
    (img : (s.wires.map value).toFinset=insert (value a) (insert (value b) U))
    (nd : (s.wires.map value).Nodup) (good : ∀w∈s.wires,Good p w)
    (acc : Accounts s (k+1)) (tail : Cone ans k (insert (op d (value a) (value b)) U))
    (continue : ∀ t : State, (t.wires.map value).toFinset=insert (op d (value a) (value b)) U →
      (t.wires.map value).Nodup → (∀w∈t.wires,Good p w) → Accounts t k → GuardPath keep (geom p) cap t) :
    Path (geom p) (cap+1) s := by
  let z := operation (geom p) d a b
  let t := next p d U s a b
  have valueZ : value z=op d (value a) (value b) := operation_value _ _ _ _
  have different (w) (hw : w∈s.wires) : value w≠op d (value a) (value b) := by
    intro e
    have h : value w∈(s.wires.map value).toFinset := by
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨w,hw,rfl⟩)
    rw [img,e] at h
    exact (Finset.mem_insert.mp h).elim left (fun hm => (Finset.mem_insert.mp hm).elim right fresh)
  have iz := next_images p d U s a b img
  have nz := next_nodup p d U s a b nd ab different ha hb
  have gz := next_good p d U s a b good ha hb
  have az : Accounts t k := advance p acc a b ha hb (good a ha) (good b hb) d (keepCode U a b)
  have width := clock_width tail iz nz
  have cover := covers p tail t.wires gz (by
    intro w hw
    exact List.mem_map.mp (List.mem_toFinset.mp (iz.symm ▸ hw)))
  have bz := safe_of_accounts L az gz nz tail iz
  have now := safe_of_accounts L acc good nd (Cone.gate d (value a) (value b) fresh tail) img
  have extra := guard s (Nat.succ_le_succ kc) (Cone.gate d (value a) (value b) fresh tail) img nd good
  apply GuardPath.gate extra now (t:=t)
  · apply child_mem (geom p) cap s a b d (keepCode U a b) pair (code_lt _ _ _)
    · intro e
      apply nc
      refine ⟨false,valueZ.symm.trans ?_⟩
      funext r
      change z.full.getLsbD r.val=false
      simp [show z.full=0 from e]
    · intro e
      apply nc
      refine ⟨true,valueZ.symm.trans ?_⟩
      funext r
      change z.full.getLsbD r.val=true
      simp [show z.full=BitVec.allOnes 512 from e,BitVec.getLsbD_allOnes,r.isLt]
    · intro w hw e
      exact different w hw (((CoNine3024Transition.full_eq w z).mp e).trans valueZ)
    · exact width.trans (by omega)
    · exact bz
    · exact cover
  · exact continue t iz nz gz az

theorem from_clean (L : SignedLower) (p : Fin 11) (keep : Nat → State → Bool) (guard : SoundGuard p keep) {k S} (c : Clean ans k S) {cap : Nat}
    (ck : k≤cap) (s : State) (img : (s.wires.map value).toFinset=S)
    (nd : (s.wires.map value).Nodup) (good : ∀w∈s.wires,Good p w)
    (acc : Accounts s k) : GuardPath keep (geom p) cap s := by
  induction c generalizing cap s with
  | stop => exact GuardPath.stop (end_live p s img nd)
  | @gate k U d a b ne nc left right fresh tail ih =>
    cases cap with
    | zero => omega
    | succ cap =>
      have find (w) (h : w∈insert a (insert b U)) : ∃ z∈s.wires,value z=w :=
        List.mem_map.mp (List.mem_toFinset.mp (img.symm ▸ h))
      obtain ⟨A,hA,rfl⟩ := find a (Finset.mem_insert_self _ _)
      obtain ⟨B,hB,rfl⟩ := find b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      rcases pair_or hA hB (fun e => ne (congrArg value e)) with ab|ba
      · exact gate_step L p keep guard (by omega) s U d A B hA hB ne ab nc left right fresh img nd good acc
          (toCone tail) (fun t ht nt gt at' => ih (by omega) t ht nt gt at')
      · have rev := scalar_comm d (value B) (value A)
        apply gate_step L p keep guard (by omega) s U d B A hB hA (Ne.symm ne) ba
        · simpa only [rev] using nc
        · simpa only [rev] using right
        · simpa only [rev] using left
        · simpa only [rev] using fresh
        · simpa only [Finset.insert_comm (value B) (value A)] using img
        · exact nd
        · exact good
        · exact acc
        · simpa only [rev] using toCone tail
        · intro t ht nt gt at'
          exact ih (by omega) t (by simpa only [rev] using ht) nt gt at'

#print axioms CoNine3024Path.from_clean
end
end CoNine3024Path
