import PEqualNP.CoNine3024Rows
import PEqualNP.CoNine3024Split

namespace CoNine3024Transition
open CoNine3024 CoNine3024Rows CoAO3143Restriction CoThetaNine

noncomputable section
local instance : DecidableEq (Wire Input) := Classical.decEq _

theorem full_eq (a b : Atom) : a.full=b.full ↔ value a=value b := by
  constructor
  · intro h; funext r; simp only [value,h]
  · exact full_inj

def keepCode (U : Finset (Wire Input)) (a b : Atom) : Nat :=
  if value a∈U then (if value b∈U then 3 else 1) else (if value b∈U then 2 else 0)

theorem code_lt (U : Finset (Wire Input)) (a b : Atom) : keepCode U a b<4 := by
  unfold keepCode
  split <;> split <;> decide

theorem kept (s : State) (a b : Atom) (w : Wire Input) :
    w∈(rest s a b).map value ↔ w∈s.wires.map value ∧ w≠value a ∧ w≠value b := by
  constructor
  · intro h
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
    obtain ⟨old,diff⟩ := List.mem_filter.mp hx
    simp only [Bool.and_eq_true,bne_iff_ne] at diff
    exact ⟨List.mem_map.mpr ⟨x,old,rfl⟩,fun e => diff.1 ((full_eq x a).mpr e),fun e => diff.2 ((full_eq x b).mpr e)⟩
  · rintro ⟨h,na,nb⟩
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
    refine List.mem_map.mpr ⟨x,List.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    simp only [Bool.and_eq_true,bne_iff_ne]
    exact ⟨fun e => na ((full_eq x a).mp e),fun e => nb ((full_eq x b).mp e)⟩

theorem keep_mem (U : Finset (Wire Input)) (a b : Atom) (w : Wire Input) :
    w∈(maskKeep a b (keepCode U a b)).map value ↔
      (w=value a ∧ value a∈U) ∨ (w=value b ∧ value b∈U) := by
  by_cases ha : value a∈U <;> by_cases hb : value b∈U <;> simp [keepCode,ha,hb,maskKeep]

def next (p : Fin 11) (d : Bool) (U : Finset (Wire Input)) (s : State) (a b : Atom) : State :=
  child s a b (operation (geom p) d a b) (rest s a b) (keepCode U a b)

theorem next_images (p : Fin 11) (d : Bool) (U : Finset (Wire Input)) (s : State) (a b : Atom)
    (images : (s.wires.map value).toFinset=insert (value a) (insert (value b) U)) :
    ((next p d U s a b).wires.map value).toFinset=insert (op d (value a) (value b)) U := by
  ext w
  change w∈((operation (geom p) d a b::(maskKeep a b (keepCode U a b) ++ rest s a b)).map value).toFinset ↔ _
  have before : w∈s.wires.map value ↔ w=value a ∨ w=value b ∨ w∈U := by
    change w∈s.wires.map value ↔ _
    simpa only [List.mem_toFinset,Finset.mem_insert] using
      (show w∈(s.wires.map value).toFinset ↔ w∈insert (value a) (insert (value b) U) by rw [images])
  simp only [List.mem_toFinset,List.map_cons,List.map_append,List.mem_cons,List.mem_append,
    operation_value,keep_mem,kept,before,Finset.mem_insert]
  constructor
  · rintro (eq|(⟨rfl,hit⟩|⟨rfl,hit⟩)|⟨(eq|eq|old),na,nb⟩)
    · exact Or.inl eq
    · exact Or.inr hit
    · exact Or.inr hit
    · exact (na eq).elim
    · exact (nb eq).elim
    · exact Or.inr old
  · rintro (out|old)
    · exact Or.inl out
    by_cases aa : w=value a
    · exact Or.inr (Or.inl (Or.inl ⟨aa,aa ▸ old⟩))
    by_cases bb : w=value b
    · exact Or.inr (Or.inl (Or.inr ⟨bb,bb ▸ old⟩))
    exact Or.inr (Or.inr ⟨Or.inr (Or.inr old),aa,bb⟩)

theorem next_nodup (p : Fin 11) (d : Bool) (U : Finset (Wire Input)) (s : State) (a b : Atom)
    (nd : (s.wires.map value).Nodup) (diff : value a≠value b)
    (fresh : ∀ w∈s.wires,value w≠op d (value a) (value b))
    (ha : a∈s.wires) (hb : b∈s.wires) : ((next p d U s a b).wires.map value).Nodup := by
  let r := (rest s a b).map value
  have sub : (rest s a b).Sublist s.wires := List.filter_sublist
  have nr : r.Nodup := (sub.map value).nodup nd
  have na : value a∉r := fun h => ((kept s a b _).mp h).2.1 rfl
  have nb : value b∉r := fun h => ((kept s a b _).mp h).2.2 rfl
  have az := fresh a ha; have bz := fresh b hb
  have rz : op d (value a) (value b)∉r := by
    intro h
    obtain ⟨w,mem,eq⟩ := List.mem_map.mp ((kept s a b _).mp h).1
    exact fresh w mem eq
  change ((operation (geom p) d a b::(maskKeep a b (keepCode U a b) ++ rest s a b)).map value).Nodup
  by_cases aa : value a∈U <;> by_cases bb : value b∈U <;>
    simp [keepCode,aa,bb,maskKeep,operation_value,show (rest s a b).map value=r from rfl,
      nr,na,nb,rz,diff,Ne.symm az,Ne.symm bz]

theorem next_good (p : Fin 11) (d : Bool) (U : Finset (Wire Input)) (s : State) (a b : Atom)
    (good : ∀w∈s.wires,Good p w) (ha : a∈s.wires) (hb : b∈s.wires) :
    ∀ w∈(next p d U s a b).wires,Good p w := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl|hw
  · exact operation_good p d (good a ha) (good b hb)
  rcases List.mem_append.mp hw with kept'|old
  · have split : w=a ∨ w=b := by
      by_cases aa : value a∈U <;> by_cases bb : value b∈U <;>
        simp [keepCode,aa,bb,maskKeep] at kept' <;> tauto
    rcases split with wa|wb
    · exact wa.symm ▸ good a ha
    · exact wb.symm ▸ good b hb
  · exact good w (List.mem_filter.mp old).1

theorem card_le {out : Wire Input} {k S} (c : Cone out k S) : S.card≤k+1 := by
  induction c with
  | stop => simp
  | @gate k U d a b fresh tail ih =>
    rw [Finset.card_insert_of_notMem fresh] at ih
    have e := Finset.card_insert_le a (insert b U)
    have e' := Finset.card_insert_le b U
    omega
end
end CoNine3024Transition
