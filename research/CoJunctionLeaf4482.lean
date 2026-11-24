import PEqualNP.CoActualGroup4482
import PEqualNP.CoJunctionLogical4482
import PEqualNP.CoGlobalShape4482
import PEqualNP.CoRecipe4482
namespace CoJunctionLeaf4482
open CoPortRoots4482 CoPortFrontier4482 CoPortTrace4482 CoPortCut4482
open CoBlockSlots4482 CoBitBlock4482 CoGroupBlock4482 CoJunctionLogical4482

/-- Use the caller's coordinate ordering of the actual wires; this is the
ordering in which the group boxes and anchor masks have been checked. -/
noncomputable def slots {n : Nat} (v : Fin n → W) (inj : Function.Injective v) :
    Fin n ≃ ↥((List.ofFn v).toFinset) :=
  Equiv.ofBijective (fun i => ⟨v i,List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩)⟩)
    ⟨fun _ _ h => inj (congrArg Subtype.val h),by
      intro y
      obtain ⟨i,h⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp y.property)
      exact ⟨i,Subtype.ext h⟩⟩

theorem group_leaf {row : Record} {n : Nat} (g : G) (w : Fin n → CoRecipe4482.Entry)
    (inj : Function.Injective (fun i => (w i).full))
    (image : (stateWords row).toFinset.image (reorder (rowEquiv g)) =
      (List.ofFn (fun i => (w i).full)).toFinset)
    (size : n=6+row.budget)
    (anchors : List (Fin n)) (seven : 6<anchors.toFinset.card)
    (big : Fin n→Box) (bounds : ∀ i, fits (big i) (w i).projected=true)
    (inc : Fin n→BitVec (2^n))
    (digits : ∀i (j : Fin (2^n)), (inc i).getLsbD j.val=j.val.testBit i.val)
    (ids : List (Fin n)) (nd : ids.Nodup) (allIds : ∀ i, i∈ids)
    (fuel : Nat) (certified : checkGroup
      (List.ofFn (fun i => (⟨big i,inc i⟩ : BCol (2^n))))
      fuel (CoGlobalShape4482.required ids anchors inc)=true) :
    ¬ Path join (cleanCut model label 6) row.budget (stateWords row).toFinset := by
  let v := fun i => (w i).full
  let S := (List.ofFn v).toFinset
  let e := slots v inj
  have card : S.card=n := by
    calc S.card = Fintype.card (↥S) := (Fintype.card_coe S).symm
         _ = Fintype.card (Fin n) := (Fintype.card_congr e).symm
         _ = n := Fintype.card_fin n
  have ordered : ∀ z∈S,CoPortEdgeRows4482.Ordered z := by
    intro z mz
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp mz)
    exact eq ▸ (w i).ordered
  have stop := CoActualGroup4482.group_excludes (S:=S) (k:=row.budget)
    (card.trans size) ordered e (fun i => (w i).projected) (fun i => (w i).correct)
    big bounds anchors.toFinset seven inc digits (CoGlobalShape4482.required ids anchors inc)
    (fun j small many => CoGlobalShape4482.required_at ids anchors inc nd allIds digits j
      (by rwa [card] at small) many) fuel certified
  intro actual
  exact stop (image ▸ reorder_path (rowEquiv g) (respects_label g) actual)

#print axioms group_leaf
end CoJunctionLeaf4482
