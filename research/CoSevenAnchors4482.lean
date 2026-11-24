import PEqualNP.CoBlockPhysical4482
import PEqualNP.CoBlockIntervals4482

namespace CoSevenAnchors4482
open CoTightBlocks4482 CoBitBlock4482 CoBlockIntervals4482
variable {W X : Type} [DecidableEq W]

/-- A proper surjective ownership map must put two of more than |T|
anchors together. Every such block has at most |S|-(|T|-1) wires. -/
theorem anchored_block {ev : W → X → Bool} {S T : Finset W}
    (B : Blocks ev S T) (A : Finset W) (sub : A⊆S) (many : T.card<A.card) :
    ∃ t∈T, ∃ a∈A, ∃ b∈A, a≠b ∧ B.owner a=t ∧ B.owner b=t ∧
      (S.filter (fun w => B.owner w=t)).card + (T.card-1) ≤ S.card := by
  classical
  let f : ↥A → ↥T := fun x => ⟨B.owner x.val, B.lands _ (sub x.property)⟩
  have collision : ∃ x y : ↥A, x≠y ∧ f x=f y := by
    by_contra no
    have inj : Function.Injective f := by
      intro x y e
      by_contra ne
      exact no ⟨x,y,ne,e⟩
    have small : A.card≤T.card := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f inj
    omega
  obtain ⟨a,b,ab,same⟩ := collision
  let t := B.owner a.val
  have ht : t∈T := B.lands _ (sub a.property)
  have bt : B.owner b.val=t := (congrArg Subtype.val same).symm
  let block := S.filter (fun w => B.owner w=t)
  have small : block⊆S := Finset.filter_subset _ _
  have loaded : T.erase t ⊆ (S \ block).image B.owner := by
    intro z mz
    obtain ⟨ne,mz⟩ := Finset.mem_erase.mp mz
    obtain ⟨w,mw,e⟩ := B.onto z mz
    have off : w∉block := by
      intro hit
      exact ne (e.symm.trans (Finset.mem_filter.mp hit).2)
    exact Finset.mem_image.mpr ⟨w,Finset.mem_sdiff.mpr ⟨mw,off⟩,e⟩
  have count := (Finset.card_le_card loaded).trans Finset.card_image_le
  rw [Finset.card_erase_of_mem ht,Finset.card_sdiff_of_subset small] at count
  have blocksize := Finset.card_le_card small
  exact ⟨t,ht,a.val,a.property,b.val,b.property,fun h => ab (Subtype.ext h),
    rfl,bt,by change block.card+(T.card-1)≤S.card; omega⟩

/-- Each selected mask slot describes the membership of each individual live
wire. An independently checkable interval cover makes such a physical
ownership impossible, even if its individual output functions are unknown. -/
theorem covered_impossible {ev : W → X → Bool} {S T : Finset W}
    (B : Blocks ev S T) (lo hi : Row → X) (mark : W → Mark)
    (pos : ∀ w i, bit (mark w).1 i=ev w (hi i))
    (neg : ∀ w i, bit (mark w).2 i=ev w (lo i))
    (ord : ∀ i w, w∈S → ev w (lo i)=true → ev w (hi i)=true)
    (det : ∀ i, ∃ w∈T, ev w (lo i)≠ev w (hi i))
    (A : Finset W) (sub : A⊆S) (many : T.card<A.card)
    {k : Nat} (col : W → Col k) (cols : List (Col k))
    (incl : ∀w∈S,col w∈cols) (marks : ∀w∈S,(col w).data=mark w)
    (pairs : List (Row×Row)) (must : BitVec k) (verified : must &&& cover cols pairs=must)
    (slots : ∀ t∈T, ∀ a∈A, ∀ b∈A, a≠b → B.owner a=t → B.owner b=t →
      (S.filter (fun w => B.owner w=t)).card+(T.card-1)≤S.card →
      ∃ j : Fin k, must.getLsbD j.val=true ∧
        ∀ w∈S, (col w).inc.getLsbD j.val=decide (B.owner w=t)) : False := by
  obtain ⟨t,mt,a,ma,b,mb,ab,oa,ob,sz⟩ := anchored_block B A sub many
  obtain ⟨j,yes,eq⟩ := slots _ mt _ ma _ mb ab oa ob sz
  obtain ⟨i,i',hit⟩ := required_witness cols pairs must verified j yes
  apply CoBlockPhysical4482.no_pair B lo hi mark pos neg ord det mt i i'
  · intro w mw outside
    have zero : (col w).inc.getLsbD j.val=false := by rw [eq w mw]; exact decide_eq_false outside
    have h := (hit _ (incl w mw)).1 zero
    rw [marks w mw] at h
    exact h
  · intro w mw inside
    have one : (col w).inc.getLsbD j.val=true := by rw [eq w mw]; exact decide_eq_true inside
    have h := (hit _ (incl w mw)).2 one
    rw [marks w mw] at h
    exact h

#print axioms anchored_block
#print axioms covered_impossible
end CoSevenAnchors4482
