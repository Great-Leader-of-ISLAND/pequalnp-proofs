import PEqualNP.CoSevenAnchors4482

namespace CoBlockSlots4482
open CoTightBlocks4482 CoBitBlock4482 CoBlockIntervals4482

def pack {n : Nat} (f : Fin n → Bool) : Fin (2^n) :=
  (BitVec.ofBoolListLE (List.ofFn f)).toFin.cast (by simp [List.length_ofFn])

theorem pack_bit {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (pack f).val.testBit i.val=f i := by
  change (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

def members {n : Nat} (j : Fin (2^n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => j.val.testBit i.val=true

/-- The certificate consists entirely of numeric row pairs, the required
bitset, an anchor-index set, and the live root columns in a chosen order.
The universal checks on inc/must involve only small, topology-free masks. -/
theorem impossible {W X : Type} [DecidableEq W] {ev : W → X → Bool} {S T : Finset W}
    (B : Blocks ev S T) (lo hi : Row → X) (mark : W → Mark)
    (pos : ∀ w i, bit (mark w).1 i=ev w (hi i))
    (neg : ∀ w i, bit (mark w).2 i=ev w (lo i))
    (ord : ∀ i w, w∈S → ev w (lo i)=true → ev w (hi i)=true)
    (det : ∀ i, ∃ w∈T, ev w (lo i)≠ev w (hi i))
    {n : Nat} (e : Fin n ≃ ↥S) (core : Finset (Fin n)) (many : T.card<core.card)
    (inc : Fin n → BitVec (2^n))
    (digits : ∀ i (j : Fin (2^n)), (inc i).getLsbD j.val=j.val.testBit i.val)
    (must : BitVec (2^n)) (need : ∀ j : Fin (2^n),
      (members j).card+(T.card-1)≤S.card → 2≤((members j)∩core).card →
      must.getLsbD j.val=true)
    (pairs : List (Row×Row)) (verified : must &&& cover
      (List.ofFn (fun i : Fin n => (⟨mark (e i).val,inc i⟩ : Col (2^n)))) pairs=must) :
    False := by
  classical
  let value := fun i : Fin n => (e i).val
  have inj : Function.Injective value := fun _ _ h => e.injective (Subtype.ext h)
  let A := core.image value
  have sub : A⊆S := by
    intro w mw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp mw
    exact (e i).property
  have cA : A.card=core.card := Finset.card_image_of_injective _ inj
  obtain ⟨t,mt,a,ma,b,mb,ab,oa,ob,sz⟩ :=
    CoSevenAnchors4482.anchored_block B A sub (by omega)
  let block := S.filter (fun w => B.owner w=t)
  let pred := fun i : Fin n => decide (B.owner (value i)=t)
  let j := pack pred
  have digit (i : Fin n) : j.val.testBit i.val=decide (B.owner (value i)=t) := pack_bit pred i
  have mem (i : Fin n) : i∈members j ↔ B.owner (value i)=t := by
    simp [members,digit]
  let embed : ↥(members j) → ↥block := fun z =>
    ⟨value z.val,Finset.mem_filter.mpr ⟨(e z.val).property,(mem _).mp z.property⟩⟩
  have inj2 : Function.Injective embed := by
    intro x y eq
    apply Subtype.ext
    apply inj
    exact congrArg Subtype.val eq
  have small : (members j).card≤block.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective embed inj2
  have sm : (members j).card+(T.card-1)≤S.card := by
    change block.card+(T.card-1)≤S.card at sz
    omega
  obtain ⟨i,mi,ia⟩ := Finset.mem_image.mp ma
  obtain ⟨h,mh,hb⟩ := Finset.mem_image.mp mb
  have it : i∈members j := (mem i).mpr (by rw [ia]; exact oa)
  have ht : h∈members j := (mem h).mpr (by rw [hb]; exact ob)
  have enough : 1<((members j)∩core).card := Finset.one_lt_card.mpr
    ⟨i,Finset.mem_inter.mpr ⟨it,mi⟩,h,Finset.mem_inter.mpr ⟨ht,mh⟩,
      fun eq => ab (ia.symm.trans ((congrArg value eq).trans hb))⟩
  obtain ⟨r,s,hit⟩ := required_witness _ pairs must verified j (need j sm enough)
  let col (l : Fin n) := (⟨mark (value l), inc l⟩ : Col (2^n))
  have found (w : W) (mw : w∈S) : ∃ l : Fin n, value l=w ∧ col l∈List.ofFn col := by
    let l := e.symm ⟨w,mw⟩
    refine ⟨l,?_,List.mem_ofFn.mpr ⟨l,rfl⟩⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨w,mw⟩)
  apply CoBlockPhysical4482.no_pair B lo hi mark pos neg ord det mt r s
  · intro w mw offt
    obtain ⟨l,lw,ml⟩ := found w mw
    have sign : (inc l).getLsbD j.val=false := by rw [digits,digit,lw]; exact decide_eq_false offt
    have z := (hit (col l) ml).1 sign
    change bit (mark (value l)).1 r=bit (mark (value l)).2 r ∧
      bit (mark (value l)).1 s=bit (mark (value l)).2 s at z
    simpa only [lw] using z
  · intro w mw ont
    obtain ⟨l,lw,ml⟩ := found w mw
    have sign : (inc l).getLsbD j.val=true := by rw [digits,digit,lw]; exact decide_eq_true ont
    have z := (hit (col l) ml).2 sign
    change bit (mark (value l)).1 r=true → bit (mark (value l)).2 s=true at z
    simpa only [lw] using z

#print axioms impossible
end CoBlockSlots4482
