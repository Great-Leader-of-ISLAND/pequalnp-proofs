import PEqualNP.CoJunctionLeaf4482
import PEqualNP.CoJunctionFixedModel4482
namespace CoJunctionFastLeaf4482
open CoPortRoots4482 CoPortFrontier4482 CoPortTrace4482 CoPortCut4482
open CoBitBlock4482 CoBlockIntervals4482 CoBlockSlots4482
open CoJunctionWire4482 CoJunctionTree4482

def axis {n : Nat} (i : Fin n) : BitVec (2^n) :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin (2^n) => j.val.testBit i.val))).cast List.length_ofFn

theorem digit {n : Nat} (i : Fin n) (j : Fin (2^n)) :
    (axis i).getLsbD j.val=j.val.testBit i.val := by
  simp only [axis,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn]
  simp [j.isLt]

def ids (n : Nat) := (List.ofFn (fun i : Fin n => i)).dedup
def anchors (n mask : Nat) := (ids n).filter (fun i => mask.testBit i.val)
def valAt (xs : List Wire) (i : Fin xs.length) := value (xs.get i)
def markAt (xs : List Wire) (i : Fin xs.length) := (eval (xs.get i)).projected

theorem real_set (xs : List Wire) : (List.ofFn (valAt xs)).toFinset = (values xs).toFinset := by
  ext z
  simp only [List.mem_toFinset,List.mem_ofFn,values,List.mem_map]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨xs.get i,List.get_mem _ _,hi⟩
  · rintro ⟨w,hw,hv⟩
    obtain ⟨i,eq⟩ := List.mem_iff_get.mp hw
    exact ⟨i,(congrArg value eq).trans hv⟩

private def key (xs : List Wire) (j : Nat) : Nat :=
  if h : j < xs.length then (valAt xs ⟨j,h⟩).toNat else 0

private def rising (xs : List Wire) :=
  (List.range (xs.length-1)).all (fun j => decide (key xs j < key xs (j+1)))

private theorem increasing {xs : List Wire} (ok : rising xs = true)
    {a b : Nat} (lt : a < b) (bound : b < xs.length) : key xs a < key xs b := by
  induction b with
  | zero => omega
  | succ b ih =>
    have member : b ∈ List.range (xs.length-1) := List.mem_range.mpr (by omega)
    have edge : key xs b < key xs (b+1) :=
      of_decide_eq_true (List.all_eq_true.mp ok b member)
    by_cases last : a=b
    · simpa only [last] using edge
    · exact lt_trans (ih (by omega) (by omega)) edge

private theorem rising_injective {xs : List Wire} (ok : rising xs = true) :
    Function.Injective (valAt xs) := by
  intro i j same
  have sameKey : key xs i.val = key xs j.val := by
    simpa only [key,dif_pos i.isLt,dif_pos j.isLt] using
      (congrArg (fun w : W => w.toNat) same)
  rcases lt_trichotomy i.val j.val with lt|eq|gt
  · exact ((ne_of_lt (increasing ok lt j.isLt)) sameKey).elim
  · exact Fin.ext eq
  · exact ((ne_of_lt (increasing ok gt i.isLt)) sameKey.symm).elim

private def distinctValues (xs : List Wire) :=
  rising xs || decide (∀ i j, valAt xs i=valAt xs j → i=j)

private theorem distinct_correct (xs : List Wire) : distinctValues xs=true ↔
    ∀ i j, valAt xs i=valAt xs j → i=j := by
  constructor
  · intro ok i j eq
    rcases Bool.or_eq_true.mp ok with sorted|slow
    · exact rising_injective sorted eq
    · exact (of_decide_eq_true slow) i j eq
  · intro h
    exact Bool.or_eq_true.mpr (Or.inr (decide_eq_true h))

def checkWith (xs : List Wire) (k mask fuel : Nat) (inc : Fin xs.length→BitVec (2^xs.length))
    (must : BitVec (2^xs.length)) : Bool :=
  let n := xs.length
  (decide (n=6+k ∧ 6<(anchors n mask).toFinset.card) && distinctValues xs) &&
    CoImplicitBlock4482.check (List.ofFn (fun i => (⟨markAt xs i,inc i⟩ : Col (2^n)))) fuel must

/-- For a standalone leaf, the only hint is its seven-position anchor mask
and its recursion depth. This fallback has precisely the original physical
column order and requires no externally supplied wire marks. -/
def check (xs : List Wire) (k mask fuel : Nat) :=
  checkWith xs k mask fuel axis (CoGlobalShape4482.required (ids xs.length) (anchors xs.length mask) axis)

theorem checkWith_sound {xs : List Wire} {k mask fuel : Nat}
    {inc : Fin xs.length→BitVec (2^xs.length)} {must : BitVec (2^xs.length)}
    (digits : ∀ i (j : Fin (2^xs.length)),(inc i).getLsbD j.val=j.val.testBit i.val)
    (needed : ∀ j : Fin (2^xs.length), (members j).card+5≤xs.length →
      2≤((members j)∩(anchors xs.length mask).toFinset).card → must.getLsbD j.val=true)
    (ok : checkWith xs k mask fuel inc must=true) :
    (values xs).toFinset.card=6+k ∧ ¬Path join (cleanCut model label 6) k (values xs).toFinset := by
  obtain ⟨data,cert⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨bounds,disjoint⟩ := Bool.and_eq_true_iff.mp data
  obtain ⟨size,core⟩ := of_decide_eq_true bounds
  have inj := (distinct_correct xs).mp disjoint
  let S := (List.ofFn (valAt xs)).toFinset
  let e := CoJunctionLeaf4482.slots (valAt xs) inj
  have card : S.card=xs.length := by
    calc S.card = Fintype.card (↥S) := (Fintype.card_coe S).symm
         _ = Fintype.card (Fin xs.length) := (Fintype.card_congr e).symm
         _ = xs.length := Fintype.card_fin _
  have order : ∀ w∈S,CoPortEdgeRows4482.Ordered w := by
    intro w hw
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hw)
    exact eq ▸ (eval (xs.get i)).ordered
  have stop := CoActualTight4482.implicit_excludes (S:=S) (k:=k) (card.trans size) order e
    (markAt xs) (fun i => (eval (xs.get i)).correct) (anchors xs.length mask).toFinset core
    inc digits must (fun j small many => needed j (by rwa [card] at small) many) fuel cert
  rw [←real_set]
  exact ⟨card.trans size,stop⟩

theorem check_sound {xs : List Wire} {k mask fuel : Nat} (good : check xs k mask fuel=true) :
    (values xs).toFinset.card=6+k ∧ ¬Path join (cleanCut model label 6) k (values xs).toFinset := by
  apply checkWith_sound (fun i j => digit i j) _ good
  intro j small many
  apply CoGlobalShape4482.required_at _ _ _ _ _ (fun i q => digit i q) j small many
  · exact List.nodup_dedup _
  · intro i
    apply List.mem_dedup.mpr
    exact List.mem_ofFn.mpr ⟨i,rfl⟩

#print axioms checkWith_sound
#print axioms check_sound
end CoJunctionFastLeaf4482
