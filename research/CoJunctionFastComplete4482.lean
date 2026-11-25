import PEqualNP.CoJunctionActual4482
import PEqualNP.CoJunctionFastGrids4482
import PEqualNP.CoJunctionTarget4482
namespace CoJunctionFastComplete4482
open CoPortRoots4482 CoPortFrontier4482 CoJunctionLogical4482 CoJunctionFixed4482
open CoJunctionActual4482 CoJunctionTarget4482

/-- Small untrusted hints are read from the original tight leaf numbering.
Higher six-bit chunks encode the seven anchors, lower bits encode the exact
interval recursion budget. All truth values are recomputed from the root. -/
def rowCheck (h : Graph) [NeZero h.size] (hints : Column) (seeded : Bool) (depth : Nat)
    (i : Fin h.size) : Bool :=
  let r := recordAt h seeded depth i
  let xs := CoJunctionFixedModel4482.build h seeded depth i.val
  let leaf := leafCode h i.val
  let cue := field hints (leaf-1)
  if leaf=0 then decide (6<(stateWords r).toFinset.card) && internal h seeded depth i
  else decide (0<r.budget) && CoJunctionFastGrids4482.checked xs r.budget (cue/64) (cue%64)

private theorem facts {h : Graph} [NeZero h.size] {hints : Column} {seeded : Bool}
    {depth : Nat} {i : Fin h.size} (good : rowCheck h hints seeded depth i=true) :
    let r := recordAt h seeded depth i
    (6 < (stateWords r).toFinset.card) ∧
      (((stateWords r).toFinset.card=6+r.budget ∧
         ¬CoPortTrace4482.Path join (CoPortCut4482.cleanCut model label 6) r.budget
           (stateWords r).toFinset) ∨ Routed (recordAt h seeded depth) r) := by
  dsimp only
  by_cases stop : leafCode h i.val = 0
  · simp only [rowCheck,if_pos stop] at good
    obtain ⟨wide,routed⟩ := Bool.and_eq_true_iff.mp good
    exact ⟨of_decide_eq_true wide,Or.inr (internal_sound routed)⟩
  · simp only [rowCheck,if_neg stop] at good
    obtain ⟨positive,checked⟩ := Bool.and_eq_true_iff.mp good
    have leaf := CoJunctionFastGrids4482.sound checked
    have exactLeaf :
        (stateWords (recordAt h seeded depth i)).toFinset.card=6+(recordAt h seeded depth i).budget ∧
        ¬CoPortTrace4482.Path join (CoPortCut4482.cleanCut model label 6)
          (recordAt h seeded depth i).budget (stateWords (recordAt h seeded depth i)).toFinset := by
      change (words (CoJunctionFixedModel4482.data _)).toFinset.card = _ ∧
        ¬CoPortTrace4482.Path join (CoPortCut4482.cleanCut model label 6) _
          (words (CoJunctionFixedModel4482.data _)).toFinset
      simpa only [CoJunctionFixedModel4482.data_values] using leaf
    have pos : 0 < (recordAt h seeded depth i).budget := of_decide_eq_true positive
    exact ⟨by rw [exactLeaf.1]; omega, Or.inl exactLeaf⟩

def certified {h : Graph} [NeZero h.size] {hints : Column} {seeded : Bool} {depth : Nat}
    (cap : 7≤budget h 0)
    (all : ∀ i : Fin h.size,rowCheck h hints seeded depth i=true) :
    Certificate (Fin h.size) (if seeded then init.toFinset else raws.toFinset) where
  table := recordAt h seeded depth
  root := 0
  ceiling := cap
  starting := CoJunctionFixedModel4482.root_values h seeded depth
  authenticAt := fun i => CoJunctionFixedModel4482.table_real h seeded depth i.val
  above := fun i => (facts (all i)).1
  classified := fun i => (facts (all i)).2

def slice {n : Nat} (test : Fin n→Bool) (start count : Nat) :=
  (List.range count).all (fun d => if h : start+d<n then test ⟨start+d,h⟩ else true)

def Holds {n : Nat} (test : Fin n→Bool) (lo hi : Nat) : Prop :=
  ∀ i : Fin n, (lo ≤ i.val) → (i.val < hi) → test i = true

theorem slice_sound {n a k : Nat} {f : Fin n→Bool} (ok : slice f a k=true) :
    Holds f a (a+k) := by
  intro i lo hi
  have lt : i.val-a<k := by omega
  have eq : a+(i.val-a)=i.val := by omega
  have h := List.all_eq_true.mp ok (i.val-a) (List.mem_range.mpr lt)
  have hn : a + (i.val-a) < n := by simpa only [eq] using i.isLt
  have point : (⟨a+(i.val-a),hn⟩ : Fin n) = i := Fin.ext eq
  simpa only [dif_pos hn,point] using h

theorem join_blocks {n a b c : Nat} {f : Fin n→Bool}
    (left : Holds f a b) (right : Holds f b c) : Holds f a c := by
  intro i lo hi
  by_cases before : i.val<b
  · exact left i lo before
  · exact right i (by omega) hi

theorem all_rows {n : Nat} {f : Fin n→Bool} (j : Holds f 0 n) (i : Fin n) : f i=true :=
  j i (Nat.zero_le _) i.isLt

#print axioms certified
#print axioms slice_sound
end CoJunctionFastComplete4482
