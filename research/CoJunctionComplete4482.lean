import PEqualNP.CoJunctionActual4482
import PEqualNP.CoJunctionGrids4482
import PEqualNP.CoJunctionTarget4482
namespace CoJunctionComplete4482
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
  decide (6<(stateWords r).toFinset.card) &&
    if leaf=0 then internal h seeded depth i
    else CoJunctionGrids4482.checked xs r.budget (cue/64) (cue%64)

def certified {h : Graph} [NeZero h.size] {hints : Column} {seeded : Bool} {depth : Nat}
    (cap : 7≤budget h 0)
    (all : ∀ i : Fin h.size,rowCheck h hints seeded depth i=true) :
    Certificate (Fin h.size) (if seeded then init.toFinset else raws.toFinset) where
  table := recordAt h seeded depth
  root := 0
  ceiling := cap
  starting := CoJunctionFixedModel4482.root_values h seeded depth
  authenticAt := fun i => CoJunctionFixedModel4482.table_real h seeded depth i.val
  above := fun i => of_decide_eq_true (Bool.and_eq_true_iff.mp (all i)).1
  classified := by
    intro i
    have localCheck := (Bool.and_eq_true_iff.mp (all i)).2
    by_cases stop : leafCode h i.val=0
    · exact Or.inr (internal_sound (by simpa only [if_pos stop] using localCheck))
    · have leaf := CoJunctionGrids4482.sound (by
        simpa only [if_neg stop] using localCheck)
      apply Or.inl
      change (words (CoJunctionFixedModel4482.data _)).toFinset.card = _ ∧
        ¬CoPortTrace4482.Path join (CoPortCut4482.cleanCut model label 6) _
          (words (CoJunctionFixedModel4482.data _)).toFinset
      simpa only [CoJunctionFixedModel4482.data_values] using leaf

def slice {n : Nat} (test : Fin n→Bool) (start count : Nat) :=
  (List.range count).all (fun d => if h : start+d<n then test ⟨start+d,h⟩ else true)

def Holds {n : Nat} (test : Fin n→Bool) (lo hi : Nat) :=
  ∀ i : Fin n, lo≤i.val → i.val<hi → test i=true

theorem slice_sound {n a k : Nat} {f : Fin n→Bool} (ok : slice f a k=true) :
    Holds f a (a+k) := by
  intro i lo hi
  have lt : i.val-a<k := by omega
  have eq : a+(i.val-a)=i.val := by omega
  have h := List.all_eq_true.mp ok (i.val-a) (List.mem_range.mpr lt)
  simpa only [eq,i.isLt,dif_pos] using h

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
end CoJunctionComplete4482
