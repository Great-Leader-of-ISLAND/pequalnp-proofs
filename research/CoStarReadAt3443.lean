import Mathlib.Combinatorics.SimpleGraph.Star
import PEqualNP.CoReadStar3443
import PEqualNP.CoStarLegal3443

namespace CoStarReadAt3443
open PEqualNP.CircuitLowerBounds PEqualNP.ReadK PEqualNP.Core
open CoStarFamily3443 CoReadStar3443

private def pair (sw : Bool) (leaf : ℕ) := if sw then [leaf,0] else [0,leaf]
private def unitLeaf (sw : Bool) : Counts := if sw then [[1,0]] else [[0,1]]
private def unitCenter (sw : Bool) : Counts := if sw then [[0,1]] else [[1,0]]
private def doubleLeaf (sw : Bool) : Counts := if sw then [[2,1]] else [[1,2]]
private def initial (sw : Bool) (n leaf : ℕ) : Wires := (List.range n).map (leafVectors (pair sw leaf) 1)
private def pre (sw : Bool) (n leaf k : ℕ) : Wires := (chain n k).foldl (push leaf) (initial sw n leaf)

private theorem leaf_pin (sw : Bool) (leaf i : ℕ) (h : 0 < i) :
    leafVectors (pair sw leaf) 1 i=(if i=leaf then unitLeaf sw else []) := by
  cases sw
  · exact leaf_value _ _ h
  · by_cases e : i=leaf
    · subst i
      simp [pair,leafVectors,unitLeaf,Nat.ne_of_gt h,Ne.symm (Nat.ne_of_gt h)]
    · simp [pair,leafVectors,unitLeaf,Nat.ne_of_gt h,Ne.symm (Nat.ne_of_gt h),e,Ne.symm e]

private theorem center_pin (sw : Bool) (leaf : ℕ) (h : 0<leaf) :
    leafVectors (pair sw leaf) 1 0=unitCenter sw := by
  cases sw <;> simp [pair,leafVectors,unitCenter,Nat.ne_of_gt h,Ne.symm (Nat.ne_of_gt h)]

private theorem oldWire (w more : Wires) (i : ℕ) (hi : i<w.length) :
    (w++more).getD i []=w.getD i [] := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

private theorem newWire (w more : Wires) (i : ℕ) :
    (w++more).getD (w.length+i) []=more.getD i [] := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_add_right w.length i)]
  simp

private theorem pre_facts (sw : Bool) (n leaf k : ℕ) (positive : 0<leaf) (within : k+1<n) :
    (pre sw n leaf k).length=n+k ∧
    (∀i<n,(pre sw n leaf k).getD i []=leafVectors (pair sw leaf) 1 i) ∧
    (pre sw n leaf k).getD (tip n k) []=(if leaf≤k+1 then unitLeaf sw else []) := by
  cases sw with
  | false => exact prefix_facts n leaf k positive within
  | true =>
    induction k with
    | zero =>
      have orig (i) (hi : i<n) : (initial true n leaf).getD i [] = leafVectors (pair true leaf) 1 i := by
        simp [initial,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,hi]
      refine ⟨by simp [pre,chain,initial],orig,?_⟩
      change (initial true n leaf).getD 1 []=_
      rw [orig 1 within,leaf_pin _ _ _ (by decide)]
      by_cases eq : leaf=1
      · simp [eq]
      · have large : ¬leaf≤1 := by omega
        simp [large,Ne.symm eq]
    | succ k ih =>
      obtain ⟨len,orig,prev⟩ := ih (by omega)
      let w := pre true n leaf k
      let z : Counts := if leaf≤k+2 then [[1,0]] else []
      have nxt : pre true n leaf (k+1)=w++[z] := by
        change (chain n (k+1)).foldl (push leaf) (initial true n leaf)=w++[z]
        rw [chain,List.foldl_append]
        change push leaf w ⟨.or,[tip n k,k+2]⟩=w++[z]
        have tipval : w.getD (tip n k) [] = _ := prev
        have rawval : w.getD (k+2) [] = _ := orig (k+2) (by omega)
        simp only [push,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,
          tipval,rawval,leaf_pin true leaf (k+2) (by omega)]
        by_cases early : leaf≤k+1
        · have hit : leaf≤k+2 := by omega
          have miss : k+2≠leaf := by omega
          simp [early,hit,miss,z,unitLeaf,insertNew]
        · by_cases hit : k+2=leaf
          · simp [early,hit,z,unitLeaf,insertNew]
          · have big : ¬leaf≤k+2 := by omega
            simp [early,big,hit,z,unitLeaf,insertNew]
      rw [nxt]
      have hw : w.length=n+k := len
      refine ⟨by simp [hw,Nat.add_assoc],?_,?_⟩
      · intro i hi
        rw [oldWire _ _ _ (by omega)]
        exact orig i hi
      · change (w++[z]).getD (n+k) []=z
        rw [←hw]
        simp [List.getD_eq_getElem?_getD,List.getElem?_append_right]

private theorem vectors_at (q leaf : ℕ) (hq : 1≤q) (pos : 0<leaf) (bound : leaf≤q) (sw : Bool) :
    let C := circuit q 1
    let n := q+1
    let source := readVectors C n (pair sw leaf) 1
    source.getD (n+q) []=(if leaf=1 then doubleLeaf sw else []) ∧
    source.getD (n+(q+1)) []=[[1,1]] := by
  let n := q+1
  let k := q-1
  let w := pre sw n leaf k
  have hk : k+1=q := by dsimp [k]; omega
  have sz : k+1<n := by dsimp [n]; omega
  obtain ⟨len,rawPins,pool⟩ := pre_facts sw n leaf k pos sz
  change w.length=n+k at len
  have top : w.getD (tip n k) []=unitLeaf sw := by
    rw [if_pos (by omega : leaf≤k+1)] at pool
    exact pool
  have zero : w.getD 0 []=unitCenter sw := (rawPins 0 (by dsimp [n]; omega)).trans (center_pin sw leaf pos)
  have one : w.getD 1 []=(if 1=leaf then unitLeaf sw else []) :=
    (rawPins 1 (by dsimp [n]; omega)).trans (leaf_pin sw leaf 1 (by decide))
  have tp : tip n k<w.length := by rw [len]; exact CoStarLegal3443.tip_before (by dsimp [n]; omega) k
  let mixed := both (unitLeaf sw) (if 1=leaf then unitLeaf sw else [])
  let a := both (unitCenter sw) mixed
  let b := both (unitCenter sw) (unitLeaf sw)
  have entire : readVectors (circuit q 1) n (pair sw leaf) 1=w++[mixed,a,b,either a b] := by
    have eq : readVectors (circuit q 1) n (pair sw leaf) 1=(suffix (n+k) (tip n k) 1).foldl (push leaf) w := by
      cases sw <;> change (chain n k ++ suffix (n+k) (tip n k) 1).foldl _ _=_
        <;> rw [List.foldl_append] <;> rfl
    rw [eq,←len,tail_vectors w _ leaf 1 tp]
    simpa only [top,one,zero,mixed,a,b]
  change (readVectors (circuit q 1) n (pair sw leaf) 1).getD (n+q) []=_ ∧
    (readVectors (circuit q 1) n (pair sw leaf) 1).getD (n+(q+1)) []=_
  rw [entire,show n+q=w.length+1 by omega,show n+(q+1)=w.length+2 by omega,newWire,newWire]
  change a=_ ∧ b=_
  by_cases hit : leaf=1
  · simp only [a,b,mixed,if_pos hit,if_pos hit.symm]
    cases sw <;> decide
  · have rev : ¬1=leaf := Ne.symm hit
    simp only [a,b,mixed,if_neg hit,if_neg rev]
    cases sw <;> decide

/-- A's two endpoint multiplicities are (1,2) on edge 01. -/
theorem repeated (q : ℕ) (hq : 4≤q) :
    ReadTwiceAt (q+1) (circuit q 1) q (0 : Fin (q+1)) ⟨1,by omega⟩ := by
  have a := (vectors_at q 1 (by omega) (by decide) (by omega) false).1
  change ((readVectors (circuit q 1) (q+1) (pair false 1) 1).getD ((q+1)+q) []).any _=false
  rw [a]
  rfl

/-- The full center-and-pool gate is READ-1 on every star edge, in either order. -/
theorem full_once (q : ℕ) (hq : 4≤q) (u v : Fin (q+1)) (edge : (SimpleGraph.starGraph (0 : Fin (q+1))).Adj u v) :
    readsAtMost (atGate (q+1) (circuit q 1) (q+1)) (q+1) [u.val,v.val] 1=true := by
  obtain ⟨ne,atCenter⟩ := SimpleGraph.starGraph_adj.mp edge
  rcases atCenter with rfl|rfl
  · have pos : 0<v.val := Nat.pos_of_ne_zero (fun eq => ne (Fin.ext (by simpa using eq.symm)))
    have b := (vectors_at q v.val (by omega) pos (by omega) false).2
    change ((readVectors (circuit q 1) (q+1) (pair false v.val) 1).getD ((q+1)+(q+1)) []).any _=true
    rw [b]
    rfl
  · have pos : 0<u.val := Nat.pos_of_ne_zero (fun eq => ne (Fin.ext (by simpa using eq)))
    have b := (vectors_at q u.val (by omega) pos (by omega) true).2
    change ((readVectors (circuit q 1) (q+1) (pair true u.val) 1).getD ((q+1)+(q+1)) []).any _=true
    rw [b]
    rfl

theorem full_not_repeated (q : ℕ) (hq : 4≤q) (u v : Fin (q+1))
    (edge : (SimpleGraph.starGraph (0 : Fin (q+1))).Adj u v) :
    ¬ReadTwiceAt (q+1) (circuit q 1) (q+1) u v := by
  change ¬readsAtMost _ _ _ _=false
  rw [full_once q hq u v edge]
  decide

#print axioms CoStarReadAt3443.repeated
#print axioms CoStarReadAt3443.full_once
#print axioms CoStarReadAt3443.full_not_repeated
end CoStarReadAt3443
