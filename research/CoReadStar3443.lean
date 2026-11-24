import PEqualNP.CoStarFamily3443

namespace CoReadStar3443
open PEqualNP.CircuitLowerBounds PEqualNP.ReadK CoStarFamily3443

abbrev Counts := List (List Nat)
abbrev Wires := List Counts

def start (n leaf : Nat) : Wires := (List.range n).map (leafVectors [0,leaf] 1)

def push (leaf : Nat) (w : Wires) (g : Gate) : Wires :=
  let ins := g.inputs.map fun i => w.getD i []
  w ++ [match g.op with
        | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
        | .and => ins.foldl (andStep 1) [[0,0]]
        | _ => []]

def prefixW (n leaf k : Nat) : Wires := (chain n k).foldl (push leaf) (start n leaf)

theorem raw (n i leaf : Nat) (hi : i<n) : (start n leaf).getD i [] = leafVectors [0,leaf] 1 i := by
  simp [start,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,hi]

theorem leaf_value (i leaf : Nat) (pos : 0<i) :
    leafVectors [0,leaf] 1 i = if i=leaf then [[0,1]] else [] := by
  by_cases e : i=leaf
  · subst i
    simp [leafVectors,Nat.ne_of_gt pos,Ne.symm (Nat.ne_of_gt pos)]
  · simp [leafVectors,Nat.ne_of_gt pos,Ne.symm (Nat.ne_of_gt pos),e,Ne.symm e]

private theorem old (w : Wires) (z : Counts) {i : Nat} (h : i<w.length) :
    (w++[z]).getD i []=w.getD i [] := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h]

private theorem last (w : Wires) (z : Counts) : (w++[z]).getD w.length []=z := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_right]

theorem prefix_facts (n leaf k : Nat) (positive : 0<leaf) (within : k+1<n) :
    (prefixW n leaf k).length=n+k ∧
    (∀ i<n,(prefixW n leaf k).getD i []=leafVectors [0,leaf] 1 i) ∧
    (prefixW n leaf k).getD (tip n k) [] =
      (if leaf≤k+1 then [[0,1]] else []) := by
  induction k with
  | zero =>
    refine ⟨by simp [prefixW,chain,start],fun i hi => raw _ _ _ hi,?_⟩
    change (start n leaf).getD 1 [] = _
    rw [raw _ _ _ within,leaf_value _ _ (by decide)]
    by_cases eq : leaf=1
    · simp [eq]
    · have gt : ¬leaf≤1 := by omega
      simp [gt,Ne.symm eq]
  | succ k ih =>
    obtain ⟨len,orig,prev⟩ := ih (by omega)
    let w := prefixW n leaf k
    let z : Counts := if leaf≤k+2 then [[0,1]] else []
    have nxt : prefixW n leaf (k+1)=w++[z] := by
      change (chain n (k+1)).foldl (push leaf) (start n leaf)=w++[z]
      rw [chain,List.foldl_append]
      change push leaf w ⟨.or,[tip n k,k+2]⟩=w++[z]
      have tipval : w.getD (tip n k) [] = _ := prev
      have rawval : w.getD (k+2) [] = _ := orig (k+2) (by omega)
      simp only [push,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,
        tipval,rawval,leaf_value _ _ (by omega)]
      by_cases early : leaf≤k+1
      · have hit : leaf≤k+2 := by omega
        have miss : k+2≠leaf := by omega
        simp [early,hit,miss,z,insertNew]
      · by_cases hit : k+2=leaf
        · simp [early,hit,z,insertNew]
        · have big : ¬leaf≤k+2 := by omega
          simp [early,big,hit,z,insertNew]
    rw [nxt]
    have hw : w.length=n+k := len
    refine ⟨by simp [hw,Nat.add_assoc],?_,?_⟩
    · intro i hi
      rw [old _ _ (by omega)]
      exact orig i hi
    · change (w++[z]).getD (n+k) []=z
      rw [← hw,last]

private theorem oldMany (w more : Wires) (i : Nat) (h : i<w.length) :
    (w++more).getD i []=w.getD i [] := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h]

private theorem newWire (w more : Wires) (i : Nat) :
    (w++more).getD (w.length+i) []=more.getD i [] := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_add_right w.length i)]
  simp

def both (a b : Counts) : Counts := andStep 1 (andStep 1 [[0,0]] a) b
def either (a b : Counts) : Counts := b.foldl insertNew (a.foldl insertNew [])

private theorem and_read (leaf : Nat) (w : Wires) (x y : Nat) :
    push leaf w ⟨.and,[x,y]⟩=w++[both (w.getD x []) (w.getD y [])] := rfl

private theorem or_read (leaf : Nat) (w : Wires) (x y : Nat) :
    push leaf w ⟨.or,[x,y]⟩=w++[either (w.getD x []) (w.getD y [])] := rfl

theorem tail_vectors (w : Wires) (pool leaf mark : Nat) (hp : pool<w.length) :
    (suffix w.length pool mark).foldl (push leaf) w =
      let y := both (w.getD pool []) (w.getD mark [])
      let a := both (w.getD 0 []) y
      let f := both (w.getD 0 []) (w.getD pool [])
      w++[y,a,f,either a f] := by
  let y := both (w.getD pool []) (w.getD mark [])
  let a := both (w.getD 0 []) y
  let f := both (w.getD 0 []) (w.getD pool [])
  have hz : 0<w.length := by omega
  have h₁ : push leaf w ⟨.and,[pool,mark]⟩=w++[y] := and_read _ _ _ _
  have h₂ : push leaf (w++[y]) ⟨.and,[0,w.length]⟩=w++[y,a] := by
    rw [and_read,oldMany _ _ _ hz,last]
    simp [a,List.append_assoc]
  have h₃ : push leaf (w++[y,a]) ⟨.and,[0,pool]⟩=w++[y,a,f] := by
    rw [and_read,oldMany _ _ _ hz,oldMany _ _ _ hp]
    simp [f,List.append_assoc]
  have h₄ : push leaf (w++[y,a,f]) ⟨.or,[w.length+1,w.length+2]⟩=w++[y,a,f,either a f] := by
    rw [or_read,newWire,newWire]
    simp [List.append_assoc,List.getD]
  change push leaf (push leaf (push leaf (push leaf w _) _) _) _ = _
  rw [h₁,h₂,h₃,h₄]

end CoReadStar3443
