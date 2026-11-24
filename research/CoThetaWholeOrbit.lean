import PEqualNP.CoThetaWholeBase

namespace CoThetaWholeBase
open PEqualNP.CircuitLowerBounds
/-- Relabel only the seven raw inputs. The supplied inverter keeps index 7,
    and every tail gate and invalid external index keeps its original index. -/
def renamePin (f : Fin 7 → Fin 7) (k : Nat) := if h : k < 7 then (f ⟨k,h⟩).val else k

def renameGate (f : Fin 7 → Fin 7) (g : Gate) : Gate := ⟨g.op,g.inputs.map (renamePin f)⟩

def relabeled (f : Fin 7 → Fin 7) (c : Circuit) : Circuit :=
  ⟨c.gates.map (renameGate f),renamePin f c.output⟩

private def rowRun (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun a => v.getD a false)]) w

private lemma rename_run (f : Fin 7 → Fin 7) (gs : List Gate) (v w : List Bool)
    (h7 : 7 ≤ v.length) (hl : v.length = w.length)
    (hv : ∀ k, w.getD (renamePin f k) false = v.getD k false) (k : Nat) :
    (rowRun (gs.map (renameGate f)) w).getD (renamePin f k) false = (rowRun gs v).getD k false := by
  induction gs generalizing v w with
  | nil => exact hv k
  | cons g gs ih =>
    have hgate : (renameGate f g).op.eval ((renameGate f g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      change g.op.eval ((g.inputs.map (renamePin f)).map fun i => w.getD i false) = _
      rw [List.map_map]
      exact congrArg (fun p : Nat → Bool => g.op.eval (g.inputs.map p)) (funext hv)
    change (rowRun (gs.map (renameGate f)) (w ++ [_])).getD _ false = (rowRun gs (v ++ [_])).getD _ false
    rw [hgate]
    apply ih (v ++ [_]) (w ++ [_]) (by simp; omega) (by simp [hl])
    intro i
    by_cases hi : i < v.length
    · have hr : renamePin f i < w.length := by
        unfold renamePin; split
        · have h := (f ⟨i,by assumption⟩).isLt; omega
        · omega
      rw [List.getD_append _ _ _ _ hr,List.getD_append _ _ _ _ hi,hv]
    · have hp : ¬i<7 := by omega
      simp only [renamePin,dif_neg hp,List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega : w.length ≤ i),
        List.getElem?_append_right (by omega : v.length ≤ i), hl]

private lemma read_ofFn {n : Nat} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD,i.isLt]

private lemma initial_rename (f : Fin 7 → Fin 7) (j : Fin 7) (x : Fin 7 → Bool) (k : Nat) :
    (List.ofFn x ++ [!(x (f j))]).getD (renamePin f k) false =
    (List.ofFn (fun i => x (f i)) ++ [!(x (f j))]).getD k false := by
  by_cases h : k<7
  · simp only [renamePin,dif_pos h]
    rw [List.getD_append _ _ _ _ (by simpa using (f ⟨k,h⟩).isLt),
      List.getD_append _ _ _ _ (by simpa using h)]
    exact (read_ofFn x (f ⟨k,h⟩)).trans (read_ofFn (fun i => x (f i)) ⟨k,h⟩).symm
  · simp only [renamePin,dif_neg h,List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h),
      List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)]
    simp

def reverseEnds : Fin 7 → Fin 7 := ![1,0,2,4,3,6,5]
def swapLongPaths : Fin 7 → Fin 7 := ![0,1,2,5,6,3,4]
def toRepresentative : Fin 7 → Fin 7 → Fin 7 :=
  ![id,reverseEnds,id,id,reverseEnds,swapLongPaths,reverseEnds ∘ swapLongPaths]

def orbitHead : Fin 7 → Fin 7 := ![0,0,2,3,3,3,3]

private lemma rep_head : ∀ j : Fin 7, toRepresentative j j = orbitHead j := by decide +kernel
private lemma rep_target (j : Fin 7) (x : Fin 7 → Bool) : theta (fun i => x (toRepresentative j i)) = theta x := by
  have table : ∀ (j : Fin 7) (a b c d e f g : Bool),
      let y : Fin 7 → Bool := ![a,b,c,d,e,f,g]
      theta (fun i => y (toRepresentative j i)) = theta y := by decide +kernel
  have hx : x = ![x 0,x 1,x 2,x 3,x 4,x 5,x 6] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  exact table j (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

/-- One certificate per orbit suffices for every physical choice of input. -/
/- A witness-free tail of size at most ten, with one supplied complemented variable. -/
def NoSignedTail (j : Fin 7) : Prop := ∀ c : Circuit, c.size ≤ 10 →
  PEqualNP.MetaComplexity.FanInTwo c → ¬ ∀ x : Fin 7 → Bool,
    c.eval (List.ofFn x ++ [!(x j)]) = theta x

theorem all_heads_from (r0 : NoSignedTail 0) (r2 : NoSignedTail 2) (r3 : NoSignedTail 3)
    (j : Fin 7) : NoSignedTail j := by
  intro c hsize hfan hag
  let f := toRepresentative j
  have hr : NoSignedTail (f j) := by
    change NoSignedTail (toRepresentative j j)
    rw [rep_head]
    have ids : ∀ i : Fin 7, orbitHead i = 0 ∨ orbitHead i = 2 ∨ orbitHead i = 3 := by decide +kernel
    rcases ids j with h | h | h
    · rw [h]; exact r0
    · rw [h]; exact r2
    · rw [h]; exact r3
  apply hr (relabeled f c) (by simpa [relabeled,Circuit.size] using hsize) ?_
  · intro x
    have hrow := rename_run f c.gates (List.ofFn (fun i => x (f i)) ++ [!(x (f j))])
      (List.ofFn x ++ [!(x (f j))]) (by simp) (by simp) (initial_rename f j x) c.output
    exact hrow.trans ((hag (fun i => x (f i))).trans (rep_target j x))
  · intro g hg
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hg
    simpa [renameGate] using hfan old hold

/-- The rowwise value of the first, possibly noncanonical, gate suffices.
    Its other pins and its particular syntax are immaterial. -/
theorem physical_of_signed_tail (j : Fin 7) (cert : NoSignedTail j) (g : Gate)
    (gs : List Gate) (o : Nat) (hf : PEqualNP.MetaComplexity.FanInTwo ⟨g :: gs,o⟩)
    (hs : (Circuit.mk (g :: gs) o).size ≤ 11)
    (head : ∀ x : Fin 7 → Bool,
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = !(x j)) :
    ¬ ∀ x : Fin 7 → Bool, (Circuit.mk (g :: gs) o).eval (List.ofFn x) = theta x := by
  intro h
  apply cert (Circuit.mk gs o) (by
    change gs.length ≤ 10
    change (g :: gs).length ≤ 11 at hs
    simp only [List.length_cons] at hs
    omega)
    (fun g' hg => hf g' (List.mem_cons_of_mem _ hg))
  intro x
  have he := h x
  change (gs.foldl (fun w g' => w ++ [g'.op.eval (g'.inputs.map fun i => w.getD i false)])
    (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD o false = _ at he
  rw [head x] at he
  exact he

end CoThetaWholeBase
