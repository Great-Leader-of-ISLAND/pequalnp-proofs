import PEqualNP.Defs

namespace CoStarFamily3443
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The current OR value is initially raw leaf 1, then the last appended gate. -/
def tip (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => n+k

def chain (n : ℕ) : ℕ → List Gate
  | 0 => []
  | k+1 => chain n k ++ [⟨.or,[tip n k,k+2]⟩]

/-- The next four wires are mark ∧ union, center ∧ repeat, center ∧ union, and
    the OR of the latter two. The mark is usually an actual leaf. -/
def suffix (f union mark : ℕ) : List Gate :=
  [⟨.and,[union,mark]⟩,⟨.and,[0,f]⟩,⟨.and,[0,union]⟩,⟨.or,[f+1,f+2]⟩]

def circuit (q mark : ℕ) : Circuit :=
  let n := q+1
  let k := q-1
  ⟨chain n k ++ suffix (n+k) (tip n k) mark,n+k+3⟩

@[simp] theorem chain_length (n k : ℕ) : (chain n k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [chain,ih]

theorem size (q mark : ℕ) (hq : 1≤q) : (circuit q mark).size=q+3 := by
  simp only [circuit,Circuit.size,List.length_append,chain_length]
  change q-1+4=q+3
  omega

private def emit (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl emit w

private theorem old (w more : List Bool) (i : ℕ) (hi : i<w.length) :
    (w++more).getD i false=w.getD i false := by
  simp [List.getD,List.getElem?_append_left hi]

private theorem added (w more : List Bool) (i : ℕ) :
    (w++more).getD (w.length+i) false=more.getD i false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_add_right w.length i)]
  simp

private theorem snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs++[g]) w = emit (run gs w) g := by simp [run,List.foldl_append]

private theorem disj (w : List Bool) (a b : ℕ) :
    emit w ⟨.or,[a,b]⟩ = w++[w.getD a false || w.getD b false] := by
  simp [emit,GateOp.eval]

private theorem conj (w : List Bool) (a b : ℕ) :
    emit w ⟨.and,[a,b]⟩ = w++[w.getD a false && w.getD b false] := by
  simp [emit,GateOp.eval]

def leafOr (x : List Bool) : ℕ → Bool
  | 0 => x.getD 1 false
  | k+1 => leafOr x k || x.getD (k+2) false

/-- Prefix invariant, including all original wires and the appended output. -/
private theorem prefix_facts (x : List Bool) (n k : ℕ) (hn : x.length=n) (hk : k+1<n) :
    (run (chain n k) x).length=n+k ∧
    (∀ i<n, (run (chain n k) x).getD i false=x.getD i false) ∧
    (run (chain n k) x).getD (tip n k) false=leafOr x k := by
  induction k with
  | zero => exact ⟨hn,fun _ _ => rfl,rfl⟩
  | succ k ih =>
    obtain ⟨hl,original,last⟩ := ih (by omega)
    let w := run (chain n k) x
    have value : run (chain n (k+1)) x = w++[leafOr x (k+1)] := by
      rw [chain,snoc,disj,last,original (k+2) (by omega)] <;> rfl
    rw [value]
    have hw : w.length=n+k := hl
    refine ⟨by simp [hw,Nat.add_assoc],?_,?_⟩
    · intro i hi
      rw [old w _ i (by omega)]
      exact original i hi
    · change (w++[_]).getD (n+k) false=leafOr x (k+1)
      rw [← hw]
      simpa using added w [leafOr x (k+1)] 0

private theorem tip_lt (n k : ℕ) (hn : 1<n) : tip n k<n+k := by
  cases k with
  | zero => simpa [tip] using hn
  | succ k => simp only [tip]; omega

/-- All four gates use actual list reads. The repeated branch is absorbed by
    the full center-and-union branch independently of the mark value. -/
private theorem suffix_eval (w : List Bool) (s mark : ℕ) (hs : s<w.length) :
    (run (suffix w.length s mark) w).getD (w.length+3) false =
      (w.getD 0 false && w.getD s false) := by
  let a := w.getD s false && w.getD mark false
  let b := w.getD 0 false && a
  let c := w.getD 0 false && w.getD s false
  have hz : 0<w.length := by omega
  have h₁ : emit w ⟨.and,[s,mark]⟩=w++[a] := conj w s mark
  have h₂ : emit (w++[a]) ⟨.and,[0,w.length]⟩=w++[a,b] := by
    rw [conj,old w _ 0 hz]
    have e : (w++[a]).getD w.length false=a := by simpa using added w [a] 0
    rw [e]
    simp [b,List.append_assoc]
  have h₃ : emit (w++[a,b]) ⟨.and,[0,s]⟩=w++[a,b,c] := by
    rw [conj,old w _ 0 hz,old w _ s hs]
    simp [c,List.append_assoc]
  have h₄ : emit (w++[a,b,c]) ⟨.or,[w.length+1,w.length+2]⟩=w++[a,b,c,b||c] := by
    rw [disj,added,added]
    simp [List.append_assoc,List.getD]
  change (emit (emit (emit (emit w _) _) _) _).getD _ false = _
  rw [h₁,h₂,h₃,h₄,added]
  change (b||c)=c
  dsimp only [a,b,c]
  cases w.getD 0 false <;> cases w.getD s false <;> cases w.getD mark false <;> rfl

theorem eval_list (q mark : ℕ) (hq : 1≤q) (x : List Bool) (hx : x.length=q+1) :
    (circuit q mark).eval x=(x.getD 0 false && leafOr x (q-1)) := by
  let n := q+1
  let k := q-1
  let w := run (chain n k) x
  have hp : k+1<n := by dsimp [n,k]; omega
  obtain ⟨hw,oldWire,last⟩ := prefix_facts x n k hx hp
  change (run (chain n k ++ suffix (n+k) (tip n k) mark) x).getD (n+k+3) false=_
  have splitRun (a b : List Gate) : run (a++b) x=run b (run a x) := by
    simp [run,List.foldl_append]
  rw [splitRun]
  change (run (suffix (n+k) (tip n k) mark) w).getD (n+k+3) false=_
  have len : w.length=n+k := hw
  rw [← len,suffix_eval w _ _ (by rw [len]; exact tip_lt n k (by dsimp [n]; omega))]
  rw [show w.getD 0 false=x.getD 0 false from oldWire 0 (by dsimp [n]; omega),
      show w.getD (tip n k) false=leafOr x k from last]

private theorem leafOr_iff (x : List Bool) (k : ℕ) :
    leafOr x k = true ↔ ∃ j : ℕ, (0 < j) ∧ (j ≤ k + 1) ∧ x.getD j false = true := by
  induction k with
  | zero =>
    constructor
    · intro h; exact ⟨1,by decide,by decide,h⟩
    · rintro ⟨i,lo,hi,h⟩
      have eq : i=1 := by omega
      simpa [eq,leafOr] using h
  | succ k ih =>
    rw [leafOr,Bool.or_eq_true,ih]
    constructor
    · rintro (⟨i,lo,hi,h⟩|h)
      · exact ⟨i,lo,by omega,h⟩
      · exact ⟨k+2,by omega,by omega,h⟩
    · rintro ⟨i,lo,hi,h⟩
      by_cases small : i≤k+1
      · exact Or.inl ⟨i,lo,small,h⟩
      · have eq : i=k+2 := by omega
        exact Or.inr (eq ▸ h)

private theorem read_input {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false=x i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

theorem computes (q mark : ℕ) (hq : 1≤q) (x : Fin (q+1) → Bool) :
    circuitFun (q+1) (circuit q mark) x =
    (x 0 && decide (∃ i : Fin (q+1), i≠0 ∧ x i=true)) := by
  have raw0 : (List.ofFn x).getD 0 false = x 0 := by
    simpa using read_input x (0 : Fin (q+1))
  rw [circuitFun,eval_list q mark hq _ (by simp),raw0]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [leafOr_iff,decide_eq_true_eq]
  constructor
  · rintro ⟨i,lo,hi,h⟩
    let j : Fin (q+1) := ⟨i,by omega⟩
    refine ⟨j,?_,?_⟩
    · intro e
      have bad : i = 0 := by simpa [j] using congrArg Fin.val e
      omega
    · exact (read_input x j).symm.trans h
  · rintro ⟨i,pos,h⟩
    have nz : i.val ≠ 0 := by
      intro e
      apply pos
      apply Fin.ext
      simpa using e
    exact ⟨i.val,by omega,by have := i.isLt; omega,(read_input x i).trans h⟩

#print axioms CoStarFamily3443.computes
end CoStarFamily3443
