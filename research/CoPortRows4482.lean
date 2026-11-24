import PEqualNP.CoPortSlice4482
namespace CoPortRows4482
open CoPortEngine4482 CoPortSlice4482

def maskGraph (vals : Fin 9 → B) : B :=
  (([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).map (fun n =>
    vals (Fin.ofNat 9 (n/10)) &&& vals (Fin.ofNat 9 (n%10)))).foldr (· ||| ·) 0

private theorem fold_bit (ys : List B) (i : ℕ) :
    (ys.foldr (· ||| ·) 0).getLsbD i = ys.any (fun w => w.getLsbD i) := by
  induction ys with
  | nil => simp
  | cons a t ih => simp [BitVec.getLsbD_or,ih]

theorem graph_bit (v : Fin 9 → B) (i : ℕ) :
    (maskGraph v).getLsbD i = graph (fun j => (v j).getLsbD i) := by
  rw [maskGraph,fold_bit]
  simp [graph,List.any_map,BitVec.getLsbD_and,Function.comp_def]

def lowBits (b : Nat) (xs : Fin 9 → Sig) (j : Fin 9) : B :=
  if b.testBit j.val then (xs j).1 else 0

def highBits (b : Nat) (xs : Fin 9 → Sig) (j : Fin 9) : B :=
  if b.testBit j.val then (xs j).2 else top

def rowCheck (b : Nat) (xs : Fin 9 → Sig) : Bool :=
  maskGraph (lowBits b xs) == 0 && maskGraph (fun j => (xs j).1) == top &&
    maskGraph (fun j => (xs j).2) == 0 && maskGraph (highBits b xs) == top

theorem rows {b : Nat} {xs : Fin 9 → Sig} (ok : rowCheck b xs = true) (i : Fin 160) :
    (graph (low b (row xs true i)) = false ∧ graph (row xs true i) = true) ∧
    (graph (row xs false i) = false ∧ graph (high b (row xs false i)) = true) := by
  simp only [rowCheck,Bool.and_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨⟨l,p⟩,n⟩,h⟩ := ok
  have low_eq : low b (row xs true i) = fun j => (lowBits b xs j).getLsbD i.val := by
    funext j
    cases e : b.testBit j.val <;> simp [low,lowBits,row,bit,e]
  have high_eq : high b (row xs false i) = fun j => (highBits b xs j).getLsbD i.val := by
    funext j
    cases e : b.testBit j.val <;> simp [high,highBits,row,bit,e,top,i.isLt]
  rw [low_eq,high_eq]
  have bit_hi (v : Fin 9 → B) (yes : maskGraph v = top) :
      graph (fun j => (v j).getLsbD i.val) = true := by
    rw [←graph_bit,yes]
    simp [top,i.isLt]
  have bit_lo (v : Fin 9 → B) (no : maskGraph v = 0) :
      graph (fun j => (v j).getLsbD i.val) = false := by
    rw [←graph_bit,no]
    simp
  exact ⟨⟨bit_lo _ l,bit_hi _ p⟩,bit_lo _ n,bit_hi _ h⟩

end CoPortRows4482
