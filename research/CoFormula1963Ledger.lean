import PEqualNP.Defs

namespace CoFormula1963Ledger
open PEqualNP.CircuitLowerBounds
open scoped BigOperators

def readCost (w : List ℕ) (is : List ℕ) := (is.map (fun i => w.getD i 0)).sum

/-- Only effective gate reads enter the fanout count. Out-of-bounds and
    self/forward operands have the fixed value false and may repeat freely. -/
def refs (available : ℕ) : List Gate → List ℕ
  | [] => []
  | g::gs => (g.inputs.filter fun i => i<available) ++ refs (available+1) gs

def noShare (n : ℕ) (gs : List Gate) := ((refs n gs).filter (fun i => n ≤ i)).Nodup

private theorem refs_append (n : ℕ) (a b : List Gate) :
    refs n (a++b) = refs n a ++ refs (n+a.length) b := by
  induction a generalizing n with
  | nil => simp [refs]
  | cons g gs ih => simp [refs,ih,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem prefix_nd {A : Type*} (a b : List A) (h : (a++b).Nodup) : a.Nodup := by
  induction a with
  | nil => simp
  | cons x a ih =>
    obtain ⟨apart,tail⟩ := List.nodup_cons.mp h
    exact List.nodup_cons.mpr ⟨fun hx => apart (List.mem_append_left _ hx), ih tail⟩

/-- For each new physical gate record the number of AND/OR nodes in its
    unfolded and constant-simplified expression. This local upper bound is
    the only property of the expression transformation used in the ledger. -/
inductive Trace (n : ℕ) : List Gate → List ℕ → Prop
  | start : Trace n [] (List.replicate n 0)
  | step {gs w} (prev : Trace n gs w) (g : Gate) (z : ℕ)
      (price : z ≤ 1+readCost w g.inputs) : Trace n (gs++[g]) (w++[z])

private theorem oldRead (w more : List ℕ) (i : ℕ) (hi : i<w.length) :
    (w++more).getD i 0 = w.getD i 0 := by
  simp [List.getD,List.getElem?_append_left hi]

private theorem newRead (w : List ℕ) (z : ℕ) : (w++[z]).getD w.length 0 = z := by
  simp [List.getD,List.getElem?_append_right]

private theorem pastEnd (w : List ℕ) (i : ℕ) (hi : w.length ≤ i) : w.getD i 0 = 0 := by
  simp [List.getD,List.getElem?_eq_none hi]

private theorem replicate_read (n i : ℕ) : (List.replicate n 0).getD i 0 = 0 := by
  induction n generalizing i with
  | zero => simp [List.getD]
  | succ n ih => cases i <;> simp [List.replicate_succ,List.getD,ih]

private theorem grows (w more : List ℕ) (is : List ℕ) : readCost w is ≤ readCost (w++more) is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change w.getD i 0 + readCost w is ≤ (w++more).getD i 0 + readCost (w++more) is
    apply Nat.add_le_add _ ih
    by_cases hi : i<w.length
    · rw [oldRead _ _ _ hi]
    · rw [pastEnd _ _ (by omega)]; omega

theorem trace_len {n gs w} (T : Trace n gs w) : w.length = n+gs.length := by
  induction T with
  | start => simp
  | step _ _ _ _ ih => simp [ih]; omega

theorem raw_zero {n gs w} (T : Trace n gs w) (i : ℕ) (hi : i<n) : w.getD i 0 = 0 := by
  induction T with
  | start => exact replicate_read _ _
  | step prev _ _ _ ih => rw [oldRead]; exact ih; have := trace_len prev; omega

private theorem filter_zero (w : List ℕ) (is : List ℕ) (p : ℕ → Bool)
    (z : ∀ i, p i=false → w.getD i 0=0) : readCost w (is.filter p) = readCost w is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    cases h : p i with
    | false =>
      calc
        _ = readCost w (is.filter p) := by simp [h]
        _ = readCost w is := ih
        _ = readCost w (i::is) := by change readCost w is = w.getD i 0 + readCost w is; rw [z i h,Nat.zero_add]
    | true =>
      simpa [h,readCost] using congrArg (fun a => w.getD i 0+a) ih

private theorem clip (w : List ℕ) (is : List ℕ) :
    readCost w (is.filter fun i => i<w.length) = readCost w is :=
  filter_zero _ _ _ (fun i h => pastEnd _ _ (by simpa using h))

theorem accumulated {n gs w} (T : Trace n gs w) : w.sum ≤ gs.length+readCost w (refs n gs) := by
  induction T with
  | start => simp [readCost,refs]
  | @step gs w prev g z price ih =>
    have a := grows w [z] (refs n gs)
    let pins := g.inputs.filter (fun i => i<w.length)
    have b := grows w [z] pins
    have costOld : readCost w pins = readCost w g.inputs := clip _ _
    have split : readCost (w++[z]) (refs n (gs++[g])) =
        readCost (w++[z]) (refs n gs) + readCost (w++[z]) pins := by
      simp [refs_append,refs,readCost,pins,trace_len prev]
    rw [split]
    simp only [List.sum_append,List.sum_cons,List.sum_nil,List.length_append,List.length_cons,
      List.length_nil,Nat.add_zero]
    omega

private theorem index_sum (w : List ℕ) (is : List ℕ) (nd : is.Nodup) :
    readCost w is = ∑ i ∈ is.toFinset, w.getD i 0 := by
  induction is with
  | nil => simp [readCost]
  | cons x xs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp nd
    simpa [readCost,List.toFinset_cons,fresh] using congrArg (fun a => w.getD x 0+a) (ih tail)

private theorem all_sum (w : List ℕ) : (∑ i ∈ Finset.range w.length, w.getD i 0) = w.sum := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w z ih =>
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add,
      Finset.sum_range_succ,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,newRead]
    rw [← ih]
    apply congrArg (fun a => a+z)
    apply Finset.sum_congr rfl
    exact fun i hi => oldRead _ _ _ (Finset.mem_range.mp hi)

theorem bounded_reads {n gs w} (T : Trace n gs w) (is : List ℕ)
    (nd : (is.filter (fun i => n ≤ i)).Nodup) : readCost w is ≤ w.sum := by
  let xs := is.filter (fun i => n ≤ i)
  have a : readCost w xs = readCost w is :=
    filter_zero w is _ (fun i h => raw_zero T i (by simpa using h))
  have b : readCost w (xs.filter (fun i => i<w.length)) = readCost w xs :=
    filter_zero w xs _ (fun i h => pastEnd w i (by simpa using h))
  rw [← a,← b,index_sum _ _ (nd.filter _),← all_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_range.mpr (by simpa using (List.mem_filter.mp (List.mem_toFinset.mp hi)).2)
  · intros; exact Nat.zero_le _

theorem final_charge {n gs w} (T : Trace n gs w) (g : Gate) (z : ℕ)
    (price : z≤1+readCost w g.inputs) (s : noShare n (gs++[g])) : z ≤ gs.length+1 := by
  have cap := bounded_reads T (refs n (gs++[g])) s
  have split : readCost w (refs n (gs++[g])) = readCost w (refs n gs)+readCost w g.inputs := by
    have h := clip w g.inputs
    simp only [readCost] at h ⊢
    simp [refs_append,refs,←trace_len T,h]
  rw [split] at cap
  have spent := accumulated T
  omega

theorem any_wire {n gs w} (T : Trace n gs w) (s : noShare n gs) (i : ℕ) :
    w.getD i 0 ≤ gs.length := by
  induction T with
  | start => simp [replicate_read]
  | @step gs w prev g z price ih =>
    have ss : noShare n gs := by
      apply prefix_nd _ ((refs (n+gs.length) [g]).filter (fun i => n ≤ i))
      simpa [noShare,refs_append] using s
    have last := final_charge prev g z price s
    have earlier := ih ss
    by_cases old : i<w.length
    · rw [oldRead _ _ _ old]; simp; omega
    by_cases top : i=w.length
    · subst i; rw [newRead]; simpa using last
    · rw [pastEnd]; omega; simp; omega

#print axioms any_wire
end CoFormula1963Ledger
