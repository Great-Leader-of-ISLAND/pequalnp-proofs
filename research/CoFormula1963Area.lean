import PEqualNP.CoFormula1963Local

namespace CoFormula1963Area
open CoFormula1963Local

/-- Concrete active rectangles at a fixed vertex and fixed negative column.
    Skipping a row mask means that rectangle does not contain the column.
    Selecting a row mask requires disjointness from all other active masks. -/
inductive Selection : List ℕ → ℕ → Prop
  | nil : Selection [] 0
  | skip {ms u} (m : ℕ) : Selection ms u → Selection (m::ms) u
  | take {ms u m} : Selection ms u → u &&& m = 0 → Selection (m::ms) (u ||| m)

theorem selection_compatible {F : List ℕ} {u : ℕ} (s : Selection F u) :
    u ∈ compatible F := by
  induction s with
  | nil => simp [compatible]
  | skip m _ ih =>
    exact List.mem_append_left _ ih
  | take _ h ih =>
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨_,List.mem_filter.mpr ⟨ih,by simp [h]⟩,rfl⟩

/-- OR of the masks of the rectangles containing this particular column. -/
def unionAt {K : Type*} (mask : K → ℕ) (active : K → Bool) : List K → ℕ
  | [] => 0
  | x::xs => if active x then mask x ||| unionAt mask active xs else unionAt mask active xs

private theorem bit_witness {K : Type*} (mask : K → ℕ) (active : K → Bool)
    (xs : List K) (i : ℕ) (bit : (unionAt mask active xs).testBit i = true) :
    ∃ k ∈ xs, active k = true ∧ (mask k).testBit i = true := by
  induction xs with
  | nil => simp [unionAt] at bit
  | cons x xs ih =>
    cases ax : active x with
    | false =>
      obtain ⟨k,mem,on,here⟩ := ih (by simpa [unionAt,ax] using bit)
      exact ⟨k,List.mem_cons_of_mem _ mem,on,here⟩
    | true =>
      have h : (mask x).testBit i = true ∨ (unionAt mask active xs).testBit i = true := by
        simpa [unionAt,ax,Nat.testBit_or,Bool.or_eq_true] using bit
      rcases h with h | h
      · exact ⟨x,by simp,ax,h⟩
      · obtain ⟨k,mem,on,here⟩ := ih h
        exact ⟨k,List.mem_cons_of_mem _ mem,on,here⟩

/-- Construct the selected-mask derivation from disjointness at the actual
    rectangle/row/column cells. IDs are occurrence indices, even if their
    masks agree. -/
theorem from_partition {K : Type*} (mask : K → ℕ) (active : K → Bool)
    (xs : List K) (ids : xs.Nodup)
    (disjoint : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → active a = true → active b = true →
      ∀ i, (mask a).testBit i = true → (mask b).testBit i = false) :
    Selection (xs.map mask) (unionAt mask active xs) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    obtain ⟨apart,ids'⟩ := List.nodup_cons.mp ids
    have rest := ih ids' (fun a ha b hb => disjoint a (List.mem_cons_of_mem _ ha)
      b (List.mem_cons_of_mem _ hb))
    cases ax : active x with
    | false => simpa [unionAt,ax] using Selection.skip (mask x) rest
    | true =>
      have apartBits : unionAt mask active xs &&& mask x = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_and]
        cases hi : (unionAt mask active xs).testBit i with
        | false => simp
        | true =>
          obtain ⟨b,mem,on,here⟩ := bit_witness mask active xs i hi
          have ne : b ≠ x := by intro eq; subst b; exact apart mem
          have off := disjoint b (List.mem_cons_of_mem _ mem) x (by simp)
            ne on ax i here
          simp [off]
      simpa [unionAt,ax,Nat.or_comm] using Selection.take rest apartBits

def update (m old w : ℕ) : ℕ :=
  if w &&& m == m then min old (weight w) else old

private theorem decreases (m : ℕ) (xs : List ℕ) (a : ℕ) :
    xs.foldl (update m) a ≤ a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    exact (ih _).trans (by unfold update; split <;> simp)

private theorem hits_upper (m : ℕ) (xs : List ℕ) (a w : ℕ)
    (mem : w ∈ xs) (req : w &&& m = m) :
    xs.foldl (update m) a ≤ weight w := by
  induction xs generalizing a with
  | nil => simp at mem
  | cons x xs ih =>
    rcases List.mem_cons.mp mem with e | e
    · subst x
      exact (decreases m xs _).trans (by simp [update,req])
    · exact ih _ e

theorem cost_of_column {F : List ℕ} {u m : ℕ} (s : Selection F u)
    (required : u &&& m = m) : least (compatible F) m ≤ weight u := by
  exact hits_upper m (compatible F) 5 u (selection_compatible s) required

/-- The four-row histogram: one copy of each single/two-row forced mask
    repeated a or b times. The actual negative columns may be ordered freely. -/
def blocks (n : ℕ) (ms : List ℕ) := ms.flatMap (fun m => List.replicate n m)

private theorem rep_sum (n k : ℕ) : (List.replicate n k).sum = n*k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,ih,Nat.succ_mul,Nat.add_comm]

private theorem block_sum (f : ℕ → ℕ) (n : ℕ) (ms : List ℕ) :
    ((blocks n ms).map f).sum = n*(ms.map f).sum := by
  induction ms with
  | nil => simp [blocks]
  | cons m ms ih =>
    change ((List.replicate n m ++ blocks n ms).map f).sum = n*(f m + (ms.map f).sum)
    simp [rep_sum,ih,Nat.mul_add]

private theorem sums_le {α : Type*} (a b : α → ℕ) (xs : List α)
    (h : ∀ x ∈ xs, a x ≤ b x) : (xs.map a).sum ≤ (xs.map b).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem vertex_area {α : Type*} (F : List ℕ) (ys : List α) (forced used : α → ℕ)
    (a b : ℕ) (freq : (ys.map forced).Perm (blocks a one ++ blocks b two))
    (selected : ∀ y ∈ ys, Selection F (used y))
    (contained : ∀ y ∈ ys, used y &&& forced y = forced y) :
    a*singles F + b*pairs F ≤ (ys.map fun y => weight (used y)).sum := by
  let h := least (compatible F)
  have same := (freq.map h).sum_eq
  have sum_eq : (ys.map (fun y => h (forced y))).sum = a*singles F + b*pairs F := by
    simpa [List.map_map,Function.comp_def,block_sum,singles,pairs,h] using same
  rw [← sum_eq]
  exact sums_le _ _ _ (fun y hy => cost_of_column (selected y hy) (contained y hy))

#print axioms vertex_area
end CoFormula1963Area
