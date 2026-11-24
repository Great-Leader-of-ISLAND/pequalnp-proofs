import PEqualNP.CoFormula1963Flags

namespace CoFormula1963Vertex
open CoFormula1963Geometry CoFormula1963Protocol CoFormula1963Private CoFormula1963Link
open CoFormula1963Area CoFormula1963Packed CoFormula1963Flags CoFormula1963Local
open scoped BigOperators

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem sum_four (f : Fin 4 → ℕ) :
    (∑ i : Fin 4, f i) = f 0+(f 1+(f 2+f 3)) := by simp [Fin.sum_univ_succ]

theorem filter_four (p : ℕ → Bool) :
    ((List.range 4).filter p).length = ∑ i : Fin 4, if p i then 1 else 0 := by
  rw [sum_four]
  change ([0,1,2,3].filter p).length = _
  cases h0 : p 0 <;> cases h1 : p 1 <;> cases h2 : p 2 <;> cases h3 : p 3 <;>
    simp [h0,h1,h2,h3]

theorem flag_inj : ∀ v : X, ∀ i j : Fin 4, flag v i = flag v j → i = j := by decide +kernel

theorem cols_singleton : ∀ y : Col, CoFormula1963Frequency.cols.filter (fun z => z=y) = [y] := by
  intro y
  rcases y with ⟨r,s⟩
  revert s
  fin_cases r <;> decide +kernel

theorem sum_cols (f : Col → ℕ) : (CoFormula1963Frequency.cols.map f).sum = ∑ y : Col, f y := by
  rw [← CoFormula1963Mass.by_label id f CoFormula1963Frequency.cols]
  apply Finset.sum_congr rfl
  intro y _
  simpa only [id_eq,cols_singleton,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]

theorem list_filter_le {A : Type*} (f : A → ℕ) (p : A → Bool) (xs : List A) :
    ((xs.filter p).map f).sum ≤ (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x with
    | false =>
      calc
        _ = ((xs.filter p).map f).sum := by simp [h]
        _ ≤ _ := ih
        _ ≤ (List.map f (x::xs)).sum := by simp
    | true => simpa [h] using Nat.add_le_add_left ih (f x)

theorem cell_weight (t : Expr X) (v : X) (y : Col) :
    weight (used t v y) ≤ ∑ i : Fin 4, multiplicity (flag v i) y (bucket t v) := by
  rw [weight,filter_four]
  apply Finset.sum_le_sum
  intro i _
  rw [← cells]
  cases b : (used t v y).testBit i with
  | false => simp
  | true =>
    have hh := (test_count (mask v) (active y) (bucket t v) i).mp b
    change 1 ≤ cnt (mask v) (active y) (bucket t v) i
    omega

theorem inject_sum {A B : Type*} [Fintype A] [DecidableEq B]
    (g : A → B) (f : B → ℕ) (inj : Function.Injective g) :
    (∑ i : A, f (g i)) = ∑ e ∈ Finset.univ.image g, f e := by
  rw [Finset.sum_image]
  exact fun a _ b _ h => inj h

theorem sum_inject_le {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (g : A → B) (f : B → ℕ) (inj : Function.Injective g) :
    (∑ i : A, f (g i)) ≤ ∑ e : B, f e := by
  rw [inject_sum g f inj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)

theorem inj_flag (v : X) : Function.Injective (flag v) := by
  intro i j h
  exact flag_inj v i j h

def localArea (t : Expr X) (v : X) := ((bucket t v).map CoFormula1963Mass.area).sum

theorem local_area_upper (t : Expr X) (v : X) (p : Col → Bool) :
    (((CoFormula1963Frequency.cols.filter p).map fun y => weight (used t v y))).sum ≤
    localArea t v := by
  calc
    _ ≤ (CoFormula1963Frequency.cols.map fun y => weight (used t v y)).sum :=
      list_filter_le _ _ _
    _ = ∑ y : Col, weight (used t v y) := sum_cols _
    _ ≤ ∑ y : Col, ∑ i : Fin 4, multiplicity (flag v i) y (bucket t v) :=
      Finset.sum_le_sum fun y _ => cell_weight t v y
    _ = ∑ i : Fin 4, ∑ y : Col, multiplicity (flag v i) y (bucket t v) := Finset.sum_comm
    _ ≤ ∑ e : E, ∑ y : Col, multiplicity e y (bucket t v) :=
      sum_inject_le (A:=Fin 4) (B:=E) (flag v)
        (fun e : E => ∑ y : Col, CoFormula1963Protocol.multiplicity e y (bucket t v)) (inj_flag v)
    _ = _ := (CoFormula1963Mass.cell_sum _).symm

private theorem pbit (y : Col) (p : V) : neg y (.inl p) = CoFormula1963Frequency.pointOn y p := by
  obtain ⟨r,s⟩ := y
  unfold neg
  exact (CoFormula1963Frequency.row_bits r s p).1.symm

private theorem lbit (y : Col) (l : V) : neg y (.inr l) = CoFormula1963Frequency.lineOn y l := by
  obtain ⟨r,s⟩ := y
  unfold neg
  exact (CoFormula1963Frequency.row_bits r s l).2.symm

theorem point_mask (p : V) (y : Col) :
    mandatory (.inl p) y = CoFormula1963Frequency.pointMask p y := by
  change CoFormula1963Frequency.four (neg y (.inr (p-0))) (neg y (.inr (p-1)))
    (neg y (.inr (p-3))) (neg y (.inr (p-9))) = _
  simp only [sub_zero,lbit,CoFormula1963Frequency.pointMask]

theorem line_mask (l : V) (y : Col) :
    mandatory (.inr l) y = CoFormula1963Frequency.lineMask l y := by
  change CoFormula1963Frequency.four (neg y (.inl (l+0))) (neg y (.inl (l+1)))
    (neg y (.inl (l+3))) (neg y (.inl (l+9))) = _
  simp only [add_zero,pbit,CoFormula1963Frequency.lineMask]

private theorem low_sum {A : Type*} (xs : List A) (a b : A → ℕ) (h : ∀ x∈xs, a x ≤ b x) :
    (xs.map a).sum ≤ (xs.map b).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact Nat.add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- The forced masks have total Hamming weight 216 at a point and 288 at a
    line. This argument works for any shape or number of local rectangles. -/
private theorem paid_forced {A : Type*} (ys : List A) (m u : A → ℕ) (ref : List ℕ)
    (hist : (ys.map m).Perm ref) (h : ∀ y, weight (m y) ≤ weight (u y)) :
    (ref.map weight).sum ≤ (ys.map fun y => weight (u y)).sum := by
  have sums := (hist.map weight).sum_eq
  rw [← sums,List.map_map]
  exact low_sum _ _ _ (fun y _ => h y)

private theorem present_mask {A : Type*} (ys : List A) (m : A → ℕ) (ref : List ℕ)
    (h : (ys.map m).Perm ref) (all : ∀ z∈one++two,z∈ref) :
    ∀ z∈one++two, ∃ y∈ys,m y=z := by
  intro z hz
  exact List.mem_map.mp (h.mem_iff.mpr (all z hz))

theorem local_charge (t : Expr X) (accept : ∀ e : E, t.eval (pos e) = true)
    (reject : ∀ y : Col, t.eval (neg y) = false) (v : X) :
    (match v with | .inl _ => 1044 | .inr _ => 1116) + 189*privateRows (masks t v) ≤
    396*(bucket t v).length + localArea t v := by
  have valid : ∀ m ∈ masks t v, m < 16 := by
    intro m hm
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hm
    exact pack_lt _
  have costs (y : Col) : weight (mandatory v y) ≤ weight (used t v y) :=
    CoFormula1963Shapes.monotone_weight
      ⟨used t v y,union_small _ _ _ (fun _ _ => pack_lt _)⟩ ⟨mandatory v y,pack_lt _⟩
      (forced_subset t accept reject v y)
  have f (ys : List Col) {a b : ℕ}
      (hist : (ys.map (mandatory v)).Perm (blocks a one ++ blocks b two))
      (presentAll : ∀ z∈one++two,z ∈ blocks a one ++ blocks b two) :
      feasible (masks t v) = true ∧
      a*singles (masks t v)+b*pairs (masks t v) ≤ (ys.map fun y => weight (used t v y)).sum ∧
      ((blocks a one ++ blocks b two).map weight).sum ≤ (ys.map fun y => weight (used t v y)).sum := by
    refine ⟨CoFormula1963Shapes.feasible_from_columns _ ys _ _
      (present_mask ys _ _ hist presentAll) (fun y _ => selection t v y)
      (fun y _ => forced_subset t accept reject v y),?_,paid_forced ys _ _ _ hist costs⟩
    exact vertex_area _ ys _ _ a b hist (fun y _ => selection t v y)
      (fun y _ => forced_subset t accept reject v y)
  cases v with
  | inl p =>
    have hist := CoFormula1963Frequency.point_freq p
    have eq : mandatory (.inl p) = CoFormula1963Frequency.pointMask p := funext (point_mask p)
    rw [← eq] at hist
    obtain ⟨ok,low,raw⟩ := f _ hist (by decide +kernel)
    have hi := local_area_upper t (.inl p) (fun y => !CoFormula1963Frequency.pointOn y p)
    have mass : ((blocks 27 one ++ blocks 9 two).map weight).sum = 216 := by decide +kernel
    rw [mass] at raw
    simpa [masks] using (CoFormula1963Shapes.charge _ valid ok _).1 (low.trans hi) (raw.trans hi)
  | inr l =>
    have hist := CoFormula1963Frequency.line_freq l
    have eq : mandatory (.inr l) = CoFormula1963Frequency.lineMask l := funext (line_mask l)
    rw [← eq] at hist
    obtain ⟨ok,low,raw⟩ := f _ hist (by decide +kernel)
    have hi := local_area_upper t (.inr l) (fun y => !CoFormula1963Frequency.lineOn y l)
    have mass : ((blocks 18 one ++ blocks 18 two).map weight).sum = 288 := by decide +kernel
    rw [mass] at raw
    simpa [masks] using (CoFormula1963Shapes.charge _ valid ok _).2 (low.trans hi) (raw.trans hi)

#print axioms local_charge
end CoFormula1963Vertex
