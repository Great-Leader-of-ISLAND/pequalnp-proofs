import PEqualNP.CoNonredundant3825
import PEqualNP.CoNearReaders3825
namespace CoLocalGate3825
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoNonredundant3825 CoNearReaders3825

/- Gate-at-time evaluation, as in the physical compaction of R_meta_2498_1. -/
theorem evaluate {n : ℕ} (C : Circuit) (ordered : NestedCover.ReadsBack n C)
    (j : ℕ) (actual : j < C.gates.length) (x : Fin n → Bool) :
    wire n C (n+j) x=(atPos C j).op.eval ((atPos C j).inputs.map (fun i => wire n C i x)) := by
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]; omega
  have lengthOf (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]; omega
  have last (w : List Bool) (b : Bool) (n : ℕ) (hn : w.length = n) :
      (w ++ [b]).getD n false = b := by
    subst hn
    simp [List.getD_eq_getElem?_getD]
  have beyond (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have getOf (n : ℕ) (y : Fin n → Bool) (m : Fin n) : (List.ofFn y).getD m.val false = y m := by
    simp [List.getD_eq_getElem?_getD]
  let W : (Fin n → Bool) → List Bool := fun y => C.wires (List.ofFn y)
  have gateW (k : ℕ) (hk : k < C.gates.length) (y) :
      (W y).getD (n + k) false =
        (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i =>
          if i < n + k then (W y).getD i false else false) := by
    have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by simp
    let P := (C.gates.take k).foldl step (List.ofFn y)
    have hP : P.length = n + k := by simp [P, lengthOf]; omega
    have hW : W y = (C.gates.drop (k + 1)).foldl step (step P C.gates[k]) := by
      change C.gates.foldl step (List.ofFn y) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hlow (i : ℕ) (hi : i < n + k) : (W y).getD i false = P.getD i false := by
      rw [hW, keep _ _ _ (by simp [step]; omega)]
      simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (hP ▸ hi)]
    rw [hW, keep _ _ _ (by simp [step]; omega)]
    have h1 : (step P C.gates[k]).getD (n + k) false =
        (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i => P.getD i false) :=
      last _ _ _ hP
    rw [h1, ← hW]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    split_ifs with hi
    · exact (hlow i hi).symm
    · exact beyond _ _ (by omega)
  have he : atPos C j=C.gates[j] := by simp [atPos,NestedCover.gateAt,List.getD_eq_getElem?_getD,actual]
  have eval := gateW j actual x
  rw [←he] at eval
  change (W x).getD (n+j) false=_
  rw [eval]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact if_pos (ordered j actual i hi)

private theorem pair_shape {xs : List ℕ} {a b : ℕ} (neq : a≠b)
    (ha : a∈xs) (hb : b∈xs) (cap : xs.length≤2) :
    xs=[a,b] ∨ xs=[b,a] := by
  rcases xs with _|⟨i,_|⟨j,_|⟨k,rest⟩⟩⟩ <;> simp_all <;> aesop

private theorem single_shape {xs : List ℕ} {a : ℕ} (ha : a∈xs) (one : xs.length=1) :
    xs=[a] := by
  rcases xs with _|⟨i,_|⟨j,rest⟩⟩ <;> simp_all

theorem co_reader_redundant {n : ℕ} {C : Circuit} (fan : FanInTwo C)
    (ordered : NestedCover.ReadsBack n C)
    (arity : ∀ i < C.gates.length,(atPos C i).op=.not → (atPos C i).inputs.length=1)
    (v : Fin n) {j k : ℕ} (early : j < k) (actual : k < C.gates.length)
    (hj : v.val∈(atPos C j).inputs)
    (spec : (atPos C j).op=.and ∨ (atPos C j).op=.not)
    (both : v.val∈(atPos C k).inputs ∧ n+j∈(atPos C k).inputs) : bypassable n C k := by
  classical
  have ja : j < C.gates.length := by omega
  have he : atPos C k=C.gates[k] := by simp [atPos,NestedCover.gateAt,List.getD_eq_getElem?_getD,actual]
  have good := fan (atPos C k) (by rw [he]; exact List.getElem_mem actual)
  have diff : v.val≠n+j := by have := v.isLt; omega
  have form := pair_shape diff both.1 both.2 good.2
  have binary : (atPos C k).op=.and ∨ (atPos C k).op=.or := by
    rcases (show (atPos C k).op=.and ∨ (atPos C k).op=.or ∨ (atPos C k).op=.not by
      simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using good.1) with yes|yes|no
    · exact Or.inl yes
    · exact Or.inr yes
    · have one := arity k actual no
      rcases form with f|f <;> rw [f] at one <;> cases one
  have av (op : (atPos C k).op=.and) (x) :
      wire n C (n+k) x=(wire n C v.val x && wire n C (n+j) x) := by
    rw [evaluate C ordered k actual x,op]
    rcases form with f|f <;> simp [f,GateOp.eval,Bool.and_comm]
  have ov (op : (atPos C k).op=.or) (x) :
      wire n C (n+k) x=(wire n C v.val x || wire n C (n+j) x) := by
    rw [evaluate C ordered k actual x,op]
    rcases form with f|f <;> simp [f,GateOp.eval,Bool.or_comm]
  rcases spec with A|N
  · have le (x) (yes : wire n C (n+j) x=true) : wire n C v.val x=true := by
      rw [evaluate C ordered j ja x,A] at yes
      have every := List.all_eq_true.mp yes
      exact every _ (List.mem_map.mpr ⟨v.val,hj,rfl⟩)
    rcases binary with op|op
    · refine Or.inr ⟨n+j,by omega,fun x => (av op x).trans ?_⟩
      cases hv : wire n C (n+j) x with
      | false => simp
      | true => simp [le x hv]
    · refine Or.inr ⟨v.val,by have := v.isLt; omega,fun x => (ov op x).trans ?_⟩
      cases hv : wire n C (n+j) x with
      | false => simp
      | true => simp [le x hv]
  · have pins := single_shape hj (arity j ja N)
    have nv (x) : wire n C (n+j) x= !(wire n C v.val x) := by
      rw [evaluate C ordered j ja x,N,pins]
      rfl
    rcases binary with op|op
    · refine Or.inl ⟨false,fun x => ?_⟩
      rw [av op x,nv x]
      cases wire n C v.val x <;> rfl
    · refine Or.inl ⟨true,fun x => ?_⟩
      rw [ov op x,nv x]
      cases wire n C v.val x <;> rfl

theorem no_common {n : ℕ} {C : Circuit} (min : IsMinimalCircuit n C)
    (nc : nonconstant n C) (ordered : NestedCover.ReadsBack n C)
    (arity : ∀ i < C.gates.length,(atPos C i).op=.not → (atPos C i).inputs.length=1)
    (v : Fin n) {j k : ℕ} (early : j < k) (actual : k < C.gates.length)
    (hj : v.val∈(atPos C j).inputs)
    (spec : (atPos C j).op=.and ∨ (atPos C j).op=.not)
    (both : v.val∈(atPos C k).inputs ∧ n+j∈(atPos C k).inputs) : False :=
  no_alias_or_constant min nc actual
    (co_reader_redundant min.1 ordered arity v early actual hj spec both)

#print axioms no_common
end CoLocalGate3825
