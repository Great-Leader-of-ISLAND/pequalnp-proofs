import PEqualNP.CoPortEngine4482
import PEqualNP.CoSwitch3302Neg

namespace CoPortSlice4482
open CoPortEngine4482 PEqualNP.CircuitLowerBounds
open CoSwitch3302.MonotoneWires3302

abbrev Input := Fin 9 → Bool
def graph (x : Input) : Bool :=
  ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun n =>
    x (Fin.ofNat 9 (n/10)) && x (Fin.ofNat 9 (n%10))

def sameOn (b : Nat) (x y : Input) := ∀ i : Fin 9, b.testBit i.val = true → x i = y i
def leInput (x y : Input) := ∀ i : Fin 9, x i = true → y i = true
def decides (b : Nat) (w : Input → Bool) :=
  ∀ x y, sameOn b x y → w x = w y → graph x = graph y

/-- A monotone scalar that separates a fixed observed-raw slice must point
    from false to true on every pair of ordered opposite-labeled inputs. -/
theorem forced {b : Nat} {w : Input → Bool}
    (mono : ∀ x y, leInput x y → w x = true → w y = true) (det : decides b w)
    {lo hi} (same : sameOn b lo hi) (ge : leInput lo hi)
    (no : graph lo = false) (yes : graph hi = true) : w lo = false ∧ w hi = true := by
  have ne : w lo ≠ w hi := by
    intro eq
    have bad := det lo hi same eq
    rw [no,yes] at bad
    contradiction
  have order := mono lo hi ge
  cases l : w lo <;> cases h : w hi <;> simp_all

def low (b : Nat) (x : Input) : Input := fun i => b.testBit i.val && x i
def high (b : Nat) (x : Input) : Input := fun i => !(b.testBit i.val) || x i

theorem force_pos {b w} (mono : ∀ x y, leInput x y → w x = true → w y = true)
    (det : decides b w) (x : Input) (no : graph (low b x) = false) (yes : graph x = true) :
    w x = true :=
  (forced mono det (lo:=low b x) (hi:=x) (by intro i h; simp [low,h])
    (by intro i h; exact (Bool.and_eq_true_iff.mp h).2) no yes).2

theorem force_neg {b w} (mono : ∀ x y, leInput x y → w x = true → w y = true)
    (det : decides b w) (x : Input) (no : graph x = false) (yes : graph (high b x) = true) :
    w x = false :=
  (forced mono det (lo:=x) (hi:=high b x) (by intro i h; simp [high,h])
    (by intro i h; simp [high,h]) no yes).1

def head : Gate := ⟨.or,[0,2]⟩
def whole (gs : List Gate) : Circuit := ⟨head::gs,0⟩
def wires (xs : Fin 9 → Sig) : List Sig := List.ofFn xs ++ [bin true (xs 0) (xs 2)]
def row (xs : Fin 9 → Sig) (s : Bool) (i : Fin 160) : Input := fun j => bit s i (xs j)
def reject (ws : List Sig) : Bool :=
  if ws.length≤8 ∧ unionSep false ws=top then !(search 7 0 ws) else true
def check (xs : Fin 9 → Sig) : Bool := (wires xs).sublists.all reject

theorem no_target (xs : Fin 9 → Sig) (hn : (wires xs).Nodup) (chk : check xs = true)
    (gs : List Gate) (len : gs.length ≤ 7)
    (legal : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    target ∉ execute gs (wires xs) := by
  intro mem
  have valid (g) (hg : g ∈ gs) : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal g hg
  obtain ⟨k,S,hk,live,sub⟩ := extract gs (wires xs) valid mem
  let ws := (wires xs).filter fun z => decide (z∈S)
  have sl : ws.Sublist (wires xs) := List.filter_sublist
  have nodup := hn.sublist sl
  have same : ws.toFinset=S := by
    ext z
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun hz => ⟨sub z hz,hz⟩⟩
  have bound := (live_size live).2
  have card : S.card=ws.length := by rw [←same,List.toFinset_card_of_nodup nodup]
  have width : ws.length≤8 := by omega
  have cov : unionSep false ws=top := by simpa using live_cover live same
  have found := search_complete (unrestricted live) 7 (by omega) ws nodup same
  have bad := List.all_eq_true.mp chk ws (List.mem_sublists.mpr sl)
  simp [reject,width,cov,found] at bad

theorem no_decision (b : Nat) (xs : Fin 9 → Sig) (hn : (wires xs).Nodup) (chk : check xs = true)
    (pos : ∀ i, graph (low b (row xs true i)) = false ∧ graph (row xs true i) = true)
    (neg : ∀ i, graph (row xs false i) = false ∧ graph (high b (row xs false i)) = true)
    (gs : List Gate) (len : gs.length≤7)
    (legal : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) (z : Nat) :
    ¬decides b (fun x => value (whole gs) x z) := by
  intro det
  have ao : AO (whole gs) := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl|m
    · exact ⟨Or.inr rfl,by decide⟩
    · exact legal g m
  have monot (x y : Input) (le : leInput x y) := wires_mono (whole gs) ao x y le z
  have valid (g) (hg : g∈gs) : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    exact (legal g hg).1.elim Or.inl (fun v => Or.inr (Or.inl v))
  let out := (execute gs (wires xs)).getD z zero
  have value_eq (s : Bool) (i : Fin 160) :
      bit s i out = value (whole gs) (row xs s i) z := by
    rw [show bit s i out = ((execute gs (wires xs)).map (bit s i)).getD z false from (b_read _ _ _ _).symm]
    rw [execute_bits gs s i (wires xs) valid]
    have wh : (wires xs).map (bit s i) = List.ofFn (row xs s i) ++
        [(row xs s i) 0 || (row xs s i) 2] := by
      simp [wires,row,bit_bin]
    rw [wh]
    let x := row xs s i
    have head_eq : head.op.eval (head.inputs.map fun j => (List.ofFn x).getD j false) =
        (x 0 || x 2) := by simp [head,GateOp.eval]
    change _ = (gs.foldl _ (List.ofFn x ++ [head.op.eval
      (head.inputs.map fun j => (List.ofFn x).getD j false)])).getD z false
    rw [head_eq]
  have up (i : Fin 160) : bit true i out = true := (value_eq _ _).trans
    (force_pos monot det _ (pos i).1 (pos i).2)
  have down (i : Fin 160) : bit false i out = false := (value_eq _ _).trans
    (force_neg monot det _ (neg i).1 (neg i).2)
  have eq : out = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have h := up ⟨i,hi⟩
      change out.1.getLsbD i = true at h
      change _ = (BitVec.allOnes _).getLsbD i
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using h
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simpa [bit,target] using down ⟨i,hi⟩
  have ok := get_rep (execute gs (wires xs)) z
  change out∈_ ∨ ¬proper out at ok
  rw [eq] at ok
  exact no_target xs hn chk gs len legal (ok.resolve_right (fun h => h target_proper))

end CoPortSlice4482
