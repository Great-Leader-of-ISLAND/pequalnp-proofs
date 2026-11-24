import PEqualNP.CoAlarmWire1481

namespace CoAlarmRecurrence1481
open PEqualNP.CircuitLowerBounds CoAlarmWire1481 CoFormula1963Circuit

-- Generic fold and prefix lemmas adapted from Gabriel Alain, L-meta-4127, PR 8464.
def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def wire (gs : List Gate) (w : List Pair) (i : Nat) : Pair :=
  (fd jetStep gs w).getD i (false,false)

theorem earlier (gs : List Gate) (w : List Pair) (i : Nat) (hi : i<w.length) :
    wire gs w i=w.getD i (false,false) := fd_keep jetStep (false,false) gs w i hi

theorem recurs (gs : List Gate) (w : List Pair) (k : Nat) (hk : k<gs.length)
    (a b : Nat) (pins : gs[k].inputs=[a,b]) (ua : a<w.length+k) (ub : b<w.length+k) :
    wire gs w (w.length+k)=product (andFlag gs[k].op) (wire gs w a) (wire gs w b) := by
  have step := fd_gate jetStep (false,false) gs w k hk
  change _ = jetStep (fd jetStep (gs.take k) w) gs[k] at step
  unfold wire
  rw [step]
  simp only [jetStep,pins,List.getD_cons_zero,List.getD_cons_succ]
  rw [fd_take jetStep (false,false) gs w k a ua (Nat.le_of_lt hk),
      fd_take jetStep (false,false) gs w k b ub (Nat.le_of_lt hk)]

def rule (d : Bool) (ra rb da db : Bool) :=
    if d then ((ra && db) || (da && rb)) else (da || db)

theorem unique (gs : List Gate) (w : List Pair) (d : Nat → Bool)
    (start : ∀ i<w.length, d i=(w.getD i (false,false)).2)
    (legal : ∀ (k : Nat) (hk : k<gs.length),∃ a b : Nat,
      gs[k].inputs=[a,b] ∧ a<w.length+k ∧ b<w.length+k ∧
      d (w.length+k)=rule (andFlag gs[k].op) (wire gs w a).1 (wire gs w b).1 (d a) (d b)) :
    ∀ i, i<w.length+gs.length → d i=(wire gs w i).2 := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases raw : i<w.length
    · rw [earlier gs w i raw]
      exact start i raw
    · let k := i-w.length
      have idx : w.length+k=i := by dsimp [k];omega
      have hk : k<gs.length := by omega
      obtain ⟨a,b,pins,ha,hb,law⟩ := legal k hk
      have aa := ih a (by omega) (by omega)
      have bb := ih b (by omega) (by omega)
      have eq := recurs gs w k hk a b pins ha hb
      rw [←idx,eq,law,aa,bb]
      cases h : andFlag gs[k].op <;> rfl

theorem values (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (binary : ∀ g∈C.gates, ∃ a b : Nat,g.inputs=[a,b]) (row : X → Bool) (v : X) (i : Nat) :
    (wire C.gates (initial.map (info row v)) i).1=(C.wires (input row)).getD i false := by
  have start : ∀ t∈initial,clean t := by simp [initial,clean,List.mem_ofFn]
  let obs := initial.map (info row v)
  have hs : (advance C.gates obs).map Prod.fst=(C.wires (input row)) := by
    dsimp only [obs]
    rw [←trace_info row v C.gates binary initial start,List.map_map]
    change (run C.gates initial).map (val row)=C.wires (input row)
    rw [run_value row C.gates initial (fun g hg => mono g hg),initial_val]
    rfl
  rw [←hs]
  exact (map_get Prod.fst (false,false) (advance C.gates obs) i).symm

#print axioms values
#print axioms unique
end CoAlarmRecurrence1481
