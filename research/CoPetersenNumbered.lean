import PEqualNP.CoPetersenCnf

namespace PEqualNP.Research.PetersenNumbered
open PEqualNP.Research.PetersenRaw
open PEqualNP.Research.PetersenCnf
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

inductive Field where
  | op (i : ℕ)
  | pin (right : Bool) (i : ℕ)
  | aux (right : Bool) (i : ℕ)
  | finalPick (i : ℕ)
  | finalAux (i : ℕ)
  | cell (z c : ℕ)
  deriving DecidableEq, Repr

abbrev Sheet := Field → Bool
abbrev Book := ℕ → Sheet

def readBits {r : ℕ} (m : ℕ) (b : Sheet) : Bits m r where
  op := fun i => b (.op i.val)
  left := fun i => b (.pin false i.val)
  right := fun i => b (.pin true i.val)
  aval := fun z => b (.cell z.val 0)
  bval := fun z => b (.cell z.val 1)
  out := fun z => b (.cell z.val 2)

def pinPre {m : ℕ} (b : Sheet) (side : Bool) (i : Pin m) : Bool :=
  if i.val = 0 then b (.pin side i.val) else b (.aux side i.val)

def outPre {m : ℕ} (b : Sheet) (i : Fin (m+1)) : Bool :=
  if i.val = 0 then b (.finalPick i.val) else b (.finalAux i.val)

def gateOK {r : ℕ} (s : List (Sig r)) (b : Sheet) : Prop :=
  let v : Bits s.length r := readBits s.length b
  oneHot v.op ∧ holds [!(v.op 2),v.right (missing s.length)] ∧
  cumulative v.left (pinPre b false) ∧ cumulative v.right (pinPre b true) ∧
  (∀ i : Pin s.length, holds [!(pinPre b true i),pinPre b false i]) ∧
  ∀ z, muxOK v.left (fun p => readPin (row s z) (v.op 0) p) (v.aval z) ∧
       muxOK v.right (fun p => readPin (row s z) (v.op 0) p) (v.bval z) ∧
       truthClauses (v.op 0) (v.op 1) (v.op 2) (v.aval z) (v.bval z) (v.out z)

def finalOK {r : ℕ} (s : List (Sig r)) (t : Sig r) (b : Sheet) : Prop :=
  cumulative (fun i : Fin (s.length+1) => b (.finalPick i.val)) (outPre b) ∧
  ∀ z (i : Fin (s.length+1)), holds [!(b (.finalPick i.val)),
    if t z then (row s z).getD i.val false else !((row s z).getD i.val false)]

def chart {r : ℕ} : ℕ → List (Sig r) → Sig r → Book → Prop
  | 0, s, t, b => finalOK s t (b 0)
  | k+1, s, t, b => gateOK s (b 0) ∧
    chart k (s ++ [fun z => b 0 (.cell z.val 2)]) t (fun i => b (i+1))

def total {n : ℕ} (f : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n then f ⟨i,h⟩ else false

@[simp] theorem total_fin {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    total f i.val = f i := by simp [total, i.isLt]

def gateSheet {m r : ℕ} (v : Bits m r) (pl pr : Pin m → Bool) : Sheet
  | .op i => total v.op i
  | .pin false i => total v.left i
  | .pin true i => total v.right i
  | .aux false i => total pl i
  | .aux true i => total pr i
  | .cell z 0 => total v.aval z
  | .cell z 1 => total v.bval z
  | .cell z _ => total v.out z
  | _ => false

private theorem read_gateSheet {m r : ℕ} (v : Bits m r) (pl pr : Pin m → Bool) :
    readBits m (gateSheet v pl pr) = v := by
  cases v
  simp [readBits, gateSheet]

private theorem cumulative_alias {n : ℕ} (pick pre : Fin n → Bool) (h : cumulative pick pre) :
    (fun i => if i.val = 0 then pick i else pre i) = pre := by
  funext i
  by_cases hi : i.val = 0
  · simpa [hi] using (h.1 i hi).symm
  · simp [hi]

private theorem buildGate {r : ℕ} (s : List (Sig r)) (v : Bits s.length r)
    (hp : prefixStruct v) (hz : ∀ z,
      muxOK v.left (fun p => readPin (row s z) (v.op 0) p) (v.aval z) ∧
      muxOK v.right (fun p => readPin (row s z) (v.op 0) p) (v.bval z) ∧
      truthClauses (v.op 0) (v.op 1) (v.op 2) (v.aval z) (v.bval z) (v.out z)) :
    ∃ b : Sheet, gateOK s b ∧ (fun z : Fin r => b (.cell z.val 2)) = v.out := by
  obtain ⟨hop, hn, pl, pr, lc, rc, ord⟩ := hp
  let b := gateSheet v pl pr
  have hl : @pinPre s.length b false = pl := by
    simpa [pinPre, b, gateSheet] using cumulative_alias v.left pl lc
  have hr : @pinPre s.length b true = pr := by
    simpa [pinPre, b, gateSheet] using cumulative_alias v.right pr rc
  refine ⟨b, ?_, ?_⟩
  · unfold gateOK
    dsimp only
    rw [show readBits s.length b = v from read_gateSheet _ _ _, hl, hr]
    exact ⟨hop, hn, lc, rc, ord, hz⟩
  · funext z
    simp [b, gateSheet]

def finalSheet {n : ℕ} (pick pre : Fin n → Bool) : Sheet
  | .finalPick i => total pick i
  | .finalAux i => total pre i
  | _ => false

theorem chart_of_prefix {r : ℕ} (k : ℕ) (s : List (Sig r)) (t : Sig r) (h : PrefixSat k s t) :
    ∃ b : Book, chart k s t b := by
  induction k generalizing s with
  | zero =>
    obtain ⟨f,p,hc,hz⟩ := h
    let b := finalSheet f p
    have hpre : @outPre s.length b = p := by
      simpa [outPre, b, finalSheet] using cumulative_alias f p hc
    refine ⟨fun _ => b, ?_⟩
    change finalOK s t b
    unfold finalOK
    rw [hpre]
    simpa [b, finalSheet] using And.intro hc hz
  | succ k ih =>
    obtain ⟨v,hp,hz,rest⟩ := h
    obtain ⟨b,hb,hout⟩ := buildGate s v hp hz
    obtain ⟨tail,ht⟩ := ih _ rest
    let book : Book := fun i => match i with | 0 => b | j+1 => tail j
    refine ⟨book, hb, ?_⟩
    change chart k (s ++ [fun z => b (.cell z.val 2)]) t tail
    rw [hout]
    exact ht

-- The static arrays follow Python raw Encoding.__init__ in allocation order.
-- Prefix position zero aliases the first choice. The true literal is ID 1.
def gateFields (j : ℕ) : List Field :=
  let pins := List.range (12+j)
  let aux := pins.filter (fun i => decide (i ≠ 0))
  (List.range 3).map Field.op ++ pins.map (.pin false) ++ aux.map (.aux false) ++
    pins.map (.pin true) ++ aux.map (.aux true)

def finalFields : List Field :=
  (List.range 25).map Field.finalPick ++
    ((List.range 25).filter (fun i => decide (i ≠ 0))).map Field.finalAux

def staticNames : List (ℕ × Field) :=
  (List.range 14).flatMap (fun j => (gateFields j).map (fun f => (j,f))) ++
    finalFields.map (fun f => (14,f))

def slot {α : Type} [DecidableEq α] (x : α) : List α → ℕ
  | [] => 0
  | y :: ys => if x = y then 0 else slot x ys + 1

private theorem slot_hit {α : Type} [DecidableEq α] (x : α) (xs : List α) (hx : x ∈ xs) :
    slot x xs < xs.length ∧ xs[slot x xs]? = some x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    by_cases he : x = y
    · subst y
      simp [slot]
    · have hy := (List.mem_cons.mp hx).resolve_left he
      obtain ⟨hl, hv⟩ := ih hy
      simp [slot, he, hl, hv]

def rowBase : ℕ := 2 + staticNames.length

def address (j : ℕ) (f : Field) : ℕ :=
  match f with
  | .cell z c => rowBase + 42*z + 3*j + c
  | _ => 2 + slot (j,f) staticNames

-- IDs after the static arrays are in Python add_row order: row, gate, then
-- left mux / right mux / output. Only this final region grows with the rows.
def assignment (b : Book) (i : ℕ) : Bool :=
  if i = 1 then true else if i < rowBase then
    match staticNames[i-2]? with
    | some (j,f) => b j f
    | none => false
  else
    let u := i-rowBase
    b ((u % 42)/3) (.cell (u/42) (u%3))

private theorem static_read (b : Book) (j : ℕ) (f : Field) (h : (j,f) ∈ staticNames)
    (hf : ∀ z c, f ≠ .cell z c) : assignment b (address j f) = b j f := by
  have ha : address j f = 2 + slot (j,f) staticNames := by
    cases f <;> first | rfl | exact False.elim (hf _ _ rfl)
  obtain ⟨hlt,hh⟩ := slot_hit _ _ h
  have h1 : 2 + slot (j,f) staticNames ≠ 1 := by omega
  have hbase : 2 + slot (j,f) staticNames < rowBase := by unfold rowBase; omega
  have hm : 2 + slot (j,f) staticNames - 2 = slot (j,f) staticNames := by omega
  simp [assignment, ha, h1, hbase, hm, hh]

private theorem cell_read (b : Book) (j z c : ℕ) (hj : j < 14) (hc : c < 3) :
    assignment b (address j (.cell z c)) = b j (.cell z c) := by
  have hbase : 2 ≤ rowBase := by unfold rowBase; omega
  have h1 : rowBase + 42*z + 3*j + c ≠ 1 := by omega
  have hb : ¬rowBase + 42*z + 3*j + c < rowBase := by omega
  have hm : rowBase + 42*z + 3*j + c - rowBase = 42*z + 3*j + c := by omega
  have hj' : ((42*z + 3*j + c) % 42) / 3 = j := by omega
  have hz' : (42*z + 3*j + c) / 42 = z := by omega
  have hc' : (42*z + 3*j + c) % 3 = c := by omega
  simp [assignment, address, h1, hb, hm, hj', hz', hc']

private theorem gate_mem (j : ℕ) (hj : j < 14) (f : Field) (h : f ∈ gateFields j) :
    (j,f) ∈ staticNames := by
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,List.mem_map.mpr ⟨f,h,rfl⟩⟩

private theorem final_mem (f : Field) (h : f ∈ finalFields) : (14,f) ∈ staticNames := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨f,h,rfl⟩

def numBook (v : ℕ → Bool) : Book := fun j f => v (address j f)

private theorem op_read (b : Book) (j : ℕ) (hj : j < 14) (i : Fin 3) :
    numBook (assignment b) j (.op i.val) = b j (.op i.val) := by
  apply static_read b j _ (gate_mem j hj _ ?_) (by intros; contradiction)
  simp [gateFields, i.isLt]

private theorem pin_read (b : Book) {j m : ℕ} (hj : j < 14) (hm : m=10+j)
    (side : Bool) (i : Pin m) :
    numBook (assignment b) j (.pin side i.val) = b j (.pin side i.val) := by
  have hi := i.isLt
  have hb : i.val < 12+j := by omega
  apply static_read b j _ (gate_mem j hj _ ?_) (by intros; contradiction)
  cases side <;> simp [gateFields, hb]

private theorem aux_read (b : Book) {j m : ℕ} (hj : j < 14) (hm : m=10+j)
    (side : Bool) (i : Pin m) (hi : i.val ≠ 0) :
    numBook (assignment b) j (.aux side i.val) = b j (.aux side i.val) := by
  have hh := i.isLt
  have hb : i.val < 12+j := by omega
  apply static_read b j _ (gate_mem j hj _ ?_) (by intros; contradiction)
  cases side <;> simp [gateFields, hb, hi]

private theorem pre_read (b : Book) {j m : ℕ} (hj : j < 14) (hm : m=10+j)
    (side : Bool) :
    @pinPre m (numBook (assignment b) j) side = @pinPre m (b j) side := by
  funext i
  by_cases hi : i.val = 0
  · simpa only [pinPre, hi, if_true] using pin_read b hj hm side i
  · simpa only [pinPre, hi, if_false] using aux_read b hj hm side i hi

private theorem bits_read {r : ℕ} (b : Book) {j m : ℕ} (hj : j < 14) (hm : m=10+j) :
    @readBits r m (numBook (assignment b) j) = readBits m (b j) := by
  unfold readBits
  congr 1 <;> funext u
  · exact op_read b j hj u
  · exact pin_read b hj hm false u
  · exact pin_read b hj hm true u
  · exact cell_read b j u.val 0 hj (by decide)
  · exact cell_read b j u.val 1 hj (by decide)
  · exact cell_read b j u.val 2 hj (by decide)

private theorem gate_read {r : ℕ} (b : Book) {j : ℕ} (s : List (Sig r))
    (hj : j < 14) (hm : s.length=10+j) :
    gateOK s (numBook (assignment b) j) ↔ gateOK s (b j) := by
  unfold gateOK
  dsimp only
  rw [bits_read b hj hm, pre_read b hj hm false, pre_read b hj hm true]

private theorem finalPick_read (b : Book) {m : ℕ} (hm : m=24) (i : Fin (m+1)) :
    numBook (assignment b) 14 (.finalPick i.val) = b 14 (.finalPick i.val) := by
  have hh := i.isLt
  have hb : i.val < 25 := by omega
  apply static_read b 14 _ (final_mem _ ?_) (by intros; contradiction)
  simp [finalFields, hb]

private theorem finalAux_read (b : Book) {m : ℕ} (hm : m=24) (i : Fin (m+1)) (hi : i.val≠0) :
    numBook (assignment b) 14 (.finalAux i.val) = b 14 (.finalAux i.val) := by
  have hh := i.isLt
  have hb : i.val < 25 := by omega
  apply static_read b 14 _ (final_mem _ ?_) (by intros; contradiction)
  simp [finalFields, hb, hi]

private theorem final_read {r : ℕ} (b : Book) (s : List (Sig r)) (t : Sig r)
    (hm : s.length=24) :
    finalOK s t (numBook (assignment b) 14) ↔ finalOK s t (b 14) := by
  have hp : @outPre s.length (numBook (assignment b) 14) = @outPre s.length (b 14) := by
    funext i
    by_cases hi : i.val = 0
    · simpa only [outPre, hi, if_true] using finalPick_read b hm i
    · simpa only [outPre, hi, if_false] using finalAux_read b hm i hi
  unfold finalOK
  simp only [hp, finalPick_read b hm]

private theorem shift (b : Book) (j : ℕ) :
    (fun i => b (j+(i+1))) = (fun i => b ((j+1)+i)) := by
  funext i
  have h : j+(i+1)=(j+1)+i := by omega
  rw [h]

private theorem numbered_chart {r : ℕ} (b : Book) (k j : ℕ) (s : List (Sig r)) (t : Sig r)
    (hj : j+k=14) (hm : s.length=10+j) (h : chart k s t (fun i => b (j+i))) :
    chart k s t (fun i => numBook (assignment b) (j+i)) := by
  induction k generalizing s j with
  | zero =>
    have he : j=14 := by omega
    subst j
    exact (final_read b s t (by omega)).mpr h
  | succ k ih =>
    have hlt : j<14 := by omega
    obtain ⟨hg,ht⟩ := h
    refine ⟨(gate_read b s hlt hm).mpr hg, ?_⟩
    have hout : (fun z : Fin r => numBook (assignment b) j (.cell z.val 2)) =
        (fun z : Fin r => b j (.cell z.val 2)) := by
      funext z
      exact cell_read b j z.val 2 hlt (by decide)
    change chart k (s ++ [fun z : Fin r => numBook (assignment b) j (.cell z.val 2)]) t
      (fun i => numBook (assignment b) (j+(i+1)))
    rw [hout, shift]
    apply ih (j := j+1)
    · omega
    · simp only [List.length_append, List.length_singleton]
      omega
    · simpa only [shift] using ht

-- Only ordinary Nat-indexed Boolean variables remain free. rowBase is 1101;
-- the 14 local blocks account for IDs 2..1051 and output selection for
-- IDs 1052..1100. Semantics is independent of which finite input rows are used.
def NumberedSat {r : ℕ} (s : List (Sig r)) (t : Sig r) (v : ℕ → Bool) : Prop :=
  v 1 = true ∧ chart 14 s t (numBook v)

theorem numbered_of_prefix {r : ℕ} (s : List (Sig r)) (t : Sig r) (hm : s.length=10)
    (h : PrefixSat 14 s t) : ∃ v : ℕ → Bool, NumberedSat s t v := by
  obtain ⟨b,hb⟩ := chart_of_prefix _ _ _ h
  refine ⟨assignment b, by simp [assignment], ?_⟩
  have h0 : (fun i => b (0+i)) = b := by simp
  have hinit : chart 14 s t (fun i => b (0+i)) := by rw [h0]; exact hb
  simpa only [Nat.zero_add] using numbered_chart b 14 0 s t (by decide) (by simpa using hm) hinit

theorem raw_numbered_model {r : ℕ} (s : List (Sig r)) (t : Sig r) (hm : s.length=10) (D : Circuit)
    (hfan : FanInTwo D) (hsize : D.size≤14) (hrows : ∀ z, D.eval (row s z)=t z) :
    ∃ v : ℕ → Bool, NumberedSat s t v :=
  numbered_of_prefix s t hm (raw_prefix_model _ _ _ D hfan hsize hrows)

theorem of_numbered_exclusion {r : ℕ} (xs : Fin r → Fin 9 → Bool) (head f : (Fin 9 → Bool) → Bool)
    (no : ¬∃ v : ℕ → Bool, NumberedSat (initial xs head) (fun z => f (xs z)) v) :
    ∀ D : Circuit, FanInTwo D → D.size ≤ 14 → ∃ x, D.eval (List.ofFn x ++ [head x]) ≠ f x := by
  apply of_prefix_exclusion 14 xs head f
  intro h
  exact no (numbered_of_prefix _ _ (by simp [initial]) h)

end PEqualNP.Research.PetersenNumbered
