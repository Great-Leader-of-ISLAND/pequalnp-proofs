import PEqualNP.CoPetersenFormula

namespace PEqualNP.Research.PetersenFast
open PEqualNP.Research.PetersenRaw
open PEqualNP.Research.PetersenCnf
open PEqualNP.Research.PetersenNumbered
open PEqualNP.Research.PetersenDimacs
open PEqualNP.Research.PetersenFormula

-- Fourteen gate blocks start at 2, 51, 104, ... . The width of block j
-- is 49+4*j. Output choice flags start at 1052, row cells at 1101.
def gateBase (j : ℕ) := 2 + 47*j + 2*j*j

def supported (j : ℕ) : Field → Bool
  | .op i => decide (j < 14 ∧ i < 3)
  | .pin _ i => decide (j < 14 ∧ i < 12+j)
  | .aux _ i => decide (j < 14 ∧ i < 12+j ∧ i ≠ 0)
  | .finalPick i => decide (j = 14 ∧ i < 25)
  | .finalAux i => decide (j = 14 ∧ i < 25 ∧ i ≠ 0)
  | .cell _ _ => false

def staticCalc (j : ℕ) : Field → ℕ
  | .op i => gateBase j + i
  | .pin false i => gateBase j + 3 + i
  | .aux false i => gateBase j + 2 + (12+j) + i
  | .pin true i => gateBase j + 2 + 2*(12+j) + i
  | .aux true i => gateBase j + 1 + 3*(12+j) + i
  | .finalPick i => 1052 + i
  | .finalAux i => 1076 + i
  | .cell _ _ => 1101

def fastAddress (j : ℕ) (f : Field) : ℕ :=
  match f with
  | .cell z c => 1101 + 42*z + 3*j + c
  | _ => if supported j f then staticCalc j f else 1101

private theorem gateMember (j : ℕ) (hj : j < 14) (f : Field) (hf : f ∈ gateFields j) :
    (j,f) ∈ staticNames := by
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,List.mem_map.mpr ⟨f,hf,rfl⟩⟩

private theorem lastMember (f : Field) (hf : f ∈ finalFields) : (14,f) ∈ staticNames := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨f,hf,rfl⟩

private theorem supported_mem (j : ℕ) (f : Field) (h : supported j f = true) :
    (j,f) ∈ staticNames := by
  cases f with
  | op i =>
    obtain ⟨hj,hi⟩ := of_decide_eq_true h
    exact gateMember j hj _ (by simp [gateFields,hi])
  | pin side i =>
    obtain ⟨hj,hi⟩ := of_decide_eq_true h
    apply gateMember j hj
    cases side <;> simp [gateFields,hi]
  | aux side i =>
    obtain ⟨hj,hi,h0⟩ := of_decide_eq_true h
    apply gateMember j hj
    cases side <;> simp [gateFields,hi,h0]
  | finalPick i =>
    obtain ⟨hj,hi⟩ := of_decide_eq_true h
    subst j
    exact lastMember _ (by simp [finalFields,hi])
  | finalAux i =>
    obtain ⟨hj,hi,h0⟩ := of_decide_eq_true h
    subst j
    exact lastMember _ (by simp [finalFields,hi,h0])
  | cell z c => contradiction

-- The finite certificate compares each field to its expected physical ID,
-- once, without performing the original repeated linear searches.
def consecutive : ℕ → List (ℕ × Field) → Bool
  | _, [] => true
  | n, (j,f) :: rest => decide (fastAddress j f = n) && consecutive (n+1) rest

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
private theorem all_named_correct : consecutive 2 staticNames = true := by decide

set_option maxRecDepth 12000 in
private theorem count_named : staticNames.length = 1099 := by decide

private theorem from_consecutive (xs : List (ℕ × Field)) (n : ℕ) (h : consecutive n xs = true)
    (x : ℕ × Field) (hx : x ∈ xs) : fastAddress x.1 x.2 = n + slot x xs := by
  induction xs generalizing n with
  | nil => simp at hx
  | cons y ys ih =>
    obtain ⟨j,f⟩ := y
    obtain ⟨hhead,hrest⟩ := Bool.and_eq_true_iff.mp h
    by_cases he : x = (j,f)
    · subst x
      simpa [slot] using of_decide_eq_true hhead
    · have htail := (List.mem_cons.mp hx).resolve_left he
      have hh := ih (n+1) hrest htail
      simp only [slot,he,if_false]
      omega

private theorem slot_absent {α : Type} [DecidableEq α] (x : α) (xs : List α) (hx : x ∉ xs) :
    slot x xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    have hne : x ≠ y := fun h => hx (List.mem_cons.mpr (Or.inl h))
    have ht : x ∉ ys := fun h => hx (List.mem_cons.mpr (Or.inr h))
    simp [slot,hne,ih ht]

private theorem static_fast (j : ℕ) (f : Field) (hc : ∀ z c, f ≠ .cell z c) :
    fastAddress j f = address j f := by
  have ha : address j f = 2 + slot (j,f) staticNames := by
    cases f <;> first | rfl | exact False.elim (hc _ _ rfl)
  rw [ha]
  by_cases hm : (j,f) ∈ staticNames
  · exact from_consecutive _ _ all_named_correct (j,f) hm
  · have hs : supported j f = false := by
      cases he : supported j f with
      | false => rfl
      | true => exact False.elim (hm (supported_mem j f he))
    have he : fastAddress j f = 1101 := by
      cases f <;> first | exact False.elim (hc _ _ rfl) | simp only [fastAddress,hs,Bool.false_eq_true,if_false]
    rw [he,slot_absent _ _ hm,count_named]

theorem fastAddress_eq (j : ℕ) (f : Field) : fastAddress j f = address j f := by
  cases f with
  | cell z c => simp [fastAddress,address,rowBase,count_named]
  | _ => exact static_fast j _ (by intro z c h; cases h)

-- The list primitives and the Tseitin templates are precisely the originals.
-- Only lookups through bit have new implementations; registering a compiler
-- rewrite alone would leave the already-compiled imported emitter unchanged.
def fbit (j : ℕ) (f : Field) := pos (fastAddress j f)
def fop (j : ℕ) (i : Fin 3) := fbit j (.op i.val)
def fpin {m : ℕ} (j : ℕ) (side : Bool) (i : Pin m) := fbit j (.pin side i.val)
def fpre {m : ℕ} (j : ℕ) (side : Bool) (i : Pin m) :=
  if i.val=0 then fpin j side i else fbit j (.aux side i.val)
def ffp {m : ℕ} (j : ℕ) (i : Fin (m+1)) := fbit j (.finalPick i.val)
def ffq {m : ℕ} (j : ℕ) (i : Fin (m+1)) :=
  if i.val=0 then ffp j i else fbit j (.finalAux i.val)
def fcell (j : ℕ) {r : ℕ} (z : Fin r) (c : ℕ) := fbit j (.cell z.val c)

def fopLines (j : ℕ) : CNF :=
  let a:=fop j 0
  let o:=fop j 1
  let n:=fop j 2
  [[a,o,n],[neg a,neg o],[neg a,neg n],[neg o,neg n]]
def fstatic (j m : ℕ) : CNF :=
  fopLines j ++ cumLines (@fpin m j false) (fpre j false) ++
    cumLines (@fpin m j true) (fpre j true) ++ [[neg (fop j 2),fpin j true (missing m)]] ++
    allFin (fun i : Pin m => [[neg (fpre j true i),fpre j false i]])
def foperand {r : ℕ} (j : ℕ) (s : List (Col r)) (z : Fin r) (i : Pin s.length) :=
  if i.val=s.length+1 then fop j 0 else wire s z i.val
def fgateRow {r : ℕ} (j : ℕ) (s : List (Col r)) (z : Fin r) : CNF :=
  muxLines (@fpin s.length j false) (foperand j s z) (fcell j z 0) ++
  muxLines (@fpin s.length j true) (foperand j s z) (fcell j z 1) ++
  truthLines (fop j 0) (fop j 1) (fop j 2) (fcell j z 0) (fcell j z 1) (fcell j z 2)
def flastRow {r : ℕ} (j : ℕ) (s : List (Col r)) (t : Sig r) (z : Fin r) : CNF :=
  allFin (fun i : Fin (s.length+1) =>
      [[neg (ffp j i),if t z then wire s z i.val else neg (wire s z i.val)]])
def femit {r : ℕ} : ℕ → ℕ → List (Col r) → Sig r → Parts r
  | 0, j, s, t => ⟨cumLines (@ffp s.length j) (ffq j),flastRow j s t⟩
  | k+1, j, s, t =>
    let after := femit k (j+1) (s++[fun z => fcell j z 2]) t
    ⟨fstatic j s.length ++ after.static,fun z => fgateRow j s z ++ after.rows z⟩

private theorem fbit_eq : fbit = bit := by
  funext j f
  simp [fbit,bit,fastAddress_eq]

theorem femit_eq {r : ℕ} (k j : ℕ) (s : List (Col r)) (t : Sig r) :
    femit k j s t = emit k j s t := by
  induction k generalizing j s with
  | zero =>
    simp only [femit,emit,flastRow,lastRow,ffq,fq,ffp,fp,fbit_eq]
  | succ k ih =>
    simp only [femit,emit,fstatic,structureLines,fopLines,opLines,fgateRow,gateRow,
      foperand,operand,fcell,cell,fpre,pref,fpin,pin,fop,op,fbit_eq,ih]

def fastDimacs35 : List (List Int) :=
  let p := femit 14 0 columns labels
  let f := [[pos 1]] ++ (p.static ++ allFin p.rows).filterMap (eraseConstant 1)
  f.map (List.map asInteger)

theorem fastDimacs35_eq : fastDimacs35 = dimacs35 := by
  simp only [fastDimacs35,dimacs35,raw35,ground,body,femit_eq]

end PEqualNP.Research.PetersenFast
