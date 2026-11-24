import PEqualNP.CoPetersenNumbered
import PEqualNP.CoPetersenDimacs

namespace PEqualNP.Research.PetersenFormula
open PEqualNP.Research.PetersenRaw
open PEqualNP.Research.PetersenCnf
open PEqualNP.Research.PetersenNumbered
open PEqualNP.Research.PetersenDimacs
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

abbrev CNF := List (List SignedVar)
abbrev Col (r : ℕ) := Fin r → SignedVar

def pos (i : ℕ) : SignedVar := (i,true)
def neg (l : SignedVar) : SignedVar := (l.1,!l.2)
def constLit (b : Bool) : SignedVar := (1,b)

@[simp] theorem eval_pos (v : ℕ → Bool) (i : ℕ) : literalValue v (pos i) = v i := rfl
@[simp] theorem eval_neg (v : ℕ → Bool) (l : SignedVar) : literalValue v (neg l) = !(literalValue v l) := by
  obtain ⟨i,b⟩ := l
  cases b <;> simp [neg, literalValue]
@[simp] theorem eval_const (v : ℕ → Bool) (hv : v 1 = true) (b : Bool) :
    literalValue v (constLit b) = b := by cases b <;> simp [literalValue, constLit, hv]

def Models (v : ℕ → Bool) (cs : CNF) : Prop := ∀ c ∈ cs, clauseTrue v c
def allFin {n : ℕ} (f : Fin n → CNF) : CNF := (List.finRange n).flatMap f

@[simp] theorem models_nil (v : ℕ → Bool) : Models v [] := by simp [Models]
@[simp] theorem models_cons (v : ℕ → Bool) (c : List SignedVar) (cs : CNF) :
    Models v (c :: cs) ↔ clauseTrue v c ∧ Models v cs := by
  constructor
  · intro h
    exact ⟨h _ (by simp), fun u hu => h u (by simp [hu])⟩
  · rintro ⟨h,hs⟩ u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h
    · exact hs u hu

@[simp] theorem models_append (v : ℕ → Bool) (a b : CNF) :
    Models v (a++b) ↔ Models v a ∧ Models v b := by
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left _ hc), fun c hc => h c (List.mem_append_right _ hc)⟩
  · rintro ⟨ha,hb⟩ c hc
    exact (List.mem_append.mp hc).elim (ha c) (hb c)

@[simp] theorem models_allFin {n : ℕ} (v : ℕ → Bool) (f : Fin n → CNF) :
    Models v (allFin f) ↔ ∀ i, Models v (f i) := by
  constructor
  · intro h i c hc
    exact h c (List.mem_flatMap.mpr ⟨i,by simp,hc⟩)
  · intro h c hc
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hc
    exact h i c hi

theorem clause_iff (v : ℕ → Bool) (c : List SignedVar) :
    clauseTrue v c ↔ holds (c.map (literalValue v)) := by
  simp [clauseTrue, holds, List.mem_map]

def cumFour (a x h : SignedVar) : CNF := [[neg a,h],[neg x,h],[neg a,neg x],[neg h,a,x]]

def cumLines {n : ℕ} (pick pre : Fin (n+1) → SignedVar) : CNF :=
  allFin (fun i : Fin n => cumFour (pre i.castSucc) (pick i.succ) (pre i.succ)) ++ [[pre (Fin.last n)]]

theorem cumSound {n : ℕ} (v : ℕ → Bool) (pick pre : Fin (n+1) → SignedVar)
    (h : cumulative (fun i => literalValue v (pick i)) (fun i => literalValue v (pre i))) :
    Models v (cumLines pick pre) := by
  rw [cumLines, models_append, models_allFin]
  constructor
  · intro i
    have hh := h.2.2 i.castSucc i.succ rfl
    simpa only [cumFour, models_cons, models_nil, and_true, clause_iff,
      List.map_cons,List.map_nil,eval_neg] using hh
  · have hh := h.2.1 (Fin.last n) rfl
    simpa only [models_cons, models_nil, and_true, clause_iff, List.map_cons,List.map_nil] using hh

def bit (j : ℕ) (f : Field) := pos (address j f)
def op (j : ℕ) (i : Fin 3) := bit j (.op i.val)
def pin {m : ℕ} (j : ℕ) (side : Bool) (i : Pin m) := bit j (.pin side i.val)
def pref {m : ℕ} (j : ℕ) (side : Bool) (i : Pin m) :=
  if i.val=0 then pin j side i else bit j (.aux side i.val)
def fp {m : ℕ} (j : ℕ) (i : Fin (m+1)) := bit j (.finalPick i.val)
def fq {m : ℕ} (j : ℕ) (i : Fin (m+1)) :=
  if i.val=0 then fp j i else bit j (.finalAux i.val)

@[simp] theorem ev_bit (v : ℕ → Bool) (j : ℕ) (f : Field) :
    literalValue v (bit j f) = numBook v j f := rfl
@[simp] theorem ev_pref {m : ℕ} (v : ℕ → Bool) (j : ℕ) (side : Bool) (i : Pin m) :
    literalValue v (pref j side i) = pinPre (numBook v j) side i := by
  by_cases h : i.val=0 <;> simp [pref,pin,pinPre,h]
@[simp] theorem ev_fq {m : ℕ} (v : ℕ → Bool) (j : ℕ) (i : Fin (m+1)) :
    literalValue v (fq j i) = outPre (numBook v j) i := by
  by_cases h : i.val=0 <;> simp [fq,fp,outPre,h]

def opLines (j : ℕ) : CNF :=
  let a:=op j 0
  let o:=op j 1
  let n:=op j 2
  [[a,o,n],[neg a,neg o],[neg a,neg n],[neg o,neg n]]

theorem opSound (v : ℕ → Bool) (j : ℕ) (h : oneHot (fun i => literalValue v (op j i))) :
    Models v (opLines j) := by
  obtain ⟨⟨i,hi⟩,hpair⟩ := h
  have ha : holds [literalValue v (op j 0),literalValue v (op j 1),literalValue v (op j 2)] := by
    fin_cases i <;> simp_all [holds]
  have h01 := hpair 0 1 (by decide)
  have h02 := hpair 0 2 (by decide)
  have h12 := hpair 1 2 (by decide)
  simpa only [opLines, models_cons, models_nil, and_true, clause_iff,
    List.map_cons, List.map_nil, eval_neg] using And.intro ha ⟨h01,h02,h12⟩

def structureLines (j m : ℕ) : CNF :=
  opLines j ++ cumLines (@pin m j false) (pref j false) ++
    cumLines (@pin m j true) (pref j true) ++ [[neg (op j 2),pin j true (missing m)]] ++
    allFin (fun i : Pin m => [[neg (pref j true i),pref j false i]])

def muxLines {n : ℕ} (pick src : Fin n → SignedVar) (out : SignedVar) : CNF :=
  allFin (fun i => [[neg (pick i),neg (src i),out],[neg (pick i),src i,neg out]])

theorem muxSound {n : ℕ} (v : ℕ → Bool) (pick src : Fin n → SignedVar) (out : SignedVar)
    (h : muxOK (fun i => literalValue v (pick i)) (fun i => literalValue v (src i)) (literalValue v out)) :
    Models v (muxLines pick src out) := by
  apply (models_allFin _ _).mpr
  intro i
  simpa only [models_cons,models_nil,and_true,clause_iff,List.map_cons,List.map_nil,eval_neg] using h i

def truthLines (a o n x y z : SignedVar) : CNF :=
  [[neg a,neg z,x],[neg a,neg z,y],[neg a,z,neg x,neg y],
   [neg o,z,neg x],[neg o,z,neg y],[neg o,neg z,x,y],[neg n,neg z,neg x],[neg n,z,x]]

theorem truthSound (v : ℕ → Bool) (a o n x y z : SignedVar)
    (h : truthClauses (literalValue v a) (literalValue v o) (literalValue v n)
      (literalValue v x) (literalValue v y) (literalValue v z)) :
    Models v (truthLines a o n x y z) := by
  simpa only [truthLines,truthClauses,models_cons,models_nil,and_true,clause_iff,
    List.map_cons,List.map_nil,eval_neg] using h

def evalCols {r : ℕ} (v : ℕ → Bool) (s : List (Col r)) : List (Sig r) :=
  s.map (fun c z => literalValue v (c z))

def wire {r : ℕ} (s : List (Col r)) (z : Fin r) (i : ℕ) : SignedVar :=
  (s.map (fun c => c z)).getD i (constLit false)

theorem wire_read {r : ℕ} (v : ℕ → Bool) (hv : v 1 = true) (s : List (Col r)) (z : Fin r) (i : ℕ) :
    literalValue v (wire s z i) = (row (evalCols v s) z).getD i false := by
  simp only [wire, row, evalCols, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : s[i]? <;> simp [h, hv]

def operand {r : ℕ} (j : ℕ) (s : List (Col r)) (z : Fin r) (i : Pin s.length) :=
  if i.val=s.length+1 then op j 0 else wire s z i.val

theorem operand_read {r : ℕ} (v : ℕ → Bool) (hv : v 1=true) (j : ℕ) (s : List (Col r))
    (z : Fin r) (i : Pin s.length) :
    literalValue v (operand j s z i) =
      readPin (row (evalCols v s) z) (numBook v j (.op 0)) i := by
  by_cases h : i.val=s.length+1 <;>
    simp [operand, readPin, h, op, wire_read v hv]

def cell (j : ℕ) {r : ℕ} (z : Fin r) (c : ℕ) := bit j (.cell z.val c)

def gateRow {r : ℕ} (j : ℕ) (s : List (Col r)) (z : Fin r) : CNF :=
  muxLines (@pin s.length j false) (operand j s z) (cell j z 0) ++
  muxLines (@pin s.length j true) (operand j s z) (cell j z 1) ++
  truthLines (op j 0) (op j 1) (op j 2) (cell j z 0) (cell j z 1) (cell j z 2)

def lastRow {r : ℕ} (j : ℕ) (s : List (Col r)) (t : Sig r) (z : Fin r) : CNF :=
  allFin (fun i : Fin (s.length+1) =>
      [[neg (fp j i),if t z then wire s z i.val else neg (wire s z i.val)]])

-- Static clauses are emitted first, then each row's mux/operation/output
-- clauses. Keeping these lists separate here preserves the solver's order.
structure Parts (r : ℕ) where
  static : CNF
  rows : Fin r → CNF

def emit {r : ℕ} : ℕ → ℕ → List (Col r) → Sig r → Parts r
  | 0, j, s, t => ⟨cumLines (@fp s.length j) (fq j), lastRow j s t⟩
  | k+1, j, s, t =>
    let after := emit k (j+1) (s++[fun z => cell j z 2]) t
    ⟨structureLines j s.length ++ after.static,fun z => gateRow j s z ++ after.rows z⟩

def modelsParts {r : ℕ} (v : ℕ → Bool) (p : Parts r) : Prop :=
  Models v p.static ∧ ∀ z, Models v (p.rows z)

private theorem gateSound {r : ℕ} (v : ℕ → Bool) (hv : v 1=true) (j : ℕ) (s : List (Col r))
    (h : gateOK (evalCols v s) (numBook v j)) :
    Models v (structureLines j s.length) ∧ ∀ z, Models v (gateRow j s z) := by
  have hlen : (evalCols v s).length = s.length := by simp [evalCols]
  simp only [gateOK, readBits, hlen] at h
  obtain ⟨ho,hn,hl,hr,hs,hrow⟩ := h
  have hlo : Models v (cumLines (@pin s.length j false) (pref j false)) := by
    apply cumSound
    simpa only [pin, ev_bit, ev_pref] using hl
  have hro : Models v (cumLines (@pin s.length j true) (pref j true)) := by
    apply cumSound
    simpa only [pin, ev_bit, ev_pref] using hr
  have hnot : Models v [[neg (op j 2),pin j true (missing s.length)]] := by
    simpa only [models_cons,models_nil,and_true,clause_iff,List.map_cons,List.map_nil,
      eval_neg,op,pin,ev_bit] using hn
  have horder : Models v (allFin (fun i : Pin s.length => [[neg (pref j true i),pref j false i]])) := by
    apply (models_allFin _ _).mpr
    intro i
    simpa only [models_cons,models_nil,and_true,clause_iff,List.map_cons,List.map_nil,
      eval_neg,ev_pref] using hs i
  constructor
  · have hoper : Models v (opLines j) := opSound v j ho
    simp only [structureLines, models_append]
    tauto
  · intro z
    obtain ⟨ha,hb,ht⟩ := hrow z
    have hma : Models v (muxLines (@pin s.length j false) (operand j s z) (cell j z 0)) := by
      apply muxSound
      simpa only [pin,cell,ev_bit,operand_read v hv] using ha
    have hmb : Models v (muxLines (@pin s.length j true) (operand j s z) (cell j z 1)) := by
      apply muxSound
      simpa only [pin,cell,ev_bit,operand_read v hv] using hb
    have htr : Models v (truthLines (op j 0) (op j 1) (op j 2)
        (cell j z 0) (cell j z 1) (cell j z 2)) := truthSound v _ _ _ _ _ _ ht
    simp only [gateRow, models_append]
    tauto

private theorem endSound {r : ℕ} (v : ℕ → Bool) (hv : v 1=true) (j : ℕ) (s : List (Col r)) (t : Sig r)
    (h : finalOK (evalCols v s) t (numBook v j)) : modelsParts v (emit 0 j s t) := by
  have hlen : (evalCols v s).length = s.length := by simp [evalCols]
  simp only [finalOK, hlen] at h
  obtain ⟨hc,hrow⟩ := h
  constructor
  · apply cumSound
    simpa only [fp,ev_bit,ev_fq] using hc
  · intro z
    apply (models_allFin _ _).mpr
    intro i
    have hh := hrow z i
    cases htz : t z <;>
      simpa only [htz, Bool.false_eq_true, if_false, if_true, models_cons,models_nil,
        and_true,clause_iff,List.map_cons,List.map_nil,eval_neg,fp,ev_bit,wire_read v hv] using hh

theorem emitSound {r : ℕ} (v : ℕ → Bool) (hv : v 1=true) (k j : ℕ) (s : List (Col r)) (t : Sig r)
    (h : chart k (evalCols v s) t (fun i => numBook v (j+i))) : modelsParts v (emit k j s t) := by
  induction k generalizing s j with
  | zero => exact endSound v hv j s t h
  | succ k ih =>
    obtain ⟨hg,ht⟩ := h
    obtain ⟨hstruct,hrows⟩ := gateSound v hv j s hg
    have he : evalCols v (s ++ [fun z => cell j z 2]) =
        evalCols v s ++ [fun z : Fin r => numBook v j (.cell z.val 2)] := by
      simp [evalCols,cell]
    have hshift : (fun i => numBook v (j+(i+1))) = (fun i => numBook v ((j+1)+i)) := by
      funext i
      have hi : j+(i+1)=(j+1)+i := by omega
      rw [hi]
    have htail : chart k (evalCols v (s ++ [fun z => cell j z 2])) t (fun i => numBook v ((j+1)+i)) := by
      rw [he]
      simpa only [Nat.add_zero,hshift] using ht
    obtain ⟨hts,htr⟩ := ih (j+1) _ htail
    refine ⟨(models_append _ _ _).mpr ⟨hstruct,hts⟩, ?_⟩
    intro z
    exact (models_append _ _ _).mpr ⟨hrows z,htr z⟩

def body {r : ℕ} (s : List (Col r)) (t : Sig r) : CNF :=
  let a := emit 14 0 s t
  a.static ++ allFin a.rows

def ground {r : ℕ} (s : List (Col r)) (t : Sig r) : CNF :=
  [[pos 1]] ++ (body s t).filterMap (eraseConstant 1)

theorem groundModel {r : ℕ} (s : List (Col r)) (t : Sig r) (v : ℕ → Bool)
    (h : NumberedSat (evalCols v s) t v) : Models v (ground s t) := by
  obtain ⟨hv,chartH⟩ := h
  have hc : chart 14 (evalCols v s) t (fun i => numBook v (0+i)) := by
    simpa only [Nat.zero_add] using chartH
  obtain ⟨hs,hr⟩ := emitSound v hv 14 0 s t hc
  apply (models_append _ _ _).mpr
  constructor
  · simp [clause_iff, holds, hv]
  · apply (eraseConstant_correct v 1 hv (body s t)).mpr
    exact (models_append _ _ _).mpr ⟨hs,(models_allFin _ _).mpr hr⟩

-- Python's sorted boundary seeds: empty/full, all vertices, all edges and
-- all maximal independent assignments of the nine-vertex graph.
def seed : Fin 35 → ℕ := ![0,1,2,3,4,6,8,12,16,17,24,32,33,42,50,64,66,69,104,116,
  128,132,138,160,201,208,256,261,264,276,288,320,385,402,511]

def xs (z : Fin 35) (i : Fin 9) : Bool := (seed z).testBit i.val
def head (x : Fin 9 → Bool) : Bool := x 0 && x 1

def edges : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def target (x : Fin 9 → Bool) : Bool := edges.any fun e => x e.1 && x e.2
def labels (z : Fin 35) : Bool := target (xs z)

def columns : List (Col 35) :=
  (List.ofFn (fun i : Fin 9 => fun z => constLit (xs z i))) ++ [fun z => constLit (head (xs z))]
def raw35 : CNF := ground columns labels
def dimacs35 : List (List Int) := raw35.map (List.map asInteger)

theorem columns_eval (v : ℕ → Bool) (hv : v 1=true) : evalCols v columns = initial xs head := by
  simp [evalCols,columns,initial,List.map_ofFn,Function.comp_def,hv]

theorem numbered_model_35 (v : ℕ → Bool) (h : NumberedSat (initial xs head) labels v) :
    Models v raw35 := by
  apply groundModel
  rw [columns_eval v h.1]
  exact h

theorem raw_circuit_models_35 (D : Circuit) (hfan : FanInTwo D) (hsize : D.size≤14)
    (hrows : ∀ z, D.eval (row (initial xs head) z)=labels z) :
    ∃ v : ℕ → Bool, Models v raw35 := by
  obtain ⟨v,hv⟩ := raw_numbered_model (initial xs head) labels (by simp [initial]) D hfan hsize hrows
  exact ⟨v,numbered_model_35 v hv⟩

theorem of_raw35_unsat (no : ¬∃ v : ℕ → Bool, Models v raw35) :
    ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
      ∃ x, D.eval (List.ofFn x ++ [head x]) ≠ target x := by
  apply of_numbered_exclusion xs head target
  rintro ⟨v,h⟩
  exact no ⟨v,numbered_model_35 v h⟩

end PEqualNP.Research.PetersenFormula
