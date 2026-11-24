import Mathlib
import PEqualNP.Defs
/- Finite live-frontier extraction and gate scanning are adapted from the
   public, accepted L-meta-1007. Our instance uses a selected family of true/false
   seven-variable theta pairs, an eighth supplied complemented literal, and
   an empty special set (no degree-restriction hypothesis on tail gates). -/
namespace CoThetaLayerSanity
abbrev B := BitVec 256
abbrev Sig := B × B
def top : B := BitVec.allOnes 256
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]


def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U))

set_option maxRecDepth 10000 in
private lemma target_proper : proper target := by unfold proper target zero one top; decide +kernel
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 256
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 256
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 256)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 256) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 256 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 256)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (side : Bool) (i : Fin 256) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 256).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]


def special : List Sig := []
inductive Restricted : Nat → Nat → Finset Sig → Prop
  | stop : Restricted 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hf : neg a ∉ insert a U) (hr : a ∉ special)
      (tail : Restricted k t (insert (neg a) U)) :
      Restricted (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hf : bin d a b ∉ insert a (insert b U))
      (hra : a ∈ special → d = true ∧ a ∉ U)
      (hrb : b ∈ special → d = true ∧ b ∉ U)
      (tail : Restricted k t (insert (bin d a b) U)) :
      Restricted (k+1) t (insert a (insert b U))

lemma Restricted.live {k t S} (h : Restricted k t S) : Live k t S := by
  induction h with
  | stop => exact Live.stop
  | unary ha hf _ _ ih => exact Live.unary ha hf ih
  | binary ha hb hab hf _ _ _ ih => exact Live.binary ha hb hab hf ih

private lemma unrestricted {k t : Nat} {S : Finset Sig} (h : Live k t S) : Restricted k t S := by
  induction h with
  | stop => exact .stop
  | unary h1 h2 _ ih => exact .unary h1 h2 (by simp [special]) ih
  | binary h1 h2 h3 h4 _ ih => exact .binary h1 h2 h3 h4 (by simp [special]) (by simp [special]) ih

def gateAvailable (v : List Sig) (g : Sig) : Bool :=
  !(v.contains g) && g != zero && g != one

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    base == top && gateAvailable v g && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && gateAvailable v g && r (g::(h++rest)))

def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  !(special.contains a) &&
    tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let c := coverage (decide (0<t)) v
  v.any (unaryAt k t r v c)

def allowedKeeps (a b : Sig) : List (List Sig) :=
  [[],[a],[b],[a,b]].filter (fun w => w.all fun x => !(special.contains x))

def fastBinary (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) : Bool :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => gateAvailable v g && r (g::rest)
  ((ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    !(special.contains a) && !(special.contains b) && use (bin false a b)) ||
    ((ua &&& b.2) == 0 && (ub &&& a.2) == 0 && use (bin true a b))

def slowBinary (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  ((!(special.contains a) && !(special.contains b)) &&
    tryGate k t r v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]]) ||
    tryGate k t r v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)

def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t

lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let d := decide (0<t)
  let c := coverage d v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a, c.2.1 &&& sep false a))
    scanPairs (fun a b => fastBinary r v a.1 b.1 a.2 b.2) acts
  else scanPairs (slowBinary k t r v c) v

def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
    v == [target] || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v == [target]
  | k+1,t,v => stepTest k t v (search k (t-1)) (search k t)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,gateAvailable,ha,hp.1,hp.2,hr] at *
  · have hav : gateAvailable v g = true := by simp [gateAvailable, ha, hp.1, hp.2]
    simp only [tryGate, ite_eq_right tight, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, hav, and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩

private lemma unique_needed (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private lemma fast_ok {k r v c a b}
    (hlen : v.length-2=k) (h : slowBinary k 0 r v c a b = true) :
    fastBinary r v a b (c.2.1 &&& sep false a) (c.2.1 &&& sep false b) = true := by
  simp only [slowBinary,tryGate,Nat.sub_zero,hlen,ite_true,decide_false,Bool.or_eq_true,
    Bool.and_eq_true,beq_iff_eq] at h
  simp only [fastBinary, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hc,hav⟩,hr⟩ | ⟨⟨hc,hav⟩,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b false hc)
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b true hc)
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (ha : a ∉ special) (l : Restricted m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves k t r v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simp [ha], gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Restricted m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    slowBinary k t r v (coverage (decide (0<t)) v) a b = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have allow : h ∈ allowedKeeps a b := by
    apply List.mem_filter.mpr
    refine ⟨opts,List.all_eq_true.mpr (fun x hx => ?_)⟩
    have hm : x ∈ U := (List.mem_filter.mp hx).2 |> of_decide_eq_true
    rcases List.mem_cons.mp (List.mem_filter.mp hx).1 with rfl | hx
    · simpa using fun ha : x ∈ special => (hra ha).2 hm
    · obtain rfl := List.mem_singleton.mp hx
      simpa using fun hb : x ∈ special => (hrb hb).2 hm
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  unfold slowBinary
  dsimp only
  rw [hlen,hmask]
  cases d with
  | false =>
    have na : a ∉ special := fun ha => Bool.false_ne_true (hra ha).1
    have nb : b ∉ special := fun hb => Bool.false_ne_true (hrb hb).1
    apply Bool.or_eq_true_iff.mpr
    left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Restricted m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Restricted m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
  have h2 := slow_found hv e' hle hab.symm hf hrb hra ht (by simpa only [bin_comm d b a] using ih)
  unfold binaryMoves
  split
  · rename_i cut
    simp only [Bool.and_eq_true, beq_iff_eq] at cut
    obtain ⟨rfl,hvlen⟩ := cut
    have hlen : v.length - 2 = k := by omega
    let f := fun x => (x, (coverage false v).2.1 &&& sep false x)
    have na : f a ∈ v.map f := List.mem_map_of_mem ah
    have nb : f b ∈ v.map f := List.mem_map_of_mem bh
    exact scanPairs_complete _ na nb (fun e => hab (congrArg Prod.fst e))
      (fast_ok hlen h1) (fast_ok hlen h2)
  · exact scanPairs_complete _ ah bh hab h1 h2

private lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
    (h : Restricted m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Restricted l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Restricted l t w.toFinset → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h.live
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, if_neg (by omega)]
  cases h with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf hr tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf hr tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf hra hrb tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Restricted m t S) (k : Nat) (hk : m ≤ k)
    (v : List Sig) (hv : v.Nodup) (hs : v.toFinset = S) : search k t v = true := by
  induction k generalizing m t S v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    cases h
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    simp [search, List.perm_singleton.mp p]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl

def Impossible (k t : Nat) (v : List Sig) : Prop :=
  ∀ m ≤ k, ¬ Restricted m t v.toFinset

lemma exclude_search {k t : Nat} {v : List Sig} (hv : v.Nodup) (hc : search k t v = false) :
    Impossible k t v := by
  intro m hm h
  exact Bool.false_ne_true (hc.symm.trans (search_complete h k hm v hv rfl))
def x0 : Sig := (0xaaa50a50a050005285c583f7ffc02942c1f9f80ffff40a000bffe0101ffff03f,0x20500140058800284d002727a9100044130382471d00b02093d448044d99136)
def x1 : Sig := (0xccc60c60c0600063067efc180ffff1837e0e8ff7e0180c000c07ffffefc03fc0,0xcc001c60c0200a0008189c0021c781804e0aa972c4980c084010e9c2e9851d84)
def x2 : Sig := (0xf0f80f80ff80007c0787001ff0003e03800f0ff8001ff0000ff8001ff0003fff,0x30f883823f85247c4307410d84003e13a08506890007f0a486c2001d12002208)
def x3 : Sig := (0xff000fff0000007ff807ffe000003ffc000ff000001ffffff000001fffffc000,0xfd000feb090608751807f981002203d8080fc302000d54c8e000811f9b260400)
def x4 : Sig := (0xfffff0000000007ffff8000000003ffffff00000001fffffffffffe000000000,0x2ffe0001208300ae7e0020608003c27b1e004000902a3370fe7160004080010)
def x5 : Sig := (0xffffffffffffff800000000000003fffffffffffffe000000000000000000000,0xfcea3ee3e3a03f000000100001043ffbbccfc7cb8e00c0380080180608000800)
def x6 : Sig := (0xffffffffffffffffffffffffffffc00000000000000000000000000000000000,0x315c11c1c5fc07ff7e763dfce38000001000004100301c00304000800300020)

def raw7 : List Sig := [x0,x1,x2,x3,x4,x5,x6]
def col (j : Fin 7) : Sig := raw7.getD j.val zero
def raw (j : Fin 7) : List Sig := raw7 ++ [neg (col j)]
def sample (d : Bool) (i : Fin 256) (j : Fin 7) := bit d i (col j)
def theta (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 1)
def edgeSig : Sig :=
  (bin true (bin true (bin true (bin true (bin true (bin true (bin true (bin false (col 0) (col 2)) (bin false (col 2) (col 1))) (bin false (col 0) (col 3))) (bin false (col 3) (col 4))) (bin false (col 4) (col 1))) (bin false (col 0) (col 5))) (bin false (col 5) (col 6))) (bin false (col 6) (col 1)))
private theorem edgeSig_eq : edgeSig = target := by decide +kernel

private theorem sample_ok (d : Bool) (i : Fin 256) : theta (sample d i) = d := by
  have h := congrArg (bit d i) edgeSig_eq
  simp only [edgeSig, bit_bin, Bool.false_eq_true, ↓reduceIte] at h
  have ht : bit d i target = d := by
    cases d
    · change (0 : B).getLsbD i.val = false
      simp
    · change (BitVec.allOnes 256).getLsbD i.val = true
      rw [BitVec.getLsbD_allOnes]
      simp
  exact h.trans ht

private theorem sample_list (d : Bool) (i : Fin 256) :
    List.ofFn (sample d i) = raw7.map (bit d i) := by
  have h : List.ofFn col = raw7 := by rfl
  rw [← h, List.map_ofFn]; rfl

theorem circuit_target (j : Fin 7) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x ++ [!(x j)]) = theta x) :
    target ∈ execute C.gates (raw j) := by
  let w := execute C.gates (raw j)
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates (raw j)).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    simpa only [raw,List.map_append,List.map_singleton,bit_neg,sample,Circuit.eval,Circuit.wires] using eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

/-- The search checks the only possible number of successors at each state,
    and projects no special degree assumption onto these signed inputs. -/
def rejectState (ws : List Sig) (t : Nat) :=
  if unionSep (decide (0<t)) ws = top then !(search 10 t ws) else true

def checkedRoot (j : Fin 7) : Bool :=
  (raw j).sublists.all fun ws => (List.range (12-ws.length)).all fun t => rejectState ws t

private lemma raws_nd (j : Fin 7) : (raw j).Nodup := by fin_cases j <;> decide +kernel

theorem exclusion (j : Fin 7) (cert : checkedRoot j = true) (C : Circuit)
    (hs : C.size ≤ 10) (hf : PEqualNP.MetaComplexity.FanInTwo C) :
    ¬ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x ++ [!(x j)]) = theta x := by
  intro he
  obtain ⟨k,t,S,hk,hl,hsub⟩ := extract C.gates (raw j) hf (circuit_target j C hf he)
  let ws := (raw j).filter fun a => decide (a ∈ S)
  have hsl : ws.Sublist (raw j) := List.filter_sublist
  have hn : ws.Nodup := (raws_nd j).sublist hsl
  have heq : ws.toFinset = S := by
    ext a; simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun ha => ⟨hsub a ha, ha⟩⟩
  have hbudget : k ≤ 10 := hk.trans hs
  have hsize := (live_size hl).2
  rw [← heq,List.toFinset_card_of_nodup hn] at hsize
  have hh := List.all_eq_true.mp cert ws (List.mem_sublists.mpr hsl)
  have hc := List.all_eq_true.mp hh t (List.mem_range.mpr (by omega))
  have hy := search_complete (unrestricted hl) 10 hbudget ws hn heq
  simp [rejectState, live_cover hl heq, hy] at hc

/-- A numerical hash chooses one candidate by index. Every successful lookup
    verifies the entire frontier up to permutation, so collisions can only
    increase work. Neither the hash nor table generation is trusted. -/
structure Layer where
  count : Nat → Nat
  state : Nat → Nat → List Sig
  pick : Nat → List Sig → Nat

def Layer.matchState (L : Layer) (t : Nat) (w : List Sig) :=
  let i := L.pick t w
  decide (i < L.count t) && w.isPerm (L.state t i)

def Layer.Valid (L : Layer) (k : Nat) := ∀ t i, i < L.count t → Impossible k t (L.state t i)

private theorem perm_impossible {k t : Nat} {w z : List Sig} (h : w.Perm z)
    (hz : Impossible k t z) : Impossible k t w := by
  have he : w.toFinset = z.toFinset := by
    ext a
    exact List.mem_toFinset.trans (h.mem_iff.trans List.mem_toFinset.symm)
  unfold Impossible at *
  rwa [he]

private theorem Layer.checked {L : Layer} {k t : Nat} {w : List Sig}
    (h : L.Valid k) (hm : L.matchState t w = true) : Impossible k t w := by
  unfold Layer.matchState at hm
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hm
  exact perm_impossible hm.2 (h _ _ hm.1)

private theorem exclude_step {k t : Nat} {v : List Sig} {u b : List Sig → Bool} (hv : v.Nodup)
    (hu : ∀ w, u w = false → Impossible k (t-1) w)
    (hb : ∀ w, b w = false → Impossible k t w)
    (hc : stepTest k t v u b = false) : Impossible (k+1) t v := by
  intro m hm h
  have hu' : ∀ w, w.Nodup → ∀ j ≤ k, Restricted j (t-1) w.toFinset → u w = true := by
    intro w _ j hj r
    cases e : u w
    · exact (hu _ e j hj r).elim
    · rfl
  have hb' : ∀ w, w.Nodup → ∀ j ≤ k, Restricted j t w.toFinset → b w = true := by
    intro w _ j hj r
    cases e : b w
    · exact (hb _ e j hj r).elim
    · rfl
  exact Bool.false_ne_true (hc.symm.trans (reduced_step h hm hv rfl hu' hb'))

def layerNode (L : Layer) (k t : Nat) (v : List Sig) : Bool :=
  decide v.Nodup && !stepTest k t v (fun w => !L.matchState (t-1) w) (fun w => !L.matchState t w)

theorem layerNode_sound {k t : Nat} {v : List Sig} {L : Layer} (hl : L.Valid k)
    (h : layerNode L k t v = true) : Impossible (k+1) t v := by
  simp only [layerNode,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
  apply exclude_step h.1 _ _ h.2
  · intro w hw; exact Layer.checked hl (by simpa using hw)
  · intro w hw; exact Layer.checked hl (by simpa using hw)

def leafPass (k t : Nat) (v : List Sig) := decide v.Nodup && !search k t v

private theorem leafPass_sound {k t : Nat} {v : List Sig} (hc : leafPass k t v = true) :
    Impossible k t v := by
  simp only [leafPass,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at hc
  exact exclude_search hc.1 hc.2

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

private theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

def rootTable (j : Fin 7) (L : Layer) : Bool := (raw j).sublists.all fun ws =>
  (List.range (12-ws.length)).all fun t =>
    if unionSep (decide (0<t)) ws = top then L.matchState t ws else true

theorem exclusion_from_layers (j : Fin 7) (L : Layer) (hv : L.Valid 10)
    (cert : rootTable j L = true) (C : Circuit) (hs : C.size ≤ 10) (hf : PEqualNP.MetaComplexity.FanInTwo C) :
    ¬ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x ++ [!(x j)]) = theta x := by
  intro he
  obtain ⟨k,t,S,hk,hl,hsub⟩ := extract C.gates (raw j) hf (circuit_target j C hf he)
  let ws := (raw j).filter fun a => decide (a ∈ S)
  have hsl : ws.Sublist (raw j) := List.filter_sublist
  have hn : ws.Nodup := (raws_nd j).sublist hsl
  have heq : ws.toFinset = S := by
    ext a; simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun ha => ⟨hsub a ha, ha⟩⟩
  have hbudget : k ≤ 10 := hk.trans hs
  have hsize := (live_size hl).2
  rw [← heq,List.toFinset_card_of_nodup hn] at hsize
  have hh := List.all_eq_true.mp cert ws (List.mem_sublists.mpr hsl)
  have hc := List.all_eq_true.mp hh t (List.mem_range.mpr (by omega))
  simp only [if_pos (live_cover hl heq)] at hc
  exact Layer.checked hv hc k hbudget (heq.symm ▸ unrestricted hl)

namespace ThetaCut
set_option maxRecDepth 30000
set_option maxHeartbeats 0
private def fingerprint (a : Sig) : Nat :=
  (((a.1.toNat % 2147483647)*257+a.2.toNat % 2147483647+317) % 2147483647)^3 % 2147483647
private def stateHash (v : List Sig) : Nat := (v.foldl (fun z a => z+fingerprint a) 0) % 2147483647
private def s0 : Sig := x0
private def s1 : Sig := x1
private def s2 : Sig := x2
private def s3 : Sig := x3
private def s4 : Sig := x4
private def s5 : Sig := x5
private def s6 : Sig := x6
private def s7 : Sig := neg s0
private def s8 : Sig := neg s2
private def s9 : Sig := neg s3
private def s10 : Sig := bin false s9 s0
private def s11 : Sig := bin true s9 s0
private def s12 : Sig := bin false s9 s1
private def s13 : Sig := bin true s9 s1
private def s14 : Sig := bin false s9 s2
private def s15 : Sig := bin true s9 s2
private def s16 : Sig := bin false s9 s4
private def s17 : Sig := bin true s9 s4
private def s18 : Sig := bin false s9 s5
private def s19 : Sig := bin true s9 s5
private def s20 : Sig := bin false s9 s6
private def s21 : Sig := bin true s9 s6
private def s22 : Sig := bin false s0 s1
private def s23 : Sig := bin true s0 s1
private def s24 : Sig := bin false s0 s2
private def s25 : Sig := bin true s0 s2
private def s26 : Sig := bin false s0 s3
private def s27 : Sig := bin true s0 s3
private def s28 : Sig := bin false s0 s4
private def s29 : Sig := bin true s0 s4
private def s30 : Sig := bin false s0 s5
private def s31 : Sig := bin true s0 s5
private def s32 : Sig := bin false s0 s6
private def s33 : Sig := bin true s0 s6
private def s34 : Sig := bin false s1 s2
private def s35 : Sig := bin true s1 s2
private def s36 : Sig := bin false s1 s3
private def s37 : Sig := bin true s1 s3
private def s38 : Sig := bin false s1 s4
private def s39 : Sig := bin true s1 s4
private def s40 : Sig := bin false s1 s5
private def s41 : Sig := bin true s1 s5
private def s42 : Sig := bin false s1 s6
private def s43 : Sig := bin true s1 s6
private def s44 : Sig := bin false s2 s3
private def s45 : Sig := bin true s2 s3
private def s46 : Sig := bin false s2 s4
private def s47 : Sig := bin true s2 s4
private def s48 : Sig := bin false s2 s5
private def s49 : Sig := bin true s2 s5
private def s50 : Sig := bin false s2 s6
private def s51 : Sig := bin true s2 s6
private def s52 : Sig := bin false s3 s4
private def s53 : Sig := bin true s3 s4
private def s54 : Sig := bin false s3 s5
private def s55 : Sig := bin true s3 s5
private def s56 : Sig := bin false s3 s6
private def s57 : Sig := bin true s3 s6
private def s58 : Sig := bin false s4 s5
private def s59 : Sig := bin true s4 s5
private def s60 : Sig := bin false s4 s6
private def s61 : Sig := bin true s4 s6
private def s62 : Sig := bin false s5 s6
private def s63 : Sig := bin true s5 s6
private def s64 : Sig := bin false s8 s0
private def s65 : Sig := bin true s8 s0
private def s66 : Sig := bin false s8 s1
private def s67 : Sig := bin true s8 s1
private def s68 : Sig := bin false s8 s3
private def s69 : Sig := bin true s8 s3
private def s70 : Sig := bin false s8 s4
private def s71 : Sig := bin true s8 s4
private def s72 : Sig := bin false s8 s5
private def s73 : Sig := bin true s8 s5
private def s74 : Sig := bin false s8 s6
private def s75 : Sig := bin true s8 s6
private def s76 : Sig := bin false s7 s1
private def s77 : Sig := bin true s7 s1
private def s78 : Sig := bin false s7 s2
private def s79 : Sig := bin true s7 s2
private def s80 : Sig := bin false s7 s3
private def s81 : Sig := bin true s7 s3
private def s82 : Sig := bin false s7 s4
private def s83 : Sig := bin true s7 s4
private def s84 : Sig := bin false s7 s5
private def s85 : Sig := bin true s7 s5
private def s86 : Sig := bin false s7 s6
private def s87 : Sig := bin true s7 s6
private def s88 : Sig := neg s1
private def s89 : Sig := neg s4
private def s90 : Sig := neg s5
private def s91 : Sig := neg s6
private def states_10_0 (i : Nat) : List Sig :=
  (if i < 2 then (if i < 1 then [s0,s1,s2,s3,s4,s5,s6,s9] else [s0,s1,s2,s3,s4,s5,s6,s8]) else (if i < 3 then [s0,s1,s2,s3,s4,s5,s6,s7] else [s0,s1,s2,s3,s4,s5,s6]))
private def slots_10_0 (h : Nat) : Nat :=
  (if h < 1539613317 then (if h < 1241647531 then 1 else 0) else (if h < 1644052150 then 2 else 3))
private def states_10_1 (i : Nat) : List Sig :=
  (if i < 3 then (if i < 1 then [s0,s1,s2,s3,s4,s5,s6,s9] else (if i < 2 then [s0,s1,s2,s4,s5,s6,s9] else [s0,s1,s2,s3,s4,s5,s6,s8])) else (if i < 5 then (if i < 4 then [s0,s1,s3,s4,s5,s6,s8] else [s0,s1,s2,s3,s4,s5,s6,s7]) else (if i < 6 then [s1,s2,s3,s4,s5,s6,s7] else [s0,s1,s2,s3,s4,s5,s6])))
private def slots_10_1 (h : Nat) : Nat :=
  (if h < 1241647531 then (if h < 163089682 then 1 else (if h < 330465445 then 3 else 2)) else (if h < 1539613317 then (if h < 1386284011 then 0 else 5) else (if h < 1644052150 then 4 else 6)))
private def states_10_2 (i : Nat) : List Sig :=
  (if i < 3 then (if i < 1 then [s0,s1,s2,s3,s4,s5,s6,s9] else (if i < 2 then [s0,s1,s2,s4,s5,s6,s9] else [s0,s1,s2,s3,s4,s5,s6,s8])) else (if i < 5 then (if i < 4 then [s0,s1,s3,s4,s5,s6,s8] else [s0,s1,s2,s3,s4,s5,s6,s7]) else (if i < 6 then [s1,s2,s3,s4,s5,s6,s7] else [s0,s1,s2,s3,s4,s5,s6])))
private def slots_10_2 (h : Nat) : Nat :=
  (if h < 1241647531 then (if h < 163089682 then 1 else (if h < 330465445 then 3 else 2)) else (if h < 1539613317 then (if h < 1386284011 then 0 else 5) else (if h < 1644052150 then 4 else 6)))
private def states_10_3 (i : Nat) : List Sig :=
  (if i < 3 then (if i < 1 then [s0,s1,s2,s3,s4,s5,s6,s9] else (if i < 2 then [s0,s1,s2,s4,s5,s6,s9] else [s0,s1,s2,s3,s4,s5,s6,s8])) else (if i < 5 then (if i < 4 then [s0,s1,s3,s4,s5,s6,s8] else [s0,s1,s2,s3,s4,s5,s6,s7]) else (if i < 6 then [s1,s2,s3,s4,s5,s6,s7] else [s0,s1,s2,s3,s4,s5,s6])))
private def slots_10_3 (h : Nat) : Nat :=
  (if h < 1241647531 then (if h < 163089682 then 1 else (if h < 330465445 then 3 else 2)) else (if h < 1539613317 then (if h < 1386284011 then 0 else 5) else (if h < 1644052150 then 4 else 6)))
private def states_10_4 (i : Nat) : List Sig :=
  (if i < 2 then (if i < 1 then [s0,s1,s2,s4,s5,s6,s9] else [s0,s1,s3,s4,s5,s6,s8]) else (if i < 3 then [s1,s2,s3,s4,s5,s6,s7] else [s0,s1,s2,s3,s4,s5,s6]))
private def slots_10_4 (h : Nat) : Nat :=
  (if h < 1386284011 then (if h < 163089682 then 0 else 1) else (if h < 1644052150 then 2 else 3))
def L10 : Layer where
  count t := if t < 5 then (if t < 2 then (if t < 1 then 4 else 7) else (if t < 3 then 7 else (if t < 4 then 7 else 4))) else 0
  state t i := (if t < 2 then (if t < 1 then states_10_0 i else states_10_1 i) else (if t < 3 then states_10_2 i else (if t < 4 then states_10_3 i else states_10_4 i)))
  pick t v := let h := stateHash v; (if t < 2 then (if t < 1 then slots_10_0 h else slots_10_1 h) else (if t < 3 then slots_10_2 h else (if t < 4 then slots_10_3 h else slots_10_4 h)))
private def states_9_0 (i : Nat) : List Sig :=
  (if i < 131 then (if i < 65 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then [s0,s1,s2,s3,s4,s5,s6,s9,s91] else [s0,s1,s2,s3,s4,s5,s6,s8,s91]) else (if i < 3 then [s0,s1,s2,s3,s4,s5,s6,s7,s91] else [s0,s1,s2,s3,s4,s5,s6,s91])) else (if i < 6 then (if i < 5 then [s0,s1,s2,s3,s4,s5,s6,s9,s90] else [s0,s1,s2,s3,s4,s5,s6,s8,s90]) else (if i < 7 then [s0,s1,s2,s3,s4,s5,s6,s7,s90] else [s0,s1,s2,s3,s4,s5,s6,s90]))) else (if i < 12 then (if i < 10 then (if i < 9 then [s0,s1,s2,s3,s4,s5,s6,s9,s89] else [s0,s1,s2,s3,s4,s5,s6,s8,s89]) else (if i < 11 then [s0,s1,s2,s3,s4,s5,s6,s7,s89] else [s0,s1,s2,s3,s4,s5,s6,s89])) else (if i < 14 then (if i < 13 then [s0,s1,s2,s3,s4,s5,s6,s9,s10] else [s0,s1,s2,s3,s4,s5,s6,s10]) else (if i < 15 then [s0,s1,s2,s3,s4,s5,s6,s9,s12] else [s0,s1,s2,s3,s4,s5,s6,s12])))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then [s0,s1,s2,s3,s4,s5,s6,s9,s14] else [s0,s1,s2,s3,s4,s5,s6,s14]) else (if i < 19 then [s0,s1,s2,s3,s4,s5,s6,s9,s16] else [s0,s1,s2,s3,s4,s5,s6,s16])) else (if i < 22 then (if i < 21 then [s0,s1,s2,s3,s4,s5,s6,s9,s18] else [s0,s1,s2,s3,s4,s5,s6,s18]) else (if i < 23 then [s0,s1,s2,s3,s4,s5,s6,s9,s20] else [s0,s1,s2,s3,s4,s5,s6,s20]))) else (if i < 28 then (if i < 26 then (if i < 25 then [s0,s1,s2,s3,s4,s5,s6,s8,s9] else [s0,s1,s2,s3,s4,s5,s6,s9,s88]) else (if i < 27 then [s0,s1,s2,s3,s4,s5,s6,s7,s9] else [s0,s1,s2,s3,s4,s5,s6,s9,s22])) else (if i < 30 then (if i < 29 then [s0,s1,s2,s3,s4,s5,s6,s9,s24] else [s0,s1,s2,s3,s4,s5,s6,s9,s26]) else (if i < 31 then [s0,s1,s2,s3,s4,s5,s6,s9,s28] else [s0,s1,s2,s3,s4,s5,s6,s9,s30]))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then [s0,s1,s2,s3,s4,s5,s6,s9,s32] else [s0,s1,s2,s3,s4,s5,s6,s9,s11]) else (if i < 35 then [s0,s1,s2,s3,s4,s5,s6,s9,s34] else [s0,s1,s2,s3,s4,s5,s6,s9,s36])) else (if i < 38 then (if i < 37 then [s0,s1,s2,s3,s4,s5,s6,s9,s38] else [s0,s1,s2,s3,s4,s5,s6,s9,s40]) else (if i < 39 then [s0,s1,s2,s3,s4,s5,s6,s9,s42] else [s0,s1,s2,s3,s4,s5,s6,s9,s13]))) else (if i < 44 then (if i < 42 then (if i < 41 then [s0,s1,s2,s3,s4,s5,s6,s9,s23] else [s0,s1,s2,s3,s4,s5,s6,s9,s44]) else (if i < 43 then [s0,s1,s2,s3,s4,s5,s6,s9,s46] else [s0,s1,s2,s3,s4,s5,s6,s9,s48])) else (if i < 46 then (if i < 45 then [s0,s1,s2,s3,s4,s5,s6,s9,s50] else [s0,s1,s2,s3,s4,s5,s6,s9,s15]) else (if i < 47 then [s0,s1,s2,s3,s4,s5,s6,s9,s25] else [s0,s1,s2,s3,s4,s5,s6,s9,s35])))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then [s0,s1,s2,s3,s4,s5,s6,s9,s52] else [s0,s1,s2,s3,s4,s5,s6,s9,s54]) else (if i < 51 then [s0,s1,s2,s3,s4,s5,s6,s9,s56] else [s0,s1,s2,s3,s4,s5,s6,s9,s27])) else (if i < 54 then (if i < 53 then [s0,s1,s2,s3,s4,s5,s6,s9,s37] else [s0,s1,s2,s3,s4,s5,s6,s9,s45]) else (if i < 55 then [s0,s1,s2,s3,s4,s5,s6,s9,s58] else [s0,s1,s2,s3,s4,s5,s6,s9,s60]))) else (if i < 60 then (if i < 58 then (if i < 57 then [s0,s1,s2,s3,s4,s5,s6,s9,s17] else [s0,s1,s2,s3,s4,s5,s6,s9,s29]) else (if i < 59 then [s0,s1,s2,s3,s4,s5,s6,s9,s39] else [s0,s1,s2,s3,s4,s5,s6,s9,s47])) else (if i < 62 then (if i < 61 then [s0,s1,s2,s3,s4,s5,s6,s9,s53] else [s0,s1,s2,s3,s4,s5,s6,s9,s62]) else (if i < 63 then [s0,s1,s2,s3,s4,s5,s6,s9,s19] else (if i < 64 then [s0,s1,s2,s3,s4,s5,s6,s9,s31] else [s0,s1,s2,s3,s4,s5,s6,s9,s41]))))))) else (if i < 98 then (if i < 81 then (if i < 73 then (if i < 69 then (if i < 67 then (if i < 66 then [s0,s1,s2,s3,s4,s5,s6,s9,s49] else [s0,s1,s2,s3,s4,s5,s6,s9,s55]) else (if i < 68 then [s0,s1,s2,s3,s4,s5,s6,s9,s59] else [s0,s1,s2,s3,s4,s5,s6,s9])) else (if i < 71 then (if i < 70 then [s0,s1,s2,s3,s4,s5,s6,s9,s21] else [s0,s1,s2,s3,s4,s5,s6,s9,s33]) else (if i < 72 then [s0,s1,s2,s3,s4,s5,s6,s9,s43] else [s0,s1,s2,s3,s4,s5,s6,s9,s51]))) else (if i < 77 then (if i < 75 then (if i < 74 then [s0,s1,s2,s3,s4,s5,s6,s9,s57] else [s0,s1,s2,s3,s4,s5,s6,s9,s61]) else (if i < 76 then [s0,s1,s2,s3,s4,s5,s6,s9,s63] else [s0,s1,s2,s3,s4,s5,s6,s8,s64])) else (if i < 79 then (if i < 78 then [s0,s1,s2,s3,s4,s5,s6,s64] else [s0,s1,s2,s3,s4,s5,s6,s8,s66]) else (if i < 80 then [s0,s1,s2,s3,s4,s5,s6,s66] else [s0,s1,s2,s3,s4,s5,s6,s8,s68])))) else (if i < 89 then (if i < 85 then (if i < 83 then (if i < 82 then [s0,s1,s2,s3,s4,s5,s6,s68] else [s0,s1,s2,s3,s4,s5,s6,s8,s70]) else (if i < 84 then [s0,s1,s2,s3,s4,s5,s6,s70] else [s0,s1,s2,s3,s4,s5,s6,s8,s72])) else (if i < 87 then (if i < 86 then [s0,s1,s2,s3,s4,s5,s6,s72] else [s0,s1,s2,s3,s4,s5,s6,s8,s74]) else (if i < 88 then [s0,s1,s2,s3,s4,s5,s6,s74] else [s0,s1,s2,s3,s4,s5,s6,s8,s88]))) else (if i < 93 then (if i < 91 then (if i < 90 then [s0,s1,s2,s3,s4,s5,s6,s7,s8] else [s0,s1,s2,s3,s4,s5,s6,s8,s22]) else (if i < 92 then [s0,s1,s2,s3,s4,s5,s6,s8,s24] else [s0,s1,s2,s3,s4,s5,s6,s8,s26])) else (if i < 95 then (if i < 94 then [s0,s1,s2,s3,s4,s5,s6,s8,s28] else [s0,s1,s2,s3,s4,s5,s6,s8,s30]) else (if i < 96 then [s0,s1,s2,s3,s4,s5,s6,s8,s32] else (if i < 97 then [s0,s1,s2,s3,s4,s5,s6,s8,s65] else [s0,s1,s2,s3,s4,s5,s6,s8,s34])))))) else (if i < 114 then (if i < 106 then (if i < 102 then (if i < 100 then (if i < 99 then [s0,s1,s2,s3,s4,s5,s6,s8,s36] else [s0,s1,s2,s3,s4,s5,s6,s8,s38]) else (if i < 101 then [s0,s1,s2,s3,s4,s5,s6,s8,s40] else [s0,s1,s2,s3,s4,s5,s6,s8,s42])) else (if i < 104 then (if i < 103 then [s0,s1,s2,s3,s4,s5,s6,s8,s67] else [s0,s1,s2,s3,s4,s5,s6,s8,s23]) else (if i < 105 then [s0,s1,s2,s3,s4,s5,s6,s8,s44] else [s0,s1,s2,s3,s4,s5,s6,s8,s46]))) else (if i < 110 then (if i < 108 then (if i < 107 then [s0,s1,s2,s3,s4,s5,s6,s8,s48] else [s0,s1,s2,s3,s4,s5,s6,s8,s50]) else (if i < 109 then [s0,s1,s2,s3,s4,s5,s6,s8,s25] else [s0,s1,s2,s3,s4,s5,s6,s8,s35])) else (if i < 112 then (if i < 111 then [s0,s1,s2,s3,s4,s5,s6,s8,s52] else [s0,s1,s2,s3,s4,s5,s6,s8,s54]) else (if i < 113 then [s0,s1,s2,s3,s4,s5,s6,s8,s56] else [s0,s1,s2,s3,s4,s5,s6,s8,s69])))) else (if i < 122 then (if i < 118 then (if i < 116 then (if i < 115 then [s0,s1,s2,s3,s4,s5,s6,s8,s27] else [s0,s1,s2,s3,s4,s5,s6,s8,s37]) else (if i < 117 then [s0,s1,s2,s3,s4,s5,s6,s8,s45] else [s0,s1,s2,s3,s4,s5,s6,s8,s58])) else (if i < 120 then (if i < 119 then [s0,s1,s2,s3,s4,s5,s6,s8,s60] else [s0,s1,s2,s3,s4,s5,s6,s8,s71]) else (if i < 121 then [s0,s1,s2,s3,s4,s5,s6,s8,s29] else [s0,s1,s2,s3,s4,s5,s6,s8,s39]))) else (if i < 126 then (if i < 124 then (if i < 123 then [s0,s1,s2,s3,s4,s5,s6,s8,s47] else [s0,s1,s2,s3,s4,s5,s6,s8,s53]) else (if i < 125 then [s0,s1,s2,s3,s4,s5,s6,s8,s62] else [s0,s1,s2,s3,s4,s5,s6,s8,s73])) else (if i < 128 then (if i < 127 then [s0,s1,s2,s3,s4,s5,s6,s8,s31] else [s0,s1,s2,s3,s4,s5,s6,s8,s41]) else (if i < 129 then [s0,s1,s2,s3,s4,s5,s6,s8,s49] else (if i < 130 then [s0,s1,s2,s3,s4,s5,s6,s8,s55] else [s0,s1,s2,s3,s4,s5,s6,s8,s59])))))))) else (if i < 197 then (if i < 164 then (if i < 147 then (if i < 139 then (if i < 135 then (if i < 133 then (if i < 132 then [s0,s1,s2,s3,s4,s5,s6,s8] else [s0,s1,s2,s3,s4,s5,s6,s8,s75]) else (if i < 134 then [s0,s1,s2,s3,s4,s5,s6,s8,s33] else [s0,s1,s2,s3,s4,s5,s6,s8,s43])) else (if i < 137 then (if i < 136 then [s0,s1,s2,s3,s4,s5,s6,s8,s51] else [s0,s1,s2,s3,s4,s5,s6,s8,s57]) else (if i < 138 then [s0,s1,s2,s3,s4,s5,s6,s8,s61] else [s0,s1,s2,s3,s4,s5,s6,s8,s63]))) else (if i < 143 then (if i < 141 then (if i < 140 then [s0,s1,s2,s3,s4,s5,s6,s7,s88] else [s0,s1,s2,s3,s4,s5,s6,s88]) else (if i < 142 then [s0,s1,s2,s3,s4,s5,s6,s7,s76] else [s0,s1,s2,s3,s4,s5,s6,s76])) else (if i < 145 then (if i < 144 then [s0,s1,s2,s3,s4,s5,s6,s7,s78] else [s0,s1,s2,s3,s4,s5,s6,s78]) else (if i < 146 then [s0,s1,s2,s3,s4,s5,s6,s7,s80] else [s0,s1,s2,s3,s4,s5,s6,s80])))) else (if i < 155 then (if i < 151 then (if i < 149 then (if i < 148 then [s0,s1,s2,s3,s4,s5,s6,s7,s82] else [s0,s1,s2,s3,s4,s5,s6,s82]) else (if i < 150 then [s0,s1,s2,s3,s4,s5,s6,s7,s84] else [s0,s1,s2,s3,s4,s5,s6,s84])) else (if i < 153 then (if i < 152 then [s0,s1,s2,s3,s4,s5,s6,s7,s86] else [s0,s1,s2,s3,s4,s5,s6,s86]) else (if i < 154 then [s0,s1,s2,s3,s4,s5,s6,s7,s22] else [s0,s1,s2,s3,s4,s5,s6,s7,s24]))) else (if i < 159 then (if i < 157 then (if i < 156 then [s0,s1,s2,s3,s4,s5,s6,s7,s26] else [s0,s1,s2,s3,s4,s5,s6,s7,s28]) else (if i < 158 then [s0,s1,s2,s3,s4,s5,s6,s7,s30] else [s0,s1,s2,s3,s4,s5,s6,s7,s32])) else (if i < 161 then (if i < 160 then [s0,s1,s2,s3,s4,s5,s6,s7,s34] else [s0,s1,s2,s3,s4,s5,s6,s7,s36]) else (if i < 162 then [s0,s1,s2,s3,s4,s5,s6,s7,s38] else (if i < 163 then [s0,s1,s2,s3,s4,s5,s6,s7,s40] else [s0,s1,s2,s3,s4,s5,s6,s7,s42])))))) else (if i < 180 then (if i < 172 then (if i < 168 then (if i < 166 then (if i < 165 then [s0,s1,s2,s3,s4,s5,s6,s7,s77] else [s0,s1,s2,s3,s4,s5,s6,s7,s23]) else (if i < 167 then [s0,s1,s2,s3,s4,s5,s6,s7,s44] else [s0,s1,s2,s3,s4,s5,s6,s7,s46])) else (if i < 170 then (if i < 169 then [s0,s1,s2,s3,s4,s5,s6,s7,s48] else [s0,s1,s2,s3,s4,s5,s6,s7,s50]) else (if i < 171 then [s0,s1,s2,s3,s4,s5,s6,s7,s79] else [s0,s1,s2,s3,s4,s5,s6,s7,s25]))) else (if i < 176 then (if i < 174 then (if i < 173 then [s0,s1,s2,s3,s4,s5,s6,s7,s35] else [s0,s1,s2,s3,s4,s5,s6,s7,s52]) else (if i < 175 then [s0,s1,s2,s3,s4,s5,s6,s7,s54] else [s0,s1,s2,s3,s4,s5,s6,s7,s56])) else (if i < 178 then (if i < 177 then [s0,s1,s2,s3,s4,s5,s6,s7,s81] else [s0,s1,s2,s3,s4,s5,s6,s7,s27]) else (if i < 179 then [s0,s1,s2,s3,s4,s5,s6,s7,s37] else [s0,s1,s2,s3,s4,s5,s6,s7,s45])))) else (if i < 188 then (if i < 184 then (if i < 182 then (if i < 181 then [s0,s1,s2,s3,s4,s5,s6,s7,s58] else [s0,s1,s2,s3,s4,s5,s6,s7,s60]) else (if i < 183 then [s0,s1,s2,s3,s4,s5,s6,s7,s83] else [s0,s1,s2,s3,s4,s5,s6,s7,s29])) else (if i < 186 then (if i < 185 then [s0,s1,s2,s3,s4,s5,s6,s7,s39] else [s0,s1,s2,s3,s4,s5,s6,s7,s47]) else (if i < 187 then [s0,s1,s2,s3,s4,s5,s6,s7,s53] else [s0,s1,s2,s3,s4,s5,s6,s7,s62]))) else (if i < 192 then (if i < 190 then (if i < 189 then [s0,s1,s2,s3,s4,s5,s6,s7,s85] else [s0,s1,s2,s3,s4,s5,s6,s7,s31]) else (if i < 191 then [s0,s1,s2,s3,s4,s5,s6,s7,s41] else [s0,s1,s2,s3,s4,s5,s6,s7,s49])) else (if i < 194 then (if i < 193 then [s0,s1,s2,s3,s4,s5,s6,s7,s55] else [s0,s1,s2,s3,s4,s5,s6,s7,s59]) else (if i < 195 then [s0,s1,s2,s3,s4,s5,s6,s7] else (if i < 196 then [s0,s1,s2,s3,s4,s5,s6,s7,s87] else [s0,s1,s2,s3,s4,s5,s6,s7,s33]))))))) else (if i < 230 then (if i < 213 then (if i < 205 then (if i < 201 then (if i < 199 then (if i < 198 then [s0,s1,s2,s3,s4,s5,s6,s7,s43] else [s0,s1,s2,s3,s4,s5,s6,s7,s51]) else (if i < 200 then [s0,s1,s2,s3,s4,s5,s6,s7,s57] else [s0,s1,s2,s3,s4,s5,s6,s7,s61])) else (if i < 203 then (if i < 202 then [s0,s1,s2,s3,s4,s5,s6,s7,s63] else [s0,s1,s2,s3,s4,s5,s6,s22]) else (if i < 204 then [s0,s1,s2,s3,s4,s5,s6,s24] else [s0,s1,s2,s3,s4,s5,s6,s26]))) else (if i < 209 then (if i < 207 then (if i < 206 then [s0,s1,s2,s3,s4,s5,s6,s28] else [s0,s1,s2,s3,s4,s5,s6,s30]) else (if i < 208 then [s0,s1,s2,s3,s4,s5,s6,s32] else [s0,s1,s2,s3,s4,s5,s6,s11])) else (if i < 211 then (if i < 210 then [s0,s1,s2,s3,s4,s5,s6,s65] else [s0,s1,s2,s3,s4,s5,s6,s34]) else (if i < 212 then [s0,s1,s2,s3,s4,s5,s6,s36] else [s0,s1,s2,s3,s4,s5,s6,s38])))) else (if i < 221 then (if i < 217 then (if i < 215 then (if i < 214 then [s0,s1,s2,s3,s4,s5,s6,s40] else [s0,s1,s2,s3,s4,s5,s6,s42]) else (if i < 216 then [s0,s1,s2,s3,s4,s5,s6,s13] else [s0,s1,s2,s3,s4,s5,s6,s67])) else (if i < 219 then (if i < 218 then [s0,s1,s2,s3,s4,s5,s6,s77] else [s0,s1,s2,s3,s4,s5,s6,s23]) else (if i < 220 then [s0,s1,s2,s3,s4,s5,s6,s44] else [s0,s1,s2,s3,s4,s5,s6,s46]))) else (if i < 225 then (if i < 223 then (if i < 222 then [s0,s1,s2,s3,s4,s5,s6,s48] else [s0,s1,s2,s3,s4,s5,s6,s50]) else (if i < 224 then [s0,s1,s2,s3,s4,s5,s6,s15] else [s0,s1,s2,s3,s4,s5,s6,s79])) else (if i < 227 then (if i < 226 then [s0,s1,s2,s3,s4,s5,s6,s25] else [s0,s1,s2,s3,s4,s5,s6,s35]) else (if i < 228 then [s0,s1,s2,s3,s4,s5,s6,s52] else (if i < 229 then [s0,s1,s2,s3,s4,s5,s6,s54] else [s0,s1,s2,s3,s4,s5,s6,s56])))))) else (if i < 246 then (if i < 238 then (if i < 234 then (if i < 232 then (if i < 231 then [s0,s1,s2,s3,s4,s5,s6,s69] else [s0,s1,s2,s3,s4,s5,s6,s81]) else (if i < 233 then [s0,s1,s2,s3,s4,s5,s6,s27] else [s0,s1,s2,s3,s4,s5,s6,s37])) else (if i < 236 then (if i < 235 then [s0,s1,s2,s3,s4,s5,s6,s45] else [s0,s1,s2,s3,s4,s5,s6,s58]) else (if i < 237 then [s0,s1,s2,s3,s4,s5,s6,s60] else [s0,s1,s2,s3,s4,s5,s6,s17]))) else (if i < 242 then (if i < 240 then (if i < 239 then [s0,s1,s2,s3,s4,s5,s6,s71] else [s0,s1,s2,s3,s4,s5,s6,s83]) else (if i < 241 then [s0,s1,s2,s3,s4,s5,s6,s29] else [s0,s1,s2,s3,s4,s5,s6,s39])) else (if i < 244 then (if i < 243 then [s0,s1,s2,s3,s4,s5,s6,s47] else [s0,s1,s2,s3,s4,s5,s6,s53]) else (if i < 245 then [s0,s1,s2,s3,s4,s5,s6,s62] else [s0,s1,s2,s3,s4,s5,s6,s19])))) else (if i < 254 then (if i < 250 then (if i < 248 then (if i < 247 then [s0,s1,s2,s3,s4,s5,s6,s73] else [s0,s1,s2,s3,s4,s5,s6,s85]) else (if i < 249 then [s0,s1,s2,s3,s4,s5,s6,s31] else [s0,s1,s2,s3,s4,s5,s6,s41])) else (if i < 252 then (if i < 251 then [s0,s1,s2,s3,s4,s5,s6,s49] else [s0,s1,s2,s3,s4,s5,s6,s55]) else (if i < 253 then [s0,s1,s2,s3,s4,s5,s6,s59] else [s0,s1,s2,s3,s4,s5,s6]))) else (if i < 258 then (if i < 256 then (if i < 255 then [s0,s1,s2,s3,s4,s5,s6,s21] else [s0,s1,s2,s3,s4,s5,s6,s75]) else (if i < 257 then [s0,s1,s2,s3,s4,s5,s6,s87] else [s0,s1,s2,s3,s4,s5,s6,s33])) else (if i < 260 then (if i < 259 then [s0,s1,s2,s3,s4,s5,s6,s43] else [s0,s1,s2,s3,s4,s5,s6,s51]) else (if i < 261 then [s0,s1,s2,s3,s4,s5,s6,s57] else (if i < 262 then [s0,s1,s2,s3,s4,s5,s6,s61] else [s0,s1,s2,s3,s4,s5,s6,s63])))))))))
private def slots_9_0 (h : Nat) : Nat :=
  (if h < 1072631617 then (if h < 534763123 then (if h < 294338933 then (if h < 134254812 then (if h < 85911322 then (if h < 58308530 then (if h < 39972531 then (if h < 21694513 then 181 else 206) else (if h < 47313625 then 127 else 124)) else (if h < 69907311 then (if h < 61663638 then 208 else 173) else (if h < 75206252 then 220 else 30))) else (if h < 108332081 then (if h < 99225538 then (if h < 93359845 then 150 else 260) else (if h < 108190022 then 104 else 171)) else (if h < 121653297 then (if h < 110609408 then 236 else 47) else (if h < 133494064 then 59 else 95)))) else (if h < 226026612 then (if h < 201561074 then (if h < 166102471 then (if h < 135285754 then 168 else 107) else (if h < 179016647 then 227 else 145)) else (if h < 212628855 then (if h < 204088184 then 29 else 65) else (if h < 216943519 then 225 else 161))) else (if h < 262708252 then (if h < 243568175 then (if h < 238693645 then 89 else 221) else (if h < 250043278 then 71 else 116)) else (if h < 283147917 then (if h < 278583952 then 138 else 182) else (if h < 283455480 then 133 else 146))))) else (if h < 441463112 then (if h < 370289548 then (if h < 327826596 then (if h < 307295026 then (if h < 295850832 then 98 else 117) else (if h < 321382352 then 91 else 212)) else (if h < 355353162 then (if h < 330465445 then 113 else 131) else (if h < 369713169 then 83 else 102))) else (if h < 408575194 then (if h < 383022785 then (if h < 373172038 then 9 else 156) else (if h < 407459354 then 239 else 39)) else (if h < 419619083 then (if h < 410655604 then 172 else 195) else (if h < 427310131 then 185 else 88)))) else (if h < 477610871 then (if h < 453065257 then (if h < 444453293 then (if h < 442843048 then 96 else 57) else (if h < 444846941 then 45 else 52)) else (if h < 457588154 then (if h < 454432423 then 255 else 84) else (if h < 469176671 then 0 else 22))) else (if h < 512429044 then (if h < 499526860 then (if h < 494322777 then 205 else 97) else (if h < 502053970 then 155 else 191)) else (if h < 513342327 then (if h < 513014027 then 130 else 226) else (if h < 515094437 then 81 else (if h < 524057916 then 256 else 242))))))) else (if h < 871581290 then (if h < 742812727 then (if h < 635560584 then (if h < 582651041 then (if h < 568841209 then (if h < 541533961 then 60 else 197) else (if h < 570170886 then 38 else 50)) else (if h < 603965693 then (if h < 584508376 then 51 else 37) else (if h < 606492803 then 204 else 250))) else (if h < 688457327 then (if h < 658889474 then (if h < 645972794 then 16 else 258) else (if h < 680737698 then 137 else 63)) else (if h < 702697812 then (if h < 700759149 then 5 else 121) else (if h < 740808834 then 40 else 183)))) else (if h < 845247667 then (if h < 784500704 then (if h < 755553940 then (if h < 743339132 then 178 else 66) else (if h < 767493918 then 2 else 77)) else (if h < 816139867 then (if h < 809863973 then 27 else 215) else (if h < 832728909 then 246 else 186))) else (if h < 855591455 then (if h < 847251560 then (if h < 846857912 then 240 else 223) else (if h < 849806304 then 233 else 49)) else (if h < 859992773 then (if h < 856625057 then 94 else 238) else (if h < 866806995 then 3 else (if h < 868136672 then 163 else 175)))))) else (if h < 971245828 then (if h < 923961057 then (if h < 884024800 then (if h < 880616827 then (if h < 877478594 then 23 else 143) else (if h < 882474162 then 177 else 162)) else (if h < 906614869 then (if h < 903804253 then 69 else 105) else (if h < 920477838 then 72 else 147))) else (if h < 944961975 then (if h < 937167742 then (if h < 927256787 then 79 else 136) else (if h < 942229023 then 243 else 118)) else (if h < 953558151 then (if h < 951154617 then 12 else 64) else (if h < 958495711 then 87 else 61)))) else (if h < 1010407624 then (if h < 985055660 then (if h < 978703484 then (if h < 972575505 then 214 else 229) else (if h < 981917427 then 189 else 144)) else (if h < 999999413 then (if h < 986912995 then 232 else 213) else (if h < 1000663598 then 110 else 165))) else (if h < 1044676150 then (if h < 1037965203 then (if h < 1024916671 then 41 else 148) else (if h < 1041304918 then 17 else 192)) else (if h < 1046525797 then (if h < 1046467840 then 32 else 44) else (if h < 1057902205 then 108 else (if h < 1072590587 then 188 else 106)))))))) else (if h < 1576294957 then (if h < 1338492217 then (if h < 1201076711 then (if h < 1155279294 then (if h < 1105102431 then (if h < 1083142317 then (if h < 1082466490 then 18 else 153) else (if h < 1086355953 then 248 else 151)) else (if h < 1145743751 then (if h < 1137208698 then 218 else 26) else (if h < 1147772090 then 251 else 174))) else (if h < 1186905323 then (if h < 1162341038 then (if h < 1161225364 then 99 else 53) else (if h < 1173890338 then 247 else 75)) else (if h < 1190794786 then (if h < 1189250104 then 202 else 82) else (if h < 1194330003 then 152 else 70)))) else (if h < 1256461497 then (if h < 1218477112 then (if h < 1205521019 then (if h < 1204580655 then 176 else 198) else (if h < 1207032918 then 35 else 54)) else (if h < 1249120403 then (if h < 1241647531 then 28 else 68) else (if h < 1252210923 then 190 else 228))) else (if h < 1305515544 then (if h < 1286429419 then (if h < 1281471634 then 187 else 8) else (if h < 1286962199 then 254 else 132)) else (if h < 1309019488 then (if h < 1308373410 then 231 else 166) else (if h < 1311507813 then 259 else (if h < 1313586868 then 93 else 170)))))) else (if h < 1447080769 then (if h < 1360900330 then (if h < 1347239269 then (if h < 1344433626 then (if h < 1342641936 then 25 else 158) else (if h < 1346910969 then 169 else 109)) else (if h < 1353559236 then (if h < 1347366594 then 80 else 13) else (if h < 1357954858 then 249 else 122))) else (if h < 1423611130 then (if h < 1412812243 then (if h < 1405504863 then 244 else 34) else (if h < 1418025701 then 219 else 224)) else (if h < 1437862635 then (if h < 1425376607 then 67 else 14) else (if h < 1440389745 then 92 else 128)))) else (if h < 1479869736 then (if h < 1463649773 then (if h < 1459128217 then (if h < 1448872459 then 207 else 222) else (if h < 1459191150 then 56 else 179)) else (if h < 1471856124 then (if h < 1465064048 then 141 else 62) else (if h < 1475036236 then 201 else 19))) else (if h < 1516442898 then (if h < 1503486805 then (if h < 1492295789 then 134 else 196) else (if h < 1504998704 then 160 else 180)) else (if h < 1563629983 then (if h < 1539613317 then 154 else 194) else (if h < 1568088606 then 234 else (if h < 1570071560 then 142 else 74))))))) else (if h < 1807909482 then (if h < 1683299874 then (if h < 1620881731 then (if h < 1601390860 then (if h < 1596734622 then (if h < 1579437420 then 262 else 10) else (if h < 1599639413 then 257 else 4)) else (if h < 1609437537 then (if h < 1607925638 then 76 else 211) else (if h < 1611941235 then 235 else 58))) else (if h < 1644052150 then (if h < 1636465564 then (if h < 1636458003 then 203 else 139) else (if h < 1641413301 then 20 else 230)) else (if h < 1679144609 then (if h < 1650036809 then 253 else 125) else (if h < 1681148502 then 120 else 115)))) else (if h < 1755049817 then (if h < 1703470649 then (if h < 1690521999 then (if h < 1683876253 then 216 else 11) else (if h < 1693889715 then 119 else 1)) else (if h < 1740896836 then (if h < 1721576916 then 159 else 193) else (if h < 1753635265 then 140 else 164))) else (if h < 1771064684 then (if h < 1766773541 then (if h < 1757857999 then 209 else 78) else (if h < 1768019128 then 31 else 85)) else (if h < 1803387558 then (if h < 1787455093 then 123 else 86) else (if h < 1805142770 then 33 else (if h < 1806472447 then 101 else 112)))))) else (if h < 1938999373 then (if h < 1858074098 then (if h < 1826015749 then (if h < 1818952602 then (if h < 1814986339 then 210 else 42) else (if h < 1820809937 then 114 else 100)) else (if h < 1838438873 then (if h < 1827781226 then 252 else 15) else (if h < 1853411109 then 73 else 55))) else (if h < 1897605199 then (if h < 1867468667 then (if h < 1861532836 then 217 else 237) else (if h < 1868037346 then 245 else 200)) else (if h < 1911181499 then (if h < 1909907021 then 6 else 184) else (if h < 1917039259 then 48 else 126)))) else (if h < 2038870183 then (if h < 1983772673 then (if h < 1972476179 then (if h < 1957707883 then 103 else 46) else (if h < 1979640693 then 261 else 129)) else (if h < 2014345854 then (if h < 2002044032 then 43 else 7) else (if h < 2020802265 then 241 else 90))) else (if h < 2086107865 then (if h < 2066461380 then (if h < 2064739327 then 21 else 157) else (if h < 2075544473 then 36 else 24)) else (if h < 2128956136 then (if h < 2112952125 then 111 else 167) else (if h < 2136404659 then 149 else (if h < 2142916430 then 199 else 135)))))))))
private def states_9_1 (i : Nat) : List Sig :=
  (if i < 238 then (if i < 119 then (if i < 59 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then [s0,s1,s2,s3,s4,s5,s9,s91] else (if i < 2 then [s0,s1,s2,s3,s4,s5,s6,s9,s91] else [s0,s1,s2,s4,s5,s9,s91])) else (if i < 5 then (if i < 4 then [s0,s1,s2,s4,s5,s6,s9,s91] else [s0,s1,s2,s3,s4,s5,s8,s91]) else (if i < 6 then [s0,s1,s2,s3,s4,s5,s6,s8,s91] else [s0,s1,s3,s4,s5,s8,s91]))) else (if i < 10 then (if i < 8 then [s0,s1,s3,s4,s5,s6,s8,s91] else (if i < 9 then [s0,s1,s2,s3,s4,s5,s7,s91] else [s0,s1,s2,s3,s4,s5,s6,s7,s91])) else (if i < 12 then (if i < 11 then [s1,s2,s3,s4,s5,s7,s91] else [s1,s2,s3,s4,s5,s6,s7,s91]) else (if i < 13 then [s0,s1,s2,s3,s4,s5,s91] else [s0,s1,s2,s3,s4,s5,s6,s91])))) else (if i < 21 then (if i < 17 then (if i < 15 then [s0,s1,s2,s3,s4,s5,s6,s9,s90] else (if i < 16 then [s0,s1,s2,s3,s4,s6,s9,s90] else [s0,s1,s2,s4,s5,s6,s9,s90])) else (if i < 19 then (if i < 18 then [s0,s1,s2,s4,s6,s9,s90] else [s0,s1,s2,s3,s4,s5,s6,s8,s90]) else (if i < 20 then [s0,s1,s2,s3,s4,s6,s8,s90] else [s0,s1,s3,s4,s5,s6,s8,s90]))) else (if i < 25 then (if i < 23 then (if i < 22 then [s0,s1,s3,s4,s6,s8,s90] else [s0,s1,s2,s3,s4,s5,s6,s7,s90]) else (if i < 24 then [s0,s1,s2,s3,s4,s6,s7,s90] else [s1,s2,s3,s4,s5,s6,s7,s90])) else (if i < 27 then (if i < 26 then [s1,s2,s3,s4,s6,s7,s90] else [s0,s1,s2,s3,s4,s5,s6,s90]) else (if i < 28 then [s0,s1,s2,s3,s4,s6,s90] else [s0,s1,s2,s3,s4,s5,s6,s9,s89]))))) else (if i < 44 then (if i < 36 then (if i < 32 then (if i < 30 then [s0,s1,s2,s3,s5,s6,s9,s89] else (if i < 31 then [s0,s1,s2,s4,s5,s6,s9,s89] else [s0,s1,s2,s5,s6,s9,s89])) else (if i < 34 then (if i < 33 then [s0,s1,s2,s3,s4,s5,s6,s8,s89] else [s0,s1,s2,s3,s5,s6,s8,s89]) else (if i < 35 then [s0,s1,s3,s4,s5,s6,s8,s89] else [s0,s1,s3,s5,s6,s8,s89]))) else (if i < 40 then (if i < 38 then (if i < 37 then [s0,s1,s2,s3,s4,s5,s6,s7,s89] else [s0,s1,s2,s3,s5,s6,s7,s89]) else (if i < 39 then [s1,s2,s3,s4,s5,s6,s7,s89] else [s1,s2,s3,s5,s6,s7,s89])) else (if i < 42 then (if i < 41 then [s0,s1,s2,s3,s4,s5,s6,s89] else [s0,s1,s2,s3,s5,s6,s89]) else (if i < 43 then [s0,s1,s2,s3,s4,s5,s6,s9,s10] else [s0,s1,s2,s4,s5,s6,s9,s10])))) else (if i < 51 then (if i < 47 then (if i < 45 then [s0,s1,s2,s3,s4,s5,s6,s10] else (if i < 46 then [s0,s1,s2,s3,s4,s5,s6,s9,s12] else [s0,s1,s2,s4,s5,s6,s9,s12])) else (if i < 49 then (if i < 48 then [s0,s1,s2,s3,s4,s5,s6,s12] else [s0,s1,s2,s3,s4,s5,s6,s9,s14]) else (if i < 50 then [s0,s1,s2,s4,s5,s6,s9,s14] else [s0,s1,s2,s3,s4,s5,s6,s14]))) else (if i < 55 then (if i < 53 then (if i < 52 then [s0,s1,s2,s3,s4,s5,s6,s9,s16] else [s0,s1,s2,s4,s5,s6,s9,s16]) else (if i < 54 then [s0,s1,s2,s3,s4,s5,s6,s16] else [s0,s1,s2,s3,s4,s5,s6,s9,s18])) else (if i < 57 then (if i < 56 then [s0,s1,s2,s4,s5,s6,s9,s18] else [s0,s1,s2,s3,s4,s5,s6,s18]) else (if i < 58 then [s0,s1,s2,s3,s4,s5,s6,s9,s20] else [s0,s1,s2,s4,s5,s6,s9,s20])))))) else (if i < 89 then (if i < 74 then (if i < 66 then (if i < 62 then (if i < 60 then [s0,s1,s2,s3,s4,s5,s6,s20] else (if i < 61 then [s0,s1,s2,s3,s4,s5,s6,s8,s9] else [s0,s1,s2,s4,s5,s6,s8,s9])) else (if i < 64 then (if i < 63 then [s0,s1,s3,s4,s5,s6,s8,s9] else [s0,s1,s4,s5,s6,s8,s9]) else (if i < 65 then [s0,s1,s2,s3,s4,s5,s6,s9,s88] else [s0,s1,s2,s4,s5,s6,s9,s88]))) else (if i < 70 then (if i < 68 then (if i < 67 then [s0,s2,s3,s4,s5,s6,s9,s88] else [s0,s2,s4,s5,s6,s9,s88]) else (if i < 69 then [s0,s1,s2,s3,s4,s5,s6,s7,s9] else [s0,s1,s2,s4,s5,s6,s7,s9])) else (if i < 72 then (if i < 71 then [s1,s2,s3,s4,s5,s6,s7,s9] else [s1,s2,s4,s5,s6,s7,s9]) else (if i < 73 then [s0,s1,s2,s3,s4,s5,s6,s9,s22] else [s0,s1,s2,s4,s5,s6,s9,s22])))) else (if i < 81 then (if i < 77 then (if i < 75 then [s0,s1,s2,s3,s4,s5,s6,s9,s24] else (if i < 76 then [s0,s1,s2,s4,s5,s6,s9,s24] else [s0,s1,s2,s3,s4,s5,s6,s9,s26])) else (if i < 79 then (if i < 78 then [s0,s1,s2,s4,s5,s6,s9,s26] else [s0,s1,s2,s3,s4,s5,s6,s9,s28]) else (if i < 80 then [s0,s1,s2,s4,s5,s6,s9,s28] else [s0,s1,s2,s3,s4,s5,s6,s9,s30]))) else (if i < 85 then (if i < 83 then (if i < 82 then [s0,s1,s2,s4,s5,s6,s9,s30] else [s0,s1,s2,s3,s4,s5,s6,s9,s32]) else (if i < 84 then [s0,s1,s2,s4,s5,s6,s9,s32] else [s0,s1,s2,s3,s4,s5,s6,s9,s11])) else (if i < 87 then (if i < 86 then [s0,s1,s2,s4,s5,s6,s9,s11] else [s0,s1,s2,s3,s4,s5,s6,s9,s34]) else (if i < 88 then [s0,s1,s2,s4,s5,s6,s9,s34] else [s0,s1,s2,s3,s4,s5,s6,s9,s36]))))) else (if i < 104 then (if i < 96 then (if i < 92 then (if i < 90 then [s0,s1,s2,s4,s5,s6,s9,s36] else (if i < 91 then [s0,s1,s2,s3,s4,s5,s6,s9,s38] else [s0,s1,s2,s4,s5,s6,s9,s38])) else (if i < 94 then (if i < 93 then [s0,s1,s2,s3,s4,s5,s6,s9,s40] else [s0,s1,s2,s4,s5,s6,s9,s40]) else (if i < 95 then [s0,s1,s2,s3,s4,s5,s6,s9,s42] else [s0,s1,s2,s4,s5,s6,s9,s42]))) else (if i < 100 then (if i < 98 then (if i < 97 then [s0,s1,s2,s3,s4,s5,s6,s9,s13] else [s0,s1,s2,s4,s5,s6,s9,s13]) else (if i < 99 then [s0,s1,s2,s3,s4,s5,s6,s9,s23] else [s0,s1,s2,s4,s5,s6,s9,s23])) else (if i < 102 then (if i < 101 then [s0,s1,s2,s3,s4,s5,s6,s9,s44] else [s0,s1,s2,s4,s5,s6,s9,s44]) else (if i < 103 then [s0,s1,s2,s3,s4,s5,s6,s9,s46] else [s0,s1,s2,s4,s5,s6,s9,s46])))) else (if i < 111 then (if i < 107 then (if i < 105 then [s0,s1,s2,s3,s4,s5,s6,s9,s48] else (if i < 106 then [s0,s1,s2,s4,s5,s6,s9,s48] else [s0,s1,s2,s3,s4,s5,s6,s9,s50])) else (if i < 109 then (if i < 108 then [s0,s1,s2,s4,s5,s6,s9,s50] else [s0,s1,s2,s3,s4,s5,s6,s9,s15]) else (if i < 110 then [s0,s1,s2,s4,s5,s6,s9,s15] else [s0,s1,s2,s3,s4,s5,s6,s9,s25]))) else (if i < 115 then (if i < 113 then (if i < 112 then [s0,s1,s2,s4,s5,s6,s9,s25] else [s0,s1,s2,s3,s4,s5,s6,s9,s35]) else (if i < 114 then [s0,s1,s2,s4,s5,s6,s9,s35] else [s0,s1,s2,s3,s4,s5,s6,s9,s52])) else (if i < 117 then (if i < 116 then [s0,s1,s2,s4,s5,s6,s9,s52] else [s0,s1,s2,s3,s4,s5,s6,s9,s54]) else (if i < 118 then [s0,s1,s2,s4,s5,s6,s9,s54] else [s0,s1,s2,s3,s4,s5,s6,s9,s56]))))))) else (if i < 178 then (if i < 148 then (if i < 133 then (if i < 126 then (if i < 122 then (if i < 120 then [s0,s1,s2,s4,s5,s6,s9,s56] else (if i < 121 then [s0,s1,s2,s3,s4,s5,s6,s9,s27] else [s0,s1,s2,s3,s4,s5,s6,s9,s37])) else (if i < 124 then (if i < 123 then [s0,s1,s2,s3,s4,s5,s6,s9,s45] else [s0,s1,s2,s3,s4,s5,s6,s9,s58]) else (if i < 125 then [s0,s1,s2,s3,s4,s5,s6,s9,s60] else [s0,s1,s2,s3,s4,s5,s6,s9,s17]))) else (if i < 129 then (if i < 127 then [s0,s1,s2,s3,s4,s5,s6,s9,s29] else (if i < 128 then [s0,s1,s2,s3,s4,s5,s6,s9,s39] else [s0,s1,s2,s3,s4,s5,s6,s9,s47])) else (if i < 131 then (if i < 130 then [s0,s1,s2,s3,s4,s5,s6,s9,s53] else [s0,s1,s2,s3,s4,s5,s6,s9,s62]) else (if i < 132 then [s0,s1,s2,s3,s4,s5,s6,s9,s19] else [s0,s1,s2,s3,s4,s5,s6,s9,s31])))) else (if i < 140 then (if i < 136 then (if i < 134 then [s0,s1,s2,s3,s4,s5,s6,s9,s41] else (if i < 135 then [s0,s1,s2,s3,s4,s5,s6,s9,s49] else [s0,s1,s2,s3,s4,s5,s6,s9,s55])) else (if i < 138 then (if i < 137 then [s0,s1,s2,s3,s4,s5,s6,s9,s59] else [s0,s1,s2,s3,s4,s5,s6,s9]) else (if i < 139 then [s0,s1,s2,s3,s4,s5,s6,s9,s21] else [s0,s1,s2,s3,s4,s5,s6,s9,s33]))) else (if i < 144 then (if i < 142 then (if i < 141 then [s0,s1,s2,s3,s4,s5,s6,s9,s43] else [s0,s1,s2,s3,s4,s5,s6,s9,s51]) else (if i < 143 then [s0,s1,s2,s3,s4,s5,s6,s9,s57] else [s0,s1,s2,s3,s4,s5,s6,s9,s61])) else (if i < 146 then (if i < 145 then [s0,s1,s2,s3,s4,s5,s6,s9,s63] else [s0,s1,s2,s4,s5,s6,s9,s27]) else (if i < 147 then [s0,s1,s2,s4,s5,s6,s9,s37] else [s0,s1,s2,s4,s5,s6,s9,s45]))))) else (if i < 163 then (if i < 155 then (if i < 151 then (if i < 149 then [s0,s1,s2,s4,s5,s6,s9,s58] else (if i < 150 then [s0,s1,s2,s4,s5,s6,s9,s60] else [s0,s1,s2,s4,s5,s6,s9,s17])) else (if i < 153 then (if i < 152 then [s0,s1,s2,s4,s5,s6,s9,s29] else [s0,s1,s2,s4,s5,s6,s9,s39]) else (if i < 154 then [s0,s1,s2,s4,s5,s6,s9,s47] else [s0,s1,s2,s4,s5,s6,s9,s53]))) else (if i < 159 then (if i < 157 then (if i < 156 then [s0,s1,s2,s4,s5,s6,s9,s62] else [s0,s1,s2,s4,s5,s6,s9,s19]) else (if i < 158 then [s0,s1,s2,s4,s5,s6,s9,s31] else [s0,s1,s2,s4,s5,s6,s9,s41])) else (if i < 161 then (if i < 160 then [s0,s1,s2,s4,s5,s6,s9,s49] else [s0,s1,s2,s4,s5,s6,s9,s55]) else (if i < 162 then [s0,s1,s2,s4,s5,s6,s9,s59] else [s0,s1,s2,s4,s5,s6,s9])))) else (if i < 170 then (if i < 166 then (if i < 164 then [s0,s1,s2,s4,s5,s6,s9,s21] else (if i < 165 then [s0,s1,s2,s4,s5,s6,s9,s33] else [s0,s1,s2,s4,s5,s6,s9,s43])) else (if i < 168 then (if i < 167 then [s0,s1,s2,s4,s5,s6,s9,s51] else [s0,s1,s2,s4,s5,s6,s9,s57]) else (if i < 169 then [s0,s1,s2,s4,s5,s6,s9,s61] else [s0,s1,s2,s4,s5,s6,s9,s63]))) else (if i < 174 then (if i < 172 then (if i < 171 then [s0,s1,s2,s3,s4,s5,s6,s8,s64] else [s0,s1,s3,s4,s5,s6,s8,s64]) else (if i < 173 then [s0,s1,s2,s3,s4,s5,s6,s64] else [s0,s1,s2,s3,s4,s5,s6,s8,s66])) else (if i < 176 then (if i < 175 then [s0,s1,s3,s4,s5,s6,s8,s66] else [s0,s1,s2,s3,s4,s5,s6,s66]) else (if i < 177 then [s0,s1,s2,s3,s4,s5,s6,s8,s68] else [s0,s1,s3,s4,s5,s6,s8,s68])))))) else (if i < 208 then (if i < 193 then (if i < 185 then (if i < 181 then (if i < 179 then [s0,s1,s2,s3,s4,s5,s6,s68] else (if i < 180 then [s0,s1,s2,s3,s4,s5,s6,s8,s70] else [s0,s1,s3,s4,s5,s6,s8,s70])) else (if i < 183 then (if i < 182 then [s0,s1,s2,s3,s4,s5,s6,s70] else [s0,s1,s2,s3,s4,s5,s6,s8,s72]) else (if i < 184 then [s0,s1,s3,s4,s5,s6,s8,s72] else [s0,s1,s2,s3,s4,s5,s6,s72]))) else (if i < 189 then (if i < 187 then (if i < 186 then [s0,s1,s2,s3,s4,s5,s6,s8,s74] else [s0,s1,s3,s4,s5,s6,s8,s74]) else (if i < 188 then [s0,s1,s2,s3,s4,s5,s6,s74] else [s0,s1,s2,s3,s4,s5,s6,s8,s88])) else (if i < 191 then (if i < 190 then [s0,s1,s3,s4,s5,s6,s8,s88] else [s0,s2,s3,s4,s5,s6,s8,s88]) else (if i < 192 then [s0,s3,s4,s5,s6,s8,s88] else [s0,s1,s2,s3,s4,s5,s6,s7,s8])))) else (if i < 200 then (if i < 196 then (if i < 194 then [s0,s1,s3,s4,s5,s6,s7,s8] else (if i < 195 then [s1,s2,s3,s4,s5,s6,s7,s8] else [s1,s3,s4,s5,s6,s7,s8])) else (if i < 198 then (if i < 197 then [s0,s1,s2,s3,s4,s5,s6,s8,s22] else [s0,s1,s3,s4,s5,s6,s8,s22]) else (if i < 199 then [s0,s1,s2,s3,s4,s5,s6,s8,s24] else [s0,s1,s3,s4,s5,s6,s8,s24]))) else (if i < 204 then (if i < 202 then (if i < 201 then [s0,s1,s2,s3,s4,s5,s6,s8,s26] else [s0,s1,s3,s4,s5,s6,s8,s26]) else (if i < 203 then [s0,s1,s2,s3,s4,s5,s6,s8,s28] else [s0,s1,s3,s4,s5,s6,s8,s28])) else (if i < 206 then (if i < 205 then [s0,s1,s2,s3,s4,s5,s6,s8,s30] else [s0,s1,s3,s4,s5,s6,s8,s30]) else (if i < 207 then [s0,s1,s2,s3,s4,s5,s6,s8,s32] else [s0,s1,s3,s4,s5,s6,s8,s32]))))) else (if i < 223 then (if i < 215 then (if i < 211 then (if i < 209 then [s0,s1,s2,s3,s4,s5,s6,s8,s65] else (if i < 210 then [s0,s1,s3,s4,s5,s6,s8,s65] else [s0,s1,s2,s3,s4,s5,s6,s8,s34])) else (if i < 213 then (if i < 212 then [s0,s1,s3,s4,s5,s6,s8,s34] else [s0,s1,s2,s3,s4,s5,s6,s8,s36]) else (if i < 214 then [s0,s1,s3,s4,s5,s6,s8,s36] else [s0,s1,s2,s3,s4,s5,s6,s8,s38]))) else (if i < 219 then (if i < 217 then (if i < 216 then [s0,s1,s3,s4,s5,s6,s8,s38] else [s0,s1,s2,s3,s4,s5,s6,s8,s40]) else (if i < 218 then [s0,s1,s3,s4,s5,s6,s8,s40] else [s0,s1,s2,s3,s4,s5,s6,s8,s42])) else (if i < 221 then (if i < 220 then [s0,s1,s3,s4,s5,s6,s8,s42] else [s0,s1,s2,s3,s4,s5,s6,s8,s67]) else (if i < 222 then [s0,s1,s3,s4,s5,s6,s8,s67] else [s0,s1,s2,s3,s4,s5,s6,s8,s23])))) else (if i < 230 then (if i < 226 then (if i < 224 then [s0,s1,s3,s4,s5,s6,s8,s23] else (if i < 225 then [s0,s1,s2,s3,s4,s5,s6,s8,s44] else [s0,s1,s3,s4,s5,s6,s8,s44])) else (if i < 228 then (if i < 227 then [s0,s1,s2,s3,s4,s5,s6,s8,s46] else [s0,s1,s3,s4,s5,s6,s8,s46]) else (if i < 229 then [s0,s1,s2,s3,s4,s5,s6,s8,s48] else [s0,s1,s3,s4,s5,s6,s8,s48]))) else (if i < 234 then (if i < 232 then (if i < 231 then [s0,s1,s2,s3,s4,s5,s6,s8,s50] else [s0,s1,s3,s4,s5,s6,s8,s50]) else (if i < 233 then [s0,s1,s2,s3,s4,s5,s6,s8,s25] else [s0,s1,s2,s3,s4,s5,s6,s8,s35])) else (if i < 236 then (if i < 235 then [s0,s1,s2,s3,s4,s5,s6,s8,s52] else [s0,s1,s2,s3,s4,s5,s6,s8,s54]) else (if i < 237 then [s0,s1,s2,s3,s4,s5,s6,s8,s56] else [s0,s1,s2,s3,s4,s5,s6,s8,s69])))))))) else (if i < 357 then (if i < 297 then (if i < 267 then (if i < 252 then (if i < 245 then (if i < 241 then (if i < 239 then [s0,s1,s2,s3,s4,s5,s6,s8,s27] else (if i < 240 then [s0,s1,s2,s3,s4,s5,s6,s8,s37] else [s0,s1,s2,s3,s4,s5,s6,s8,s45])) else (if i < 243 then (if i < 242 then [s0,s1,s2,s3,s4,s5,s6,s8,s58] else [s0,s1,s2,s3,s4,s5,s6,s8,s60]) else (if i < 244 then [s0,s1,s2,s3,s4,s5,s6,s8,s71] else [s0,s1,s2,s3,s4,s5,s6,s8,s29]))) else (if i < 248 then (if i < 246 then [s0,s1,s2,s3,s4,s5,s6,s8,s39] else (if i < 247 then [s0,s1,s2,s3,s4,s5,s6,s8,s47] else [s0,s1,s2,s3,s4,s5,s6,s8,s53])) else (if i < 250 then (if i < 249 then [s0,s1,s2,s3,s4,s5,s6,s8,s62] else [s0,s1,s2,s3,s4,s5,s6,s8,s73]) else (if i < 251 then [s0,s1,s2,s3,s4,s5,s6,s8,s31] else [s0,s1,s2,s3,s4,s5,s6,s8,s41])))) else (if i < 259 then (if i < 255 then (if i < 253 then [s0,s1,s2,s3,s4,s5,s6,s8,s49] else (if i < 254 then [s0,s1,s2,s3,s4,s5,s6,s8,s55] else [s0,s1,s2,s3,s4,s5,s6,s8,s59])) else (if i < 257 then (if i < 256 then [s0,s1,s2,s3,s4,s5,s6,s8] else [s0,s1,s2,s3,s4,s5,s6,s8,s75]) else (if i < 258 then [s0,s1,s2,s3,s4,s5,s6,s8,s33] else [s0,s1,s2,s3,s4,s5,s6,s8,s43]))) else (if i < 263 then (if i < 261 then (if i < 260 then [s0,s1,s2,s3,s4,s5,s6,s8,s51] else [s0,s1,s2,s3,s4,s5,s6,s8,s57]) else (if i < 262 then [s0,s1,s2,s3,s4,s5,s6,s8,s61] else [s0,s1,s2,s3,s4,s5,s6,s8,s63])) else (if i < 265 then (if i < 264 then [s0,s1,s3,s4,s5,s6,s8,s25] else [s0,s1,s3,s4,s5,s6,s8,s35]) else (if i < 266 then [s0,s1,s3,s4,s5,s6,s8,s52] else [s0,s1,s3,s4,s5,s6,s8,s54]))))) else (if i < 282 then (if i < 274 then (if i < 270 then (if i < 268 then [s0,s1,s3,s4,s5,s6,s8,s56] else (if i < 269 then [s0,s1,s3,s4,s5,s6,s8,s69] else [s0,s1,s3,s4,s5,s6,s8,s27])) else (if i < 272 then (if i < 271 then [s0,s1,s3,s4,s5,s6,s8,s37] else [s0,s1,s3,s4,s5,s6,s8,s45]) else (if i < 273 then [s0,s1,s3,s4,s5,s6,s8,s58] else [s0,s1,s3,s4,s5,s6,s8,s60]))) else (if i < 278 then (if i < 276 then (if i < 275 then [s0,s1,s3,s4,s5,s6,s8,s71] else [s0,s1,s3,s4,s5,s6,s8,s29]) else (if i < 277 then [s0,s1,s3,s4,s5,s6,s8,s39] else [s0,s1,s3,s4,s5,s6,s8,s47])) else (if i < 280 then (if i < 279 then [s0,s1,s3,s4,s5,s6,s8,s53] else [s0,s1,s3,s4,s5,s6,s8,s62]) else (if i < 281 then [s0,s1,s3,s4,s5,s6,s8,s73] else [s0,s1,s3,s4,s5,s6,s8,s31])))) else (if i < 289 then (if i < 285 then (if i < 283 then [s0,s1,s3,s4,s5,s6,s8,s41] else (if i < 284 then [s0,s1,s3,s4,s5,s6,s8,s49] else [s0,s1,s3,s4,s5,s6,s8,s55])) else (if i < 287 then (if i < 286 then [s0,s1,s3,s4,s5,s6,s8,s59] else [s0,s1,s3,s4,s5,s6,s8]) else (if i < 288 then [s0,s1,s3,s4,s5,s6,s8,s75] else [s0,s1,s3,s4,s5,s6,s8,s33]))) else (if i < 293 then (if i < 291 then (if i < 290 then [s0,s1,s3,s4,s5,s6,s8,s43] else [s0,s1,s3,s4,s5,s6,s8,s51]) else (if i < 292 then [s0,s1,s3,s4,s5,s6,s8,s57] else [s0,s1,s3,s4,s5,s6,s8,s61])) else (if i < 295 then (if i < 294 then [s0,s1,s3,s4,s5,s6,s8,s63] else [s0,s1,s2,s3,s4,s5,s6,s7,s88]) else (if i < 296 then [s0,s2,s3,s4,s5,s6,s7,s88] else [s1,s2,s3,s4,s5,s6,s7,s88])))))) else (if i < 327 then (if i < 312 then (if i < 304 then (if i < 300 then (if i < 298 then [s2,s3,s4,s5,s6,s7,s88] else (if i < 299 then [s0,s1,s2,s3,s4,s5,s6,s88] else [s0,s2,s3,s4,s5,s6,s88])) else (if i < 302 then (if i < 301 then [s0,s1,s2,s3,s4,s5,s6,s7,s76] else [s1,s2,s3,s4,s5,s6,s7,s76]) else (if i < 303 then [s0,s1,s2,s3,s4,s5,s6,s76] else [s0,s1,s2,s3,s4,s5,s6,s7,s78]))) else (if i < 308 then (if i < 306 then (if i < 305 then [s1,s2,s3,s4,s5,s6,s7,s78] else [s0,s1,s2,s3,s4,s5,s6,s78]) else (if i < 307 then [s0,s1,s2,s3,s4,s5,s6,s7,s80] else [s1,s2,s3,s4,s5,s6,s7,s80])) else (if i < 310 then (if i < 309 then [s0,s1,s2,s3,s4,s5,s6,s80] else [s0,s1,s2,s3,s4,s5,s6,s7,s82]) else (if i < 311 then [s1,s2,s3,s4,s5,s6,s7,s82] else [s0,s1,s2,s3,s4,s5,s6,s82])))) else (if i < 319 then (if i < 315 then (if i < 313 then [s0,s1,s2,s3,s4,s5,s6,s7,s84] else (if i < 314 then [s1,s2,s3,s4,s5,s6,s7,s84] else [s0,s1,s2,s3,s4,s5,s6,s84])) else (if i < 317 then (if i < 316 then [s0,s1,s2,s3,s4,s5,s6,s7,s86] else [s1,s2,s3,s4,s5,s6,s7,s86]) else (if i < 318 then [s0,s1,s2,s3,s4,s5,s6,s86] else [s0,s1,s2,s3,s4,s5,s6,s7,s22]))) else (if i < 323 then (if i < 321 then (if i < 320 then [s1,s2,s3,s4,s5,s6,s7,s22] else [s0,s1,s2,s3,s4,s5,s6,s7,s24]) else (if i < 322 then [s1,s2,s3,s4,s5,s6,s7,s24] else [s0,s1,s2,s3,s4,s5,s6,s7,s26])) else (if i < 325 then (if i < 324 then [s1,s2,s3,s4,s5,s6,s7,s26] else [s0,s1,s2,s3,s4,s5,s6,s7,s28]) else (if i < 326 then [s1,s2,s3,s4,s5,s6,s7,s28] else [s0,s1,s2,s3,s4,s5,s6,s7,s30]))))) else (if i < 342 then (if i < 334 then (if i < 330 then (if i < 328 then [s1,s2,s3,s4,s5,s6,s7,s30] else (if i < 329 then [s0,s1,s2,s3,s4,s5,s6,s7,s32] else [s1,s2,s3,s4,s5,s6,s7,s32])) else (if i < 332 then (if i < 331 then [s0,s1,s2,s3,s4,s5,s6,s7,s34] else [s0,s1,s2,s3,s4,s5,s6,s7,s36]) else (if i < 333 then [s0,s1,s2,s3,s4,s5,s6,s7,s38] else [s0,s1,s2,s3,s4,s5,s6,s7,s40]))) else (if i < 338 then (if i < 336 then (if i < 335 then [s0,s1,s2,s3,s4,s5,s6,s7,s42] else [s0,s1,s2,s3,s4,s5,s6,s7,s77]) else (if i < 337 then [s0,s1,s2,s3,s4,s5,s6,s7,s23] else [s0,s1,s2,s3,s4,s5,s6,s7,s44])) else (if i < 340 then (if i < 339 then [s0,s1,s2,s3,s4,s5,s6,s7,s46] else [s0,s1,s2,s3,s4,s5,s6,s7,s48]) else (if i < 341 then [s0,s1,s2,s3,s4,s5,s6,s7,s50] else [s0,s1,s2,s3,s4,s5,s6,s7,s79])))) else (if i < 349 then (if i < 345 then (if i < 343 then [s0,s1,s2,s3,s4,s5,s6,s7,s25] else (if i < 344 then [s0,s1,s2,s3,s4,s5,s6,s7,s35] else [s0,s1,s2,s3,s4,s5,s6,s7,s52])) else (if i < 347 then (if i < 346 then [s0,s1,s2,s3,s4,s5,s6,s7,s54] else [s0,s1,s2,s3,s4,s5,s6,s7,s56]) else (if i < 348 then [s0,s1,s2,s3,s4,s5,s6,s7,s81] else [s0,s1,s2,s3,s4,s5,s6,s7,s27]))) else (if i < 353 then (if i < 351 then (if i < 350 then [s0,s1,s2,s3,s4,s5,s6,s7,s37] else [s0,s1,s2,s3,s4,s5,s6,s7,s45]) else (if i < 352 then [s0,s1,s2,s3,s4,s5,s6,s7,s58] else [s0,s1,s2,s3,s4,s5,s6,s7,s60])) else (if i < 355 then (if i < 354 then [s0,s1,s2,s3,s4,s5,s6,s7,s83] else [s0,s1,s2,s3,s4,s5,s6,s7,s29]) else (if i < 356 then [s0,s1,s2,s3,s4,s5,s6,s7,s39] else [s0,s1,s2,s3,s4,s5,s6,s7,s47]))))))) else (if i < 417 then (if i < 387 then (if i < 372 then (if i < 364 then (if i < 360 then (if i < 358 then [s0,s1,s2,s3,s4,s5,s6,s7,s53] else (if i < 359 then [s0,s1,s2,s3,s4,s5,s6,s7,s62] else [s0,s1,s2,s3,s4,s5,s6,s7,s85])) else (if i < 362 then (if i < 361 then [s0,s1,s2,s3,s4,s5,s6,s7,s31] else [s0,s1,s2,s3,s4,s5,s6,s7,s41]) else (if i < 363 then [s0,s1,s2,s3,s4,s5,s6,s7,s49] else [s0,s1,s2,s3,s4,s5,s6,s7,s55]))) else (if i < 368 then (if i < 366 then (if i < 365 then [s0,s1,s2,s3,s4,s5,s6,s7,s59] else [s0,s1,s2,s3,s4,s5,s6,s7]) else (if i < 367 then [s0,s1,s2,s3,s4,s5,s6,s7,s87] else [s0,s1,s2,s3,s4,s5,s6,s7,s33])) else (if i < 370 then (if i < 369 then [s0,s1,s2,s3,s4,s5,s6,s7,s43] else [s0,s1,s2,s3,s4,s5,s6,s7,s51]) else (if i < 371 then [s0,s1,s2,s3,s4,s5,s6,s7,s57] else [s0,s1,s2,s3,s4,s5,s6,s7,s61])))) else (if i < 379 then (if i < 375 then (if i < 373 then [s0,s1,s2,s3,s4,s5,s6,s7,s63] else (if i < 374 then [s1,s2,s3,s4,s5,s6,s7,s34] else [s1,s2,s3,s4,s5,s6,s7,s36])) else (if i < 377 then (if i < 376 then [s1,s2,s3,s4,s5,s6,s7,s38] else [s1,s2,s3,s4,s5,s6,s7,s40]) else (if i < 378 then [s1,s2,s3,s4,s5,s6,s7,s42] else [s1,s2,s3,s4,s5,s6,s7,s77]))) else (if i < 383 then (if i < 381 then (if i < 380 then [s1,s2,s3,s4,s5,s6,s7,s23] else [s1,s2,s3,s4,s5,s6,s7,s44]) else (if i < 382 then [s1,s2,s3,s4,s5,s6,s7,s46] else [s1,s2,s3,s4,s5,s6,s7,s48])) else (if i < 385 then (if i < 384 then [s1,s2,s3,s4,s5,s6,s7,s50] else [s1,s2,s3,s4,s5,s6,s7,s79]) else (if i < 386 then [s1,s2,s3,s4,s5,s6,s7,s25] else [s1,s2,s3,s4,s5,s6,s7,s35]))))) else (if i < 402 then (if i < 394 then (if i < 390 then (if i < 388 then [s1,s2,s3,s4,s5,s6,s7,s52] else (if i < 389 then [s1,s2,s3,s4,s5,s6,s7,s54] else [s1,s2,s3,s4,s5,s6,s7,s56])) else (if i < 392 then (if i < 391 then [s1,s2,s3,s4,s5,s6,s7,s81] else [s1,s2,s3,s4,s5,s6,s7,s27]) else (if i < 393 then [s1,s2,s3,s4,s5,s6,s7,s37] else [s1,s2,s3,s4,s5,s6,s7,s45]))) else (if i < 398 then (if i < 396 then (if i < 395 then [s1,s2,s3,s4,s5,s6,s7,s58] else [s1,s2,s3,s4,s5,s6,s7,s60]) else (if i < 397 then [s1,s2,s3,s4,s5,s6,s7,s83] else [s1,s2,s3,s4,s5,s6,s7,s29])) else (if i < 400 then (if i < 399 then [s1,s2,s3,s4,s5,s6,s7,s39] else [s1,s2,s3,s4,s5,s6,s7,s47]) else (if i < 401 then [s1,s2,s3,s4,s5,s6,s7,s53] else [s1,s2,s3,s4,s5,s6,s7,s62])))) else (if i < 409 then (if i < 405 then (if i < 403 then [s1,s2,s3,s4,s5,s6,s7,s85] else (if i < 404 then [s1,s2,s3,s4,s5,s6,s7,s31] else [s1,s2,s3,s4,s5,s6,s7,s41])) else (if i < 407 then (if i < 406 then [s1,s2,s3,s4,s5,s6,s7,s49] else [s1,s2,s3,s4,s5,s6,s7,s55]) else (if i < 408 then [s1,s2,s3,s4,s5,s6,s7,s59] else [s1,s2,s3,s4,s5,s6,s7]))) else (if i < 413 then (if i < 411 then (if i < 410 then [s1,s2,s3,s4,s5,s6,s7,s87] else [s1,s2,s3,s4,s5,s6,s7,s33]) else (if i < 412 then [s1,s2,s3,s4,s5,s6,s7,s43] else [s1,s2,s3,s4,s5,s6,s7,s51])) else (if i < 415 then (if i < 414 then [s1,s2,s3,s4,s5,s6,s7,s57] else [s1,s2,s3,s4,s5,s6,s7,s61]) else (if i < 416 then [s1,s2,s3,s4,s5,s6,s7,s63] else [s0,s1,s2,s3,s4,s5,s6,s22])))))) else (if i < 447 then (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then [s0,s1,s2,s3,s4,s5,s6,s24] else (if i < 419 then [s0,s1,s2,s3,s4,s5,s6,s26] else [s0,s1,s2,s3,s4,s5,s6,s28])) else (if i < 422 then (if i < 421 then [s0,s1,s2,s3,s4,s5,s6,s30] else [s0,s1,s2,s3,s4,s5,s6,s32]) else (if i < 423 then [s0,s1,s2,s3,s4,s5,s6,s11] else [s0,s1,s2,s3,s4,s5,s6,s65]))) else (if i < 428 then (if i < 426 then (if i < 425 then [s0,s1,s2,s3,s4,s5,s6,s34] else [s0,s1,s2,s3,s4,s5,s6,s36]) else (if i < 427 then [s0,s1,s2,s3,s4,s5,s6,s38] else [s0,s1,s2,s3,s4,s5,s6,s40])) else (if i < 430 then (if i < 429 then [s0,s1,s2,s3,s4,s5,s6,s42] else [s0,s1,s2,s3,s4,s5,s6,s13]) else (if i < 431 then [s0,s1,s2,s3,s4,s5,s6,s67] else [s0,s1,s2,s3,s4,s5,s6,s77])))) else (if i < 439 then (if i < 435 then (if i < 433 then [s0,s1,s2,s3,s4,s5,s6,s23] else (if i < 434 then [s0,s1,s2,s3,s4,s5,s6,s44] else [s0,s1,s2,s3,s4,s5,s6,s46])) else (if i < 437 then (if i < 436 then [s0,s1,s2,s3,s4,s5,s6,s48] else [s0,s1,s2,s3,s4,s5,s6,s50]) else (if i < 438 then [s0,s1,s2,s3,s4,s5,s6,s15] else [s0,s1,s2,s3,s4,s5,s6,s79]))) else (if i < 443 then (if i < 441 then (if i < 440 then [s0,s1,s2,s3,s4,s5,s6,s25] else [s0,s1,s2,s3,s4,s5,s6,s35]) else (if i < 442 then [s0,s1,s2,s3,s4,s5,s6,s52] else [s0,s1,s2,s3,s4,s5,s6,s54])) else (if i < 445 then (if i < 444 then [s0,s1,s2,s3,s4,s5,s6,s56] else [s0,s1,s2,s3,s4,s5,s6,s69]) else (if i < 446 then [s0,s1,s2,s3,s4,s5,s6,s81] else [s0,s1,s2,s3,s4,s5,s6,s27]))))) else (if i < 462 then (if i < 454 then (if i < 450 then (if i < 448 then [s0,s1,s2,s3,s4,s5,s6,s37] else (if i < 449 then [s0,s1,s2,s3,s4,s5,s6,s45] else [s0,s1,s2,s3,s4,s5,s6,s58])) else (if i < 452 then (if i < 451 then [s0,s1,s2,s3,s4,s5,s6,s60] else [s0,s1,s2,s3,s4,s5,s6,s17]) else (if i < 453 then [s0,s1,s2,s3,s4,s5,s6,s71] else [s0,s1,s2,s3,s4,s5,s6,s83]))) else (if i < 458 then (if i < 456 then (if i < 455 then [s0,s1,s2,s3,s4,s5,s6,s29] else [s0,s1,s2,s3,s4,s5,s6,s39]) else (if i < 457 then [s0,s1,s2,s3,s4,s5,s6,s47] else [s0,s1,s2,s3,s4,s5,s6,s53])) else (if i < 460 then (if i < 459 then [s0,s1,s2,s3,s4,s5,s6,s62] else [s0,s1,s2,s3,s4,s5,s6,s19]) else (if i < 461 then [s0,s1,s2,s3,s4,s5,s6,s73] else [s0,s1,s2,s3,s4,s5,s6,s85])))) else (if i < 469 then (if i < 465 then (if i < 463 then [s0,s1,s2,s3,s4,s5,s6,s31] else (if i < 464 then [s0,s1,s2,s3,s4,s5,s6,s41] else [s0,s1,s2,s3,s4,s5,s6,s49])) else (if i < 467 then (if i < 466 then [s0,s1,s2,s3,s4,s5,s6,s55] else [s0,s1,s2,s3,s4,s5,s6,s59]) else (if i < 468 then [s0,s1,s2,s3,s4,s5,s6] else [s0,s1,s2,s3,s4,s5,s6,s21]))) else (if i < 473 then (if i < 471 then (if i < 470 then [s0,s1,s2,s3,s4,s5,s6,s75] else [s0,s1,s2,s3,s4,s5,s6,s87]) else (if i < 472 then [s0,s1,s2,s3,s4,s5,s6,s33] else [s0,s1,s2,s3,s4,s5,s6,s43])) else (if i < 475 then (if i < 474 then [s0,s1,s2,s3,s4,s5,s6,s51] else [s0,s1,s2,s3,s4,s5,s6,s57]) else (if i < 476 then [s0,s1,s2,s3,s4,s5,s6,s61] else [s0,s1,s2,s3,s4,s5,s6,s63])))))))))
private def slots_9_1 (h : Nat) : Nat :=
  (if h < 1105102431 then (if h < 582651041 then (if h < 266289777 then (if h < 133494064 then (if h < 82667515 then (if h < 58308530 then (if h < 25687341 then (if h < 7539144 then 352 else (if h < 21694513 then 162 else 420)) else (if h < 47313625 then (if h < 39972531 then 307 else 251) else (if h < 47363247 then 248 else 30))) else (if h < 63614213 then (if h < 58650849 then 422 else (if h < 61663638 then 193 else 344)) else (if h < 72697306 then (if h < 69907311 then 375 else 434) else (if h < 75206252 then 194 else 78)))) else (if h < 108190022 then (if h < 93359845 then (if h < 85911322 then 271 else (if h < 89536739 then 314 else 295)) else (if h < 99225538 then (if h < 95332489 then 474 else 293) else (if h < 104383830 then 224 else 65))) else (if h < 121653297 then (if h < 110609408 then (if h < 108332081 then 342 else 450) else (if h < 115772154 then 112 else 288)) else (if h < 126963170 then (if h < 125254646 then 128 else 396) else (if h < 128475069 then 213 else 272))))) else (if h < 202913785 then (if h < 166102471 then (if h < 139919263 then (if h < 134254812 then 206 else (if h < 135285754 then 339 else 230)) else (if h < 160450833 then (if h < 143770346 then 199 else 17) else (if h < 163089682 then 268 else 286))) else (if h < 191268220 then (if h < 179016647 then (if h < 171396476 then 441 else 87) else (if h < 189502743 then 306 else 161)) else (if h < 201561074 then (if h < 193975572 then 46 else 299) else (if h < 202337406 then 76 else 221)))) else (if h < 230955661 then (if h < 216943519 then (if h < 204088184 then 34 else (if h < 212628855 then 134 else 439)) else (if h < 225019830 then (if h < 219842732 then 332 else 325) else (if h < 226026612 then 150 else 192))) else (if h < 255245888 then (if h < 243568175 then (if h < 238693645 then 156 else 435) else (if h < 250043278 then 140 else 240)) else (if h < 259934368 then (if h < 257326298 then 386 else 409) else (if h < 262708252 then 189 else 262)))))) else (if h < 419619083 then (if h < 345053281 then (if h < 295850832 then (if h < 283147917 then (if h < 274087349 then 399 else (if h < 278583952 then 209 else 353)) else (if h < 287056660 then (if h < 283455480 then 257 else 308) else (if h < 294338933 then 183 else 212))) else (if h < 326947014 then (if h < 307295026 then (if h < 299320884 then 241 else 21) else (if h < 321382352 then 198 else 426)) else (if h < 330465445 then (if h < 327826596 then 211 else 237) else (if h < 335963173 then 255 else 168)))) else (if h < 373172038 then (if h < 355353162 then (if h < 346197554 then 285 else (if h < 348724664 then 323 else 405)) else (if h < 369713169 then (if h < 365531026 then 181 else 16) else (if h < 370289548 then 220 else 32))) else (if h < 402357177 then (if h < 383022785 then (if h < 377832848 then 324 else 152) else (if h < 388204655 then 453 else 411)) else (if h < 408575194 then (if h < 407459354 then 55 else 96) else (if h < 410655604 then 343 else 366))))) else (if h < 502053970 then (if h < 454432423 then (if h < 442843048 then (if h < 427310131 then 356 else (if h < 441463112 then 188 else 208)) else (if h < 444846941 then (if h < 444453293 then 126 else 108) else (if h < 453065257 then 121 else 469))) else (if h < 477610871 then (if h < 466696647 then (if h < 457588154 then 182 else 1) else (if h < 469176671 then 19 else 57)) else (if h < 494322777 then (if h < 491513711 then 419 else 292) else (if h < 499526860 then 210 else 322)))) else (if h < 532665154 then (if h < 513342327 then (if h < 512429044 then 362 else (if h < 513014027 then 254 else 440)) else (if h < 521081564 then (if h < 515094437 then 178 else 470) else (if h < 524057916 then 20 else 456))) else (if h < 568841209 then (if h < 534763123 then (if h < 533383386 then 81 else 276) else (if h < 541533961 then 129 else 368)) else (if h < 570170886 then (if h < 569279171 then 94 else 85) else (if h < 580877952 then 118 else 103))))))) else (if h < 868136672 then (if h < 736428490 then (if h < 674060323 then (if h < 606492803 then (if h < 589483421 then (if h < 584508376 then 120 else (if h < 587479528 then 92 else 397)) else (if h < 603965693 then (if h < 602224634 then 392 else 11) else (if h < 604330486 then 418 else 167))) else (if h < 635560584 then (if h < 606672324 then 464 else (if h < 619302722 then 0 else 149)) else (if h < 658889474 then (if h < 645972794 then 48 else 472) else (if h < 664347067 then 261 else 29)))) else (if h < 702697812 then (if h < 680737698 then (if h < 677073112 then 63 else (if h < 679399603 then 115 else 400)) else (if h < 688457327 then (if h < 688215692 then 132 else 205) else (if h < 700759149 then 18 else 245))) else (if h < 723599496 then (if h < 713477689 then (if h < 704946213 then 98 else 67) else (if h < 714807366 then 377 else 389)) else (if h < 727287521 then (if h < 724149288 then 111 else 304) else (if h < 729144856 then 391 else 376))))) else (if h < 825374178 then (if h < 759881024 then (if h < 743339132 then (if h < 740808834 then 227 else (if h < 742812727 then 354 else 349)) else (if h < 751308804 then (if h < 749664286 then 135 else 105) else (if h < 755553940 then 10 else 9))) else (if h < 784500704 then (if h < 767493918 then (if h < 767148532 then 291 else 310) else (if h < 774853260 then 172 else 273)) else (if h < 809863973 then (if h < 808983547 then 72 else 39) else (if h < 816139867 then 429 else 460)))) else (if h < 847251560 then (if h < 832728909 then (if h < 832352993 then 403 else (if h < 832623650 then 91 else 265)) else (if h < 845247667 then (if h < 841436086 then 357 else 61) else (if h < 846857912 then 454 else 437))) else (if h < 856625057 then (if h < 849806304 then (if h < 847334292 then 447 else 379) else (if h < 855591455 then 116 else 204)) else (if h < 860496751 then (if h < 859992773 then 452 else 13) else (if h < 866806995 then 191 else 334)))))) else (if h < 985055660 then (if h < 927256787 then (if h < 887975612 then (if h < 879150034 then (if h < 871581290 then 346 else (if h < 877478594 then 59 else 303)) else (if h < 882474162 then (if h < 880616827 then 263 else 348) else (if h < 884024800 then 333 else 138))) else (if h < 905214824 then (if h < 904572899 then (if h < 903804253 then 406 else 226) else (if h < 904638110 then 402 else 8)) else (if h < 920477838 then (if h < 906614869 then 229 else 141) else (if h < 923961057 then 309 else 175)))) else (if h < 953558151 then (if h < 937167742 then (if h < 929137184 then 260 else (if h < 933026647 then 319 else 316)) else (if h < 944961975 then (if h < 942229023 then 457 else 242) else (if h < 951154617 then 42 else 133))) else (if h < 972575505 then (if h < 962312853 then (if h < 958495711 then 187 else 130) else (if h < 971245828 then 37 else 428)) else (if h < 981917427 then (if h < 978703484 then 443 else 360) else (if h < 983879392 then 305 else 70))))) else (if h < 1041304918 then (if h < 1009076943 then (if h < 988581512 then (if h < 986912995 then 446 else (if h < 987903531 then 427 else 215)) else (if h < 999999413 then (if h < 994442784 then 79 else 388) else (if h < 1000663598 then 234 else 336))) else (if h < 1024916671 then (if h < 1021874341 then (if h < 1010407624 then 12 else 100) else (if h < 1023984668 then 180 else 113)) else (if h < 1035028557 then (if h < 1027872514 then 311 else 190) else (if h < 1037965203 then 153 else 50)))) else (if h < 1066751686 then (if h < 1046525797 then (if h < 1044676150 then 363 else (if h < 1046467840 then 82 else 106)) else (if h < 1051251349 then (if h < 1047747405 then 232 else 390) else (if h < 1057902205 then 412 else 359))) else (if h < 1083142317 then (if h < 1072631617 then (if h < 1072590587 then 41 else 228) else (if h < 1082466490 then 51 else 318)) else (if h < 1095791097 then (if h < 1086355953 then 462 else 315) else (if h < 1103132191 then 404 else 401)))))))) else (if h < 1603688921 then (if h < 1357828553 then (if h < 1241647531 then (if h < 1173890338 then (if h < 1147772090 then (if h < 1119586436 then (if h < 1114936334 then 432 else (if h < 1117463444 then 77 else 159)) else (if h < 1144132050 then (if h < 1137208698 then 287 else 68) else (if h < 1145743751 then 203 else 465))) else (if h < 1156943435 then (if h < 1155044104 then 345 else (if h < 1155279294 then 380 else 214)) else (if h < 1161225364 then (if h < 1160257562 then 165 else 384) else (if h < 1162341038 then 122 else 461)))) else (if h < 1190794786 then (if h < 1186905323 then (if h < 1179535206 then 144 else (if h < 1179863506 then 264 else 177)) else (if h < 1189312630 then (if h < 1189250104 then 416 else 179) else (if h < 1190579095 then 329 else 277))) else (if h < 1204580655 then (if h < 1194330003 then (if h < 1191104320 then 317 else 383) else (if h < 1201076711 then 139 else 347)) else (if h < 1207032918 then (if h < 1205521019 then 369 else 88) else (if h < 1218477112 then 123 else 74))))) else (if h < 1312493973 then (if h < 1286429419 then (if h < 1256461497 then (if h < 1249120403 then 137 else (if h < 1252210923 then 361 else 442)) else (if h < 1273013982 then (if h < 1270486872 then 358 else 201) else (if h < 1281471634 then 283 else 28))) else (if h < 1308373410 then (if h < 1305515544 then (if h < 1286962199 then 468 else 256) else (if h < 1305861844 then 445 else 393)) else (if h < 1310320467 then (if h < 1309019488 then 337 else 473) else (if h < 1311507813 then 301 else 202)))) else (if h < 1344433626 then (if h < 1320834614 then (if h < 1313586868 then 289 else (if h < 1318526818 then 341 else 415)) else (if h < 1338966483 then (if h < 1338492217 then 97 else 64) else (if h < 1342641936 then 410 else 328))) else (if h < 1350157499 then (if h < 1347239269 then (if h < 1346910969 then 340 else 233) else (if h < 1347366594 then 176 else 44)) else (if h < 1353559236 then (if h < 1351669398 then 374 else 394) else (if h < 1356218308 then 463 else 151)))))) else (if h < 1483128697 then (if h < 1434015097 then (if h < 1382551931 then (if h < 1360900330 then (if h < 1357954858 then 109 else (if h < 1358222201 then 246 else 146)) else (if h < 1370963414 then (if h < 1363113592 then 458 else 321) else (if h < 1377878733 then 3 else 15))) else (if h < 1418025701 then (if h < 1405504863 then (if h < 1386284011 then 58 else 408) else (if h < 1412812243 then 86 else 433)) else (if h < 1425376607 then (if h < 1423611130 then 438 else 136) else (if h < 1426108114 then 45 else 38)))) else (if h < 1459191150 then (if h < 1447080769 then (if h < 1437862635 then 171 else (if h < 1440389745 then 200 else 252)) else (if h < 1448872459 then (if h < 1448138383 then 421 else 154) else (if h < 1459128217 then 436 else 125))) else (if h < 1475036236 then (if h < 1465064048 then (if h < 1463649773 then 350 else 300) else (if h < 1471856124 then 131 else 372)) else (if h < 1482216469 then (if h < 1479869736 then 53 else 258) else (if h < 1482661046 then 95 else 280))))) else (if h < 1548935844 then (if h < 1511768846 then (if h < 1496026301 then (if h < 1483546146 then 296 else (if h < 1492295789 then 119 else 367)) else (if h < 1503486805 then (if h < 1497883636 then 145 else 93) else (if h < 1504998704 then 331 else 351))) else (if h < 1522515213 then (if h < 1516442898 then (if h < 1513772739 then 275 else 270) else (if h < 1520047584 then 320 else 2)) else (if h < 1526513952 then (if h < 1523146236 then 25 else 274) else (if h < 1539613317 then 7 else 365)))) else (if h < 1577722327 then (if h < 1568088606 then (if h < 1550141343 then 49 else (if h < 1563629983 then 373 else 448)) else (if h < 1570071560 then (if h < 1568247610 then 302 else 407) else (if h < 1576294957 then 143 else 476))) else (if h < 1596734622 then (if h < 1590482236 then (if h < 1579437420 then 31 else 36) else (if h < 1594112958 then 174 else 157)) else (if h < 1600305959 then (if h < 1599639413 then 471 else 14) else (if h < 1601390860 then 378 else 170))))))) else (if h < 1858074098 then (if h < 1740896836 then (if h < 1653434174 then (if h < 1636458003 then (if h < 1611941235 then (if h < 1607925638 then 278 else (if h < 1609437537 then 425 else 449)) else (if h < 1620079330 then (if h < 1616073072 then 127 else 99) else (if h < 1620881731 then 186 else 417))) else (if h < 1641413301 then (if h < 1637767007 then (if h < 1636465564 then 294 else 54) else (if h < 1639096684 then 219 else 267)) else (if h < 1650036809 then (if h < 1644052150 then 444 else 467) else (if h < 1651576839 then 249 else 269)))) else (if h < 1683876253 then (if h < 1675844519 then (if h < 1656714392 then 217 else (if h < 1675598122 then 160 else 6)) else (if h < 1681148502 then (if h < 1679144609 then 23 else 244) else (if h < 1683299874 then 239 else 430))) else (if h < 1703470649 then (if h < 1693889715 then (if h < 1690521999 then 40 else 243) else (if h < 1697875964 then 5 else 73)) else (if h < 1721576916 then (if h < 1714708040 then 330 else 414) else (if h < 1733272865 then 364 else 35))))) else (if h < 1803387558 then (if h < 1763181564 then (if h < 1753635265 then (if h < 1744275893 then 298 else (if h < 1749663496 then 24 else 281)) else (if h < 1756577715 then (if h < 1755049817 then 335 else 423) else (if h < 1757857999 then 398 else 173))) else (if h < 1771623610 then (if h < 1768019128 then (if h < 1766773541 then 117 else 80) else (if h < 1771064684 then 184 else 247)) else (if h < 1787455093 then (if h < 1780283352 then 223 else 27) else (if h < 1797400060 then 185 else 163)))) else (if h < 1819990129 then (if h < 1807909482 then (if h < 1805142770 then 84 else (if h < 1806472447 then 218 else 236)) else (if h < 1814986339 then (if h < 1812264930 then 424 else 284) else (if h < 1818952602 then 102 else 238))) else (if h < 1838438873 then (if h < 1826015749 then (if h < 1820809937 then 166 else 216) else (if h < 1827781226 then 466 else 47)) else (if h < 1853411109 then (if h < 1842973885 then 142 else 4) else (if h < 1853426502 then 124 else 197)))))) else (if h < 1998047589 then (if h < 1918732102 then (if h < 1897254652 then (if h < 1864529877 then (if h < 1858337235 then 431 else (if h < 1861532836 then 43 else 451)) else (if h < 1868037346 then (if h < 1867468667 then 158 else 459) else (if h < 1871870971 then 371 else 155))) else (if h < 1909907021 then (if h < 1900648628 then (if h < 1897605199 then 71 else 22) else (if h < 1908168710 then 33 else 62)) else (if h < 1911410021 then (if h < 1911181499 then 355 else 114) else (if h < 1917039259 then 327 else 250)))) else (if h < 1959843100 then (if h < 1939054600 then (if h < 1923782884 then 266 else (if h < 1938999373 then 101 else 222)) else (if h < 1958051410 then (if h < 1957707883 then 66 else 110) else (if h < 1959622819 then 83 else 381))) else (if h < 1979640693 then (if h < 1975540667 then (if h < 1972476179 then 107 else 475) else (if h < 1975626830 then 290 else 313)) else (if h < 1983772673 then (if h < 1983075353 then 253 else 413) else (if h < 1986006877 then 104 else 52))))) else (if h < 2083691080 then (if h < 2050583958 then (if h < 2020080415 then (if h < 2002044032 then 395 else (if h < 2014345854 then 26 else 455)) else (if h < 2027421509 then (if h < 2020802265 then 282 else 196) else (if h < 2038870183 then 279 else 56))) else (if h < 2066461380 then (if h < 2055817979 then (if h < 2052805190 then 69 else 195) else (if h < 2064739327 then 387 else 326)) else (if h < 2075544473 then (if h < 2074600624 then 90 else 147) else (if h < 2079333422 then 60 else 225)))) else (if h < 2115393638 then (if h < 2102344363 then (if h < 2086107865 then 297 else (if h < 2087265598 then 235 else 169)) else (if h < 2112952125 then (if h < 2107705263 then 385 else 164) else (if h < 2113601948 then 338 else 207))) else (if h < 2128956136 then (if h < 2120408178 then (if h < 2118896279 then 231 else 89) else (if h < 2128409153 then 148 else 382)) else (if h < 2136404659 then (if h < 2131852372 then 312 else 75) else (if h < 2142916430 then 370 else 259)))))))))
private def states_9_2 (i : Nat) : List Sig :=
  (if i < 150 then (if i < 75 then (if i < 37 then (if i < 18 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then [s0,s1,s2,s3,s4,s5,s9,s91] else [s0,s1,s2,s4,s5,s9,s91]) else (if i < 3 then [s0,s1,s2,s4,s5,s6,s9,s91] else [s0,s1,s2,s3,s4,s5,s8,s91])) else (if i < 6 then (if i < 5 then [s0,s1,s3,s4,s5,s8,s91] else [s0,s1,s3,s4,s5,s6,s8,s91]) else (if i < 7 then [s0,s1,s2,s3,s4,s5,s7,s91] else (if i < 8 then [s1,s2,s3,s4,s5,s7,s91] else [s1,s2,s3,s4,s5,s6,s7,s91])))) else (if i < 13 then (if i < 11 then (if i < 10 then [s0,s1,s2,s3,s4,s5,s91] else [s0,s1,s2,s3,s4,s5,s6,s91]) else (if i < 12 then [s0,s1,s2,s3,s4,s6,s9,s90] else [s0,s1,s2,s4,s5,s6,s9,s90])) else (if i < 15 then (if i < 14 then [s0,s1,s2,s4,s6,s9,s90] else [s0,s1,s2,s3,s4,s6,s8,s90]) else (if i < 16 then [s0,s1,s3,s4,s5,s6,s8,s90] else (if i < 17 then [s0,s1,s3,s4,s6,s8,s90] else [s0,s1,s2,s3,s4,s6,s7,s90]))))) else (if i < 27 then (if i < 22 then (if i < 20 then (if i < 19 then [s1,s2,s3,s4,s5,s6,s7,s90] else [s1,s2,s3,s4,s6,s7,s90]) else (if i < 21 then [s0,s1,s2,s3,s4,s5,s6,s90] else [s0,s1,s2,s3,s4,s6,s90])) else (if i < 24 then (if i < 23 then [s0,s1,s2,s3,s5,s6,s9,s89] else [s0,s1,s2,s4,s5,s6,s9,s89]) else (if i < 25 then [s0,s1,s2,s5,s6,s9,s89] else (if i < 26 then [s0,s1,s2,s3,s5,s6,s8,s89] else [s0,s1,s3,s4,s5,s6,s8,s89])))) else (if i < 32 then (if i < 29 then (if i < 28 then [s0,s1,s3,s5,s6,s8,s89] else [s0,s1,s2,s3,s5,s6,s7,s89]) else (if i < 30 then [s1,s2,s3,s4,s5,s6,s7,s89] else (if i < 31 then [s1,s2,s3,s5,s6,s7,s89] else [s0,s1,s2,s3,s4,s5,s6,s89]))) else (if i < 34 then (if i < 33 then [s0,s1,s2,s3,s5,s6,s89] else [s0,s1,s2,s4,s5,s6,s9,s10]) else (if i < 35 then [s0,s1,s2,s3,s4,s5,s6,s10] else (if i < 36 then [s0,s1,s2,s4,s5,s6,s9,s12] else [s0,s1,s2,s3,s4,s5,s6,s12])))))) else (if i < 56 then (if i < 46 then (if i < 41 then (if i < 39 then (if i < 38 then [s0,s1,s2,s4,s5,s6,s9,s14] else [s0,s1,s2,s3,s4,s5,s6,s14]) else (if i < 40 then [s0,s1,s2,s4,s5,s6,s9,s16] else [s0,s1,s2,s3,s4,s5,s6,s16])) else (if i < 43 then (if i < 42 then [s0,s1,s2,s4,s5,s6,s9,s18] else [s0,s1,s2,s3,s4,s5,s6,s18]) else (if i < 44 then [s0,s1,s2,s4,s5,s6,s9,s20] else (if i < 45 then [s0,s1,s2,s3,s4,s5,s6,s20] else [s0,s1,s2,s4,s5,s6,s8,s9])))) else (if i < 51 then (if i < 48 then (if i < 47 then [s0,s1,s3,s4,s5,s6,s8,s9] else [s0,s1,s4,s5,s6,s8,s9]) else (if i < 49 then [s0,s1,s2,s4,s5,s6,s9,s88] else (if i < 50 then [s0,s2,s3,s4,s5,s6,s9,s88] else [s0,s2,s4,s5,s6,s9,s88]))) else (if i < 53 then (if i < 52 then [s0,s1,s2,s4,s5,s6,s7,s9] else [s1,s2,s3,s4,s5,s6,s7,s9]) else (if i < 54 then [s1,s2,s4,s5,s6,s7,s9] else (if i < 55 then [s0,s1,s2,s4,s5,s6,s9,s22] else [s0,s1,s2,s4,s5,s6,s9,s24]))))) else (if i < 65 then (if i < 60 then (if i < 58 then (if i < 57 then [s0,s1,s2,s4,s5,s6,s9,s26] else [s0,s1,s2,s4,s5,s6,s9,s28]) else (if i < 59 then [s0,s1,s2,s4,s5,s6,s9,s30] else [s0,s1,s2,s4,s5,s6,s9,s32])) else (if i < 62 then (if i < 61 then [s0,s1,s2,s4,s5,s6,s9,s11] else [s0,s1,s2,s4,s5,s6,s9,s34]) else (if i < 63 then [s0,s1,s2,s4,s5,s6,s9,s36] else (if i < 64 then [s0,s1,s2,s4,s5,s6,s9,s38] else [s0,s1,s2,s4,s5,s6,s9,s40])))) else (if i < 70 then (if i < 67 then (if i < 66 then [s0,s1,s2,s4,s5,s6,s9,s42] else [s0,s1,s2,s4,s5,s6,s9,s13]) else (if i < 68 then [s0,s1,s2,s4,s5,s6,s9,s23] else (if i < 69 then [s0,s1,s2,s4,s5,s6,s9,s44] else [s0,s1,s2,s4,s5,s6,s9,s46]))) else (if i < 72 then (if i < 71 then [s0,s1,s2,s4,s5,s6,s9,s48] else [s0,s1,s2,s4,s5,s6,s9,s50]) else (if i < 73 then [s0,s1,s2,s4,s5,s6,s9,s15] else (if i < 74 then [s0,s1,s2,s4,s5,s6,s9,s25] else [s0,s1,s2,s4,s5,s6,s9,s35]))))))) else (if i < 112 then (if i < 93 then (if i < 84 then (if i < 79 then (if i < 77 then (if i < 76 then [s0,s1,s2,s4,s5,s6,s9,s52] else [s0,s1,s2,s4,s5,s6,s9,s54]) else (if i < 78 then [s0,s1,s2,s4,s5,s6,s9,s56] else [s0,s1,s2,s3,s4,s5,s6,s9])) else (if i < 81 then (if i < 80 then [s0,s1,s2,s4,s5,s6,s9,s27] else [s0,s1,s2,s4,s5,s6,s9,s37]) else (if i < 82 then [s0,s1,s2,s4,s5,s6,s9,s45] else (if i < 83 then [s0,s1,s2,s4,s5,s6,s9,s58] else [s0,s1,s2,s4,s5,s6,s9,s60])))) else (if i < 88 then (if i < 86 then (if i < 85 then [s0,s1,s2,s4,s5,s6,s9,s17] else [s0,s1,s2,s4,s5,s6,s9,s29]) else (if i < 87 then [s0,s1,s2,s4,s5,s6,s9,s39] else [s0,s1,s2,s4,s5,s6,s9,s47])) else (if i < 90 then (if i < 89 then [s0,s1,s2,s4,s5,s6,s9,s53] else [s0,s1,s2,s4,s5,s6,s9,s62]) else (if i < 91 then [s0,s1,s2,s4,s5,s6,s9,s19] else (if i < 92 then [s0,s1,s2,s4,s5,s6,s9,s31] else [s0,s1,s2,s4,s5,s6,s9,s41]))))) else (if i < 102 then (if i < 97 then (if i < 95 then (if i < 94 then [s0,s1,s2,s4,s5,s6,s9,s49] else [s0,s1,s2,s4,s5,s6,s9,s55]) else (if i < 96 then [s0,s1,s2,s4,s5,s6,s9,s59] else [s0,s1,s2,s4,s5,s6,s9])) else (if i < 99 then (if i < 98 then [s0,s1,s2,s4,s5,s6,s9,s21] else [s0,s1,s2,s4,s5,s6,s9,s33]) else (if i < 100 then [s0,s1,s2,s4,s5,s6,s9,s43] else (if i < 101 then [s0,s1,s2,s4,s5,s6,s9,s51] else [s0,s1,s2,s4,s5,s6,s9,s57])))) else (if i < 107 then (if i < 104 then (if i < 103 then [s0,s1,s2,s4,s5,s6,s9,s61] else [s0,s1,s2,s4,s5,s6,s9,s63]) else (if i < 105 then [s0,s1,s3,s4,s5,s6,s8,s64] else (if i < 106 then [s0,s1,s2,s3,s4,s5,s6,s64] else [s0,s1,s3,s4,s5,s6,s8,s66]))) else (if i < 109 then (if i < 108 then [s0,s1,s2,s3,s4,s5,s6,s66] else [s0,s1,s3,s4,s5,s6,s8,s68]) else (if i < 110 then [s0,s1,s2,s3,s4,s5,s6,s68] else (if i < 111 then [s0,s1,s3,s4,s5,s6,s8,s70] else [s0,s1,s2,s3,s4,s5,s6,s70])))))) else (if i < 131 then (if i < 121 then (if i < 116 then (if i < 114 then (if i < 113 then [s0,s1,s3,s4,s5,s6,s8,s72] else [s0,s1,s2,s3,s4,s5,s6,s72]) else (if i < 115 then [s0,s1,s3,s4,s5,s6,s8,s74] else [s0,s1,s2,s3,s4,s5,s6,s74])) else (if i < 118 then (if i < 117 then [s0,s1,s3,s4,s5,s6,s8,s88] else [s0,s2,s3,s4,s5,s6,s8,s88]) else (if i < 119 then [s0,s3,s4,s5,s6,s8,s88] else (if i < 120 then [s0,s1,s3,s4,s5,s6,s7,s8] else [s1,s2,s3,s4,s5,s6,s7,s8])))) else (if i < 126 then (if i < 123 then (if i < 122 then [s1,s3,s4,s5,s6,s7,s8] else [s0,s1,s3,s4,s5,s6,s8,s22]) else (if i < 124 then [s0,s1,s3,s4,s5,s6,s8,s24] else (if i < 125 then [s0,s1,s3,s4,s5,s6,s8,s26] else [s0,s1,s3,s4,s5,s6,s8,s28]))) else (if i < 128 then (if i < 127 then [s0,s1,s3,s4,s5,s6,s8,s30] else [s0,s1,s3,s4,s5,s6,s8,s32]) else (if i < 129 then [s0,s1,s3,s4,s5,s6,s8,s65] else (if i < 130 then [s0,s1,s3,s4,s5,s6,s8,s34] else [s0,s1,s3,s4,s5,s6,s8,s36]))))) else (if i < 140 then (if i < 135 then (if i < 133 then (if i < 132 then [s0,s1,s3,s4,s5,s6,s8,s38] else [s0,s1,s3,s4,s5,s6,s8,s40]) else (if i < 134 then [s0,s1,s3,s4,s5,s6,s8,s42] else [s0,s1,s3,s4,s5,s6,s8,s67])) else (if i < 137 then (if i < 136 then [s0,s1,s3,s4,s5,s6,s8,s23] else [s0,s1,s3,s4,s5,s6,s8,s44]) else (if i < 138 then [s0,s1,s3,s4,s5,s6,s8,s46] else (if i < 139 then [s0,s1,s3,s4,s5,s6,s8,s48] else [s0,s1,s3,s4,s5,s6,s8,s50])))) else (if i < 145 then (if i < 142 then (if i < 141 then [s0,s1,s2,s3,s4,s5,s6,s8] else [s0,s1,s3,s4,s5,s6,s8,s25]) else (if i < 143 then [s0,s1,s3,s4,s5,s6,s8,s35] else (if i < 144 then [s0,s1,s3,s4,s5,s6,s8,s52] else [s0,s1,s3,s4,s5,s6,s8,s54]))) else (if i < 147 then (if i < 146 then [s0,s1,s3,s4,s5,s6,s8,s56] else [s0,s1,s3,s4,s5,s6,s8,s69]) else (if i < 148 then [s0,s1,s3,s4,s5,s6,s8,s27] else (if i < 149 then [s0,s1,s3,s4,s5,s6,s8,s37] else [s0,s1,s3,s4,s5,s6,s8,s45])))))))) else (if i < 225 then (if i < 187 then (if i < 168 then (if i < 159 then (if i < 154 then (if i < 152 then (if i < 151 then [s0,s1,s3,s4,s5,s6,s8,s58] else [s0,s1,s3,s4,s5,s6,s8,s60]) else (if i < 153 then [s0,s1,s3,s4,s5,s6,s8,s71] else [s0,s1,s3,s4,s5,s6,s8,s29])) else (if i < 156 then (if i < 155 then [s0,s1,s3,s4,s5,s6,s8,s39] else [s0,s1,s3,s4,s5,s6,s8,s47]) else (if i < 157 then [s0,s1,s3,s4,s5,s6,s8,s53] else (if i < 158 then [s0,s1,s3,s4,s5,s6,s8,s62] else [s0,s1,s3,s4,s5,s6,s8,s73])))) else (if i < 163 then (if i < 161 then (if i < 160 then [s0,s1,s3,s4,s5,s6,s8,s31] else [s0,s1,s3,s4,s5,s6,s8,s41]) else (if i < 162 then [s0,s1,s3,s4,s5,s6,s8,s49] else [s0,s1,s3,s4,s5,s6,s8,s55])) else (if i < 165 then (if i < 164 then [s0,s1,s3,s4,s5,s6,s8,s59] else [s0,s1,s3,s4,s5,s6,s8]) else (if i < 166 then [s0,s1,s3,s4,s5,s6,s8,s75] else (if i < 167 then [s0,s1,s3,s4,s5,s6,s8,s33] else [s0,s1,s3,s4,s5,s6,s8,s43]))))) else (if i < 177 then (if i < 172 then (if i < 170 then (if i < 169 then [s0,s1,s3,s4,s5,s6,s8,s51] else [s0,s1,s3,s4,s5,s6,s8,s57]) else (if i < 171 then [s0,s1,s3,s4,s5,s6,s8,s61] else [s0,s1,s3,s4,s5,s6,s8,s63])) else (if i < 174 then (if i < 173 then [s0,s2,s3,s4,s5,s6,s7,s88] else [s1,s2,s3,s4,s5,s6,s7,s88]) else (if i < 175 then [s2,s3,s4,s5,s6,s7,s88] else (if i < 176 then [s0,s1,s2,s3,s4,s5,s6,s88] else [s0,s2,s3,s4,s5,s6,s88])))) else (if i < 182 then (if i < 179 then (if i < 178 then [s1,s2,s3,s4,s5,s6,s7,s76] else [s0,s1,s2,s3,s4,s5,s6,s76]) else (if i < 180 then [s1,s2,s3,s4,s5,s6,s7,s78] else (if i < 181 then [s0,s1,s2,s3,s4,s5,s6,s78] else [s1,s2,s3,s4,s5,s6,s7,s80]))) else (if i < 184 then (if i < 183 then [s0,s1,s2,s3,s4,s5,s6,s80] else [s1,s2,s3,s4,s5,s6,s7,s82]) else (if i < 185 then [s0,s1,s2,s3,s4,s5,s6,s82] else (if i < 186 then [s1,s2,s3,s4,s5,s6,s7,s84] else [s0,s1,s2,s3,s4,s5,s6,s84])))))) else (if i < 206 then (if i < 196 then (if i < 191 then (if i < 189 then (if i < 188 then [s1,s2,s3,s4,s5,s6,s7,s86] else [s0,s1,s2,s3,s4,s5,s6,s86]) else (if i < 190 then [s1,s2,s3,s4,s5,s6,s7,s22] else [s1,s2,s3,s4,s5,s6,s7,s24])) else (if i < 193 then (if i < 192 then [s1,s2,s3,s4,s5,s6,s7,s26] else [s1,s2,s3,s4,s5,s6,s7,s28]) else (if i < 194 then [s1,s2,s3,s4,s5,s6,s7,s30] else (if i < 195 then [s1,s2,s3,s4,s5,s6,s7,s32] else [s0,s1,s2,s3,s4,s5,s6,s7])))) else (if i < 201 then (if i < 198 then (if i < 197 then [s1,s2,s3,s4,s5,s6,s7,s34] else [s1,s2,s3,s4,s5,s6,s7,s36]) else (if i < 199 then [s1,s2,s3,s4,s5,s6,s7,s38] else (if i < 200 then [s1,s2,s3,s4,s5,s6,s7,s40] else [s1,s2,s3,s4,s5,s6,s7,s42]))) else (if i < 203 then (if i < 202 then [s1,s2,s3,s4,s5,s6,s7,s77] else [s1,s2,s3,s4,s5,s6,s7,s23]) else (if i < 204 then [s1,s2,s3,s4,s5,s6,s7,s44] else (if i < 205 then [s1,s2,s3,s4,s5,s6,s7,s46] else [s1,s2,s3,s4,s5,s6,s7,s48]))))) else (if i < 215 then (if i < 210 then (if i < 208 then (if i < 207 then [s1,s2,s3,s4,s5,s6,s7,s50] else [s1,s2,s3,s4,s5,s6,s7,s79]) else (if i < 209 then [s1,s2,s3,s4,s5,s6,s7,s25] else [s1,s2,s3,s4,s5,s6,s7,s35])) else (if i < 212 then (if i < 211 then [s1,s2,s3,s4,s5,s6,s7,s52] else [s1,s2,s3,s4,s5,s6,s7,s54]) else (if i < 213 then [s1,s2,s3,s4,s5,s6,s7,s56] else (if i < 214 then [s1,s2,s3,s4,s5,s6,s7,s81] else [s1,s2,s3,s4,s5,s6,s7,s27])))) else (if i < 220 then (if i < 217 then (if i < 216 then [s1,s2,s3,s4,s5,s6,s7,s37] else [s1,s2,s3,s4,s5,s6,s7,s45]) else (if i < 218 then [s1,s2,s3,s4,s5,s6,s7,s58] else (if i < 219 then [s1,s2,s3,s4,s5,s6,s7,s60] else [s1,s2,s3,s4,s5,s6,s7,s83]))) else (if i < 222 then (if i < 221 then [s1,s2,s3,s4,s5,s6,s7,s29] else [s1,s2,s3,s4,s5,s6,s7,s39]) else (if i < 223 then [s1,s2,s3,s4,s5,s6,s7,s47] else (if i < 224 then [s1,s2,s3,s4,s5,s6,s7,s53] else [s1,s2,s3,s4,s5,s6,s7,s62]))))))) else (if i < 262 then (if i < 243 then (if i < 234 then (if i < 229 then (if i < 227 then (if i < 226 then [s1,s2,s3,s4,s5,s6,s7,s85] else [s1,s2,s3,s4,s5,s6,s7,s31]) else (if i < 228 then [s1,s2,s3,s4,s5,s6,s7,s41] else [s1,s2,s3,s4,s5,s6,s7,s49])) else (if i < 231 then (if i < 230 then [s1,s2,s3,s4,s5,s6,s7,s55] else [s1,s2,s3,s4,s5,s6,s7,s59]) else (if i < 232 then [s1,s2,s3,s4,s5,s6,s7] else (if i < 233 then [s1,s2,s3,s4,s5,s6,s7,s87] else [s1,s2,s3,s4,s5,s6,s7,s33])))) else (if i < 238 then (if i < 236 then (if i < 235 then [s1,s2,s3,s4,s5,s6,s7,s43] else [s1,s2,s3,s4,s5,s6,s7,s51]) else (if i < 237 then [s1,s2,s3,s4,s5,s6,s7,s57] else [s1,s2,s3,s4,s5,s6,s7,s61])) else (if i < 240 then (if i < 239 then [s1,s2,s3,s4,s5,s6,s7,s63] else [s0,s1,s2,s3,s4,s5,s6,s22]) else (if i < 241 then [s0,s1,s2,s3,s4,s5,s6,s24] else (if i < 242 then [s0,s1,s2,s3,s4,s5,s6,s26] else [s0,s1,s2,s3,s4,s5,s6,s28]))))) else (if i < 252 then (if i < 247 then (if i < 245 then (if i < 244 then [s0,s1,s2,s3,s4,s5,s6,s30] else [s0,s1,s2,s3,s4,s5,s6,s32]) else (if i < 246 then [s0,s1,s2,s3,s4,s5,s6,s11] else [s0,s1,s2,s3,s4,s5,s6,s65])) else (if i < 249 then (if i < 248 then [s0,s1,s2,s3,s4,s5,s6,s34] else [s0,s1,s2,s3,s4,s5,s6,s36]) else (if i < 250 then [s0,s1,s2,s3,s4,s5,s6,s38] else (if i < 251 then [s0,s1,s2,s3,s4,s5,s6,s40] else [s0,s1,s2,s3,s4,s5,s6,s42])))) else (if i < 257 then (if i < 254 then (if i < 253 then [s0,s1,s2,s3,s4,s5,s6,s13] else [s0,s1,s2,s3,s4,s5,s6,s67]) else (if i < 255 then [s0,s1,s2,s3,s4,s5,s6,s77] else (if i < 256 then [s0,s1,s2,s3,s4,s5,s6,s23] else [s0,s1,s2,s3,s4,s5,s6,s44]))) else (if i < 259 then (if i < 258 then [s0,s1,s2,s3,s4,s5,s6,s46] else [s0,s1,s2,s3,s4,s5,s6,s48]) else (if i < 260 then [s0,s1,s2,s3,s4,s5,s6,s50] else (if i < 261 then [s0,s1,s2,s3,s4,s5,s6,s15] else [s0,s1,s2,s3,s4,s5,s6,s79])))))) else (if i < 281 then (if i < 271 then (if i < 266 then (if i < 264 then (if i < 263 then [s0,s1,s2,s3,s4,s5,s6,s25] else [s0,s1,s2,s3,s4,s5,s6,s35]) else (if i < 265 then [s0,s1,s2,s3,s4,s5,s6,s52] else [s0,s1,s2,s3,s4,s5,s6,s54])) else (if i < 268 then (if i < 267 then [s0,s1,s2,s3,s4,s5,s6,s56] else [s0,s1,s2,s3,s4,s5,s6,s69]) else (if i < 269 then [s0,s1,s2,s3,s4,s5,s6,s81] else (if i < 270 then [s0,s1,s2,s3,s4,s5,s6,s27] else [s0,s1,s2,s3,s4,s5,s6,s37])))) else (if i < 276 then (if i < 273 then (if i < 272 then [s0,s1,s2,s3,s4,s5,s6,s45] else [s0,s1,s2,s3,s4,s5,s6,s58]) else (if i < 274 then [s0,s1,s2,s3,s4,s5,s6,s60] else (if i < 275 then [s0,s1,s2,s3,s4,s5,s6,s17] else [s0,s1,s2,s3,s4,s5,s6,s71]))) else (if i < 278 then (if i < 277 then [s0,s1,s2,s3,s4,s5,s6,s83] else [s0,s1,s2,s3,s4,s5,s6,s29]) else (if i < 279 then [s0,s1,s2,s3,s4,s5,s6,s39] else (if i < 280 then [s0,s1,s2,s3,s4,s5,s6,s47] else [s0,s1,s2,s3,s4,s5,s6,s53]))))) else (if i < 290 then (if i < 285 then (if i < 283 then (if i < 282 then [s0,s1,s2,s3,s4,s5,s6,s62] else [s0,s1,s2,s3,s4,s5,s6,s19]) else (if i < 284 then [s0,s1,s2,s3,s4,s5,s6,s73] else [s0,s1,s2,s3,s4,s5,s6,s85])) else (if i < 287 then (if i < 286 then [s0,s1,s2,s3,s4,s5,s6,s31] else [s0,s1,s2,s3,s4,s5,s6,s41]) else (if i < 288 then [s0,s1,s2,s3,s4,s5,s6,s49] else (if i < 289 then [s0,s1,s2,s3,s4,s5,s6,s55] else [s0,s1,s2,s3,s4,s5,s6,s59])))) else (if i < 295 then (if i < 292 then (if i < 291 then [s0,s1,s2,s3,s4,s5,s6] else [s0,s1,s2,s3,s4,s5,s6,s21]) else (if i < 293 then [s0,s1,s2,s3,s4,s5,s6,s75] else (if i < 294 then [s0,s1,s2,s3,s4,s5,s6,s87] else [s0,s1,s2,s3,s4,s5,s6,s33]))) else (if i < 297 then (if i < 296 then [s0,s1,s2,s3,s4,s5,s6,s43] else [s0,s1,s2,s3,s4,s5,s6,s51]) else (if i < 298 then [s0,s1,s2,s3,s4,s5,s6,s57] else (if i < 299 then [s0,s1,s2,s3,s4,s5,s6,s61] else [s0,s1,s2,s3,s4,s5,s6,s63])))))))))
private def slots_9_2 (h : Nat) : Nat :=
  (if h < 1144132050 then (if h < 606492803 then (if h < 257326298 then (if h < 126963170 then (if h < 82667515 then (if h < 58308530 then (if h < 25687341 then (if h < 21694513 then 96 else 243) else (if h < 47363247 then 181 else 23)) else (if h < 63614213 then (if h < 58650849 then 245 else 119) else (if h < 69907311 then 198 else (if h < 72697306 then 257 else 120)))) else (if h < 95332489 then (if h < 89536739 then (if h < 85911322 then 149 else 186) else (if h < 93359845 then 172 else 297)) else (if h < 108332081 then (if h < 104383830 then 171 else 48) else (if h < 115772154 then 273 else (if h < 125254646 then 166 else 219))))) else (if h < 191268220 then (if h < 160450833 then (if h < 139919263 then (if h < 128475069 then 130 else 150) else (if h < 143770346 then 123 else 13)) else (if h < 166102471 then (if h < 163089682 then 146 else 164) else (if h < 171396476 then 264 else (if h < 189502743 then 61 else 95)))) else (if h < 219842732 then (if h < 202337406 then (if h < 193975572 then 35 else 176) else (if h < 202913785 then 134 else (if h < 212628855 then 26 else 262))) else (if h < 230955661 then (if h < 225019830 then 192 else 84) else (if h < 238693645 then 90 else (if h < 255245888 then 258 else 209)))))) else (if h < 402357177 then (if h < 330465445 then (if h < 283455480 then (if h < 266289777 then (if h < 259934368 then 232 else 116) else (if h < 274087349 then 222 else 128)) else (if h < 299320884 then (if h < 287056660 then 182 else 112) else (if h < 321382352 then 16 else (if h < 326947014 then 249 else 129)))) else (if h < 355353162 then (if h < 345053281 then (if h < 335963173 then 140 else 102) else (if h < 346197554 then 163 else (if h < 348724664 then 191 else 228))) else (if h < 377832848 then (if h < 365531026 then 111 else 12) else (if h < 383022785 then 86 else (if h < 388204655 then 276 else 234))))) else (if h < 524057916 then (if h < 491513711 then (if h < 466696647 then (if h < 453065257 then 41 else 292) else (if h < 477610871 then 14 else 242)) else (if h < 513342327 then (if h < 513014027 then 170 else 263) else (if h < 515094437 then 109 else (if h < 521081564 then 293 else 15)))) else (if h < 587479528 then (if h < 533383386 then (if h < 532665154 then 279 else 58) else (if h < 569279171 then 154 else (if h < 580877952 then 60 else 69))) else (if h < 602224634 then (if h < 589483421 then 220 else 215) else (if h < 603965693 then 8 else (if h < 604330486 then 241 else 101))))))) else (if h < 871581290 then (if h < 751308804 then (if h < 704946213 then (if h < 664347067 then (if h < 619302722 then (if h < 606672324 then 287 else 0) else (if h < 645972794 then 83 else 295)) else (if h < 677073112 then (if h < 674060323 then 22 else 47) else (if h < 679399603 then 75 else (if h < 688215692 then 223 else 126)))) else (if h < 724149288 then (if h < 714807366 then (if h < 713477689 then 50 else 200) else (if h < 723599496 then 212 else 73)) else (if h < 729144856 then (if h < 727287521 then 179 else 214) else (if h < 736428490 then 199 else (if h < 749664286 then 137 else 70))))) else (if h < 832352993 then (if h < 774853260 then (if h < 767148532 then (if h < 759881024 then 7 else 169) else (if h < 767493918 then 183 else 105)) else (if h < 809863973 then (if h < 808983547 then 151 else 30) else (if h < 816139867 then 252 else (if h < 825374178 then 283 else 226)))) else (if h < 847251560 then (if h < 841436086 then (if h < 832623650 then 63 else 143) else (if h < 845247667 then 45 else (if h < 846857912 then 277 else 260))) else (if h < 856625057 then (if h < 847334292 then 270 else 202) else (if h < 859992773 then 275 else (if h < 860496751 then 10 else 118)))))) else (if h < 988581512 then (if h < 937167742 then (if h < 904638110 then (if h < 887975612 then (if h < 879150034 then 44 else 141) else (if h < 904572899 then 229 else 225)) else (if h < 923961057 then (if h < 905214824 then 6 else 138) else (if h < 929137184 then 107 else (if h < 933026647 then 189 else 187)))) else (if h < 981917427 then (if h < 962312853 then (if h < 953558151 then 280 else 115) else (if h < 971245828 then 28 else (if h < 972575505 then 251 else 266))) else (if h < 985055660 then (if h < 983879392 then 180 else 52) else (if h < 986912995 then 269 else (if h < 987903531 then 250 else 131))))) else (if h < 1047747405 then (if h < 1023984668 then (if h < 1009076943 then (if h < 994442784 then 57 else 211) else (if h < 1021874341 then 9 else 110)) else (if h < 1027872514 then (if h < 1024916671 then 74 else 184) else (if h < 1035028557 then 117 else (if h < 1037965203 then 87 else 38)))) else (if h < 1103132191 then (if h < 1066751686 then (if h < 1051251349 then 213 else 235) else (if h < 1083142317 then 32 else (if h < 1095791097 then 285 else 227))) else (if h < 1114936334 then (if h < 1105102431 then 224 else 255) else (if h < 1117463444 then 56 else (if h < 1119586436 then 93 else 165)))))))) else (if h < 1620079330 then (if h < 1382551931 then (if h < 1305515544 then (if h < 1189312630 then (if h < 1160257562 then (if h < 1155044104 then (if h < 1145743751 then 125 else 288) else (if h < 1156943435 then 203 else 99)) else (if h < 1179535206 then (if h < 1162341038 then 207 else 284) else (if h < 1179863506 then 142 else (if h < 1186905323 then 108 else 239)))) else (if h < 1241647531 then (if h < 1190794786 then (if h < 1190579095 then 194 else 155) else (if h < 1191104320 then 188 else 206)) else (if h < 1270486872 then (if h < 1252210923 then 78 else 265) else (if h < 1273013982 then 124 else (if h < 1286429419 then 161 else 291))))) else (if h < 1350157499 then (if h < 1312493973 then (if h < 1309019488 then (if h < 1305861844 then 268 else 216) else (if h < 1310320467 then 296 else 177)) else (if h < 1320834614 then (if h < 1318526818 then 167 else 238) else (if h < 1338966483 then 66 else (if h < 1347366594 then 233 else 34)))) else (if h < 1358222201 then (if h < 1353559236 then (if h < 1351669398 then 197 else 217) else (if h < 1356218308 then 286 else (if h < 1357828553 then 85 else 72))) else (if h < 1363113592 then (if h < 1360900330 then 80 else 281) else (if h < 1370963414 then 190 else (if h < 1377878733 then 2 else 11)))))) else (if h < 1522515213 then (if h < 1475036236 then (if h < 1426108114 then (if h < 1412812243 then (if h < 1386284011 then 43 else 231) else (if h < 1418025701 then 256 else 261)) else (if h < 1447080769 then (if h < 1434015097 then 29 else 104) else (if h < 1448138383 then 244 else (if h < 1448872459 then 88 else 259)))) else (if h < 1496026301 then (if h < 1482661046 then (if h < 1482216469 then 40 else 65) else (if h < 1483128697 then 158 else (if h < 1483546146 then 173 else 77))) else (if h < 1511768846 then (if h < 1497883636 then 79 else 64) else (if h < 1513772739 then 153 else (if h < 1520047584 then 148 else 1))))) else (if h < 1576294957 then (if h < 1548935844 then (if h < 1526513952 then (if h < 1523146236 then 19 else 152) else (if h < 1539613317 then 5 else 195)) else (if h < 1563629983 then (if h < 1550141343 then 37 else 196) else (if h < 1568088606 then 271 else (if h < 1568247610 then 178 else 230)))) else (if h < 1600305959 then (if h < 1590482236 then (if h < 1577722327 then 299 else 24) else (if h < 1594112958 then 106 else (if h < 1596734622 then 91 else 294))) else (if h < 1607925638 then (if h < 1603688921 then 201 else 156) else (if h < 1609437537 then 248 else (if h < 1616073072 then 272 else 67))))))) else (if h < 1867468667 then (if h < 1749663496 then (if h < 1675598122 then (if h < 1641413301 then (if h < 1637767007 then (if h < 1620881731 then 114 else 240) else (if h < 1639096684 then 133 else 145)) else (if h < 1651576839 then (if h < 1644052150 then 267 else 290) else (if h < 1653434174 then 147 else (if h < 1656714392 then 132 else 94)))) else (if h < 1697875964 then (if h < 1683299874 then (if h < 1675844519 then 4 else 17) else (if h < 1683876253 then 253 else 31)) else (if h < 1733272865 then (if h < 1714708040 then 54 else 237) else (if h < 1740896836 then 27 else (if h < 1744275893 then 175 else 18))))) else (if h < 1812264930 then (if h < 1768019128 then (if h < 1756577715 then (if h < 1755049817 then 159 else 246) else (if h < 1763181564 then 221 else 76)) else (if h < 1780283352 then (if h < 1771623610 then 113 else 135) else (if h < 1797400060 then 21 else (if h < 1807909482 then 97 else 247)))) else (if h < 1853426502 then (if h < 1826015749 then (if h < 1819990129 then 162 else 100) else (if h < 1827781226 then 289 else (if h < 1842973885 then 36 else 3))) else (if h < 1858337235 then (if h < 1858074098 then 122 else 254) else (if h < 1861532836 then 33 else (if h < 1864529877 then 274 else 92)))))) else (if h < 2014345854 then (if h < 1958051410 then (if h < 1908168710 then (if h < 1897254652 then (if h < 1871870971 then 282 else 89) else (if h < 1900648628 then 53 else 25)) else (if h < 1918732102 then (if h < 1911410021 then 46 else 193) else (if h < 1923782884 then 144 else (if h < 1939054600 then 68 else 49)))) else (if h < 1975626830 then (if h < 1959843100 then (if h < 1959622819 then 59 else 204) else (if h < 1972476179 then 71 else (if h < 1975540667 then 298 else 168))) else (if h < 1986006877 then (if h < 1983075353 then 185 else 236) else (if h < 1998047589 then 39 else (if h < 2002044032 then 218 else 20))))) else (if h < 2083691080 then (if h < 2050583958 then (if h < 2027421509 then (if h < 2020080415 then 278 else 160) else (if h < 2038870183 then 157 else 42)) else (if h < 2055817979 then (if h < 2052805190 then 51 else 121) else (if h < 2074600624 then 210 else (if h < 2079333422 then 81 else 136)))) else (if h < 2115393638 then (if h < 2102344363 then (if h < 2087265598 then 174 else 103) else (if h < 2107705263 then 208 else (if h < 2113601948 then 98 else 127))) else (if h < 2120408178 then (if h < 2118896279 then 139 else 62) else (if h < 2128409153 then 82 else (if h < 2131852372 then 205 else 55)))))))))
private def states_9_3 (i : Nat) : List Sig :=
  (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then [s0,s1,s2,s4,s5,s9,s91] else [s0,s1,s3,s4,s5,s8,s91]) else (if i < 3 then [s1,s2,s3,s4,s5,s7,s91] else (if i < 4 then [s0,s1,s2,s3,s4,s5,s91] else [s0,s1,s2,s4,s6,s9,s90]))) else (if i < 8 then (if i < 6 then [s0,s1,s3,s4,s6,s8,s90] else (if i < 7 then [s1,s2,s3,s4,s6,s7,s90] else [s0,s1,s2,s3,s4,s6,s90])) else (if i < 9 then [s0,s1,s2,s5,s6,s9,s89] else (if i < 10 then [s0,s1,s3,s5,s6,s8,s89] else [s1,s2,s3,s5,s6,s7,s89])))) else (if i < 17 then (if i < 14 then (if i < 12 then [s0,s1,s2,s3,s5,s6,s89] else (if i < 13 then [s0,s1,s4,s5,s6,s8,s9] else [s0,s2,s4,s5,s6,s9,s88])) else (if i < 15 then [s1,s2,s4,s5,s6,s7,s9] else (if i < 16 then [s0,s1,s2,s4,s5,s6,s9] else [s0,s3,s4,s5,s6,s8,s88]))) else (if i < 20 then (if i < 18 then [s1,s3,s4,s5,s6,s7,s8] else (if i < 19 then [s0,s1,s3,s4,s5,s6,s8] else [s2,s3,s4,s5,s6,s7,s88])) else (if i < 21 then [s0,s2,s3,s4,s5,s6,s88] else (if i < 22 then [s1,s2,s3,s4,s5,s6,s7] else [s0,s1,s2,s3,s4,s5,s6])))))
private def slots_9_3 (h : Nat) : Nat :=
  (if h < 1066751686 then (if h < 674060323 then (if h < 163089682 then (if h < 143770346 then 15 else 4) else (if h < 193975572 then 18 else (if h < 299320884 then 20 else 5))) else (if h < 808983547 then (if h < 704946213 then 12 else (if h < 751308804 then 13 else 2)) else (if h < 860496751 then 10 else (if h < 1009076943 then 16 else 3)))) else (if h < 1675598122 then (if h < 1522515213 then (if h < 1386284011 then 11 else (if h < 1520047584 then 21 else 0)) else (if h < 1577722327 then 6 else (if h < 1644052150 then 8 else 22))) else (if h < 1897254652 then (if h < 1733272865 then 1 else (if h < 1780283352 then 9 else 7)) else (if h < 2052805190 then 14 else (if h < 2083691080 then 17 else 19)))))
private def states_9_4 (i : Nat) : List Sig :=
  []
private def slots_9_4 (h : Nat) : Nat :=
  0
def L9 : Layer where
  count t := if t < 5 then (if t < 2 then (if t < 1 then 263 else 477) else (if t < 3 then 300 else (if t < 4 then 23 else 0))) else 0
  state t i := (if t < 2 then (if t < 1 then states_9_0 i else states_9_1 i) else (if t < 3 then states_9_2 i else (if t < 4 then states_9_3 i else states_9_4 i)))
  pick t v := let h := stateHash v; (if t < 2 then (if t < 1 then slots_9_0 h else slots_9_1 h) else (if t < 3 then slots_9_2 h else (if t < 4 then slots_9_3 h else slots_9_4 h)))
private def valid_10 (t i : Nat) := layerNode L9 9 t (L10.state t i)
private theorem sub_10_0_0 : span (valid_10 0) 4 0 = true := by decide +kernel
private theorem done_10_0 (i : Nat) (hi : i < 4) : valid_10 0 i = true := by
  exact span_ok sub_10_0_0 i (by omega) (by omega)
private theorem sub_10_1_0 : span (valid_10 1) 7 0 = true := by decide +kernel
private theorem done_10_1 (i : Nat) (hi : i < 7) : valid_10 1 i = true := by
  exact span_ok sub_10_1_0 i (by omega) (by omega)
private theorem sub_10_2_0 : span (valid_10 2) 7 0 = true := by decide +kernel
private theorem done_10_2 (i : Nat) (hi : i < 7) : valid_10 2 i = true := by
  exact span_ok sub_10_2_0 i (by omega) (by omega)
private theorem sub_10_3_0 : span (valid_10 3) 7 0 = true := by decide +kernel
private theorem done_10_3 (i : Nat) (hi : i < 7) : valid_10 3 i = true := by
  exact span_ok sub_10_3_0 i (by omega) (by omega)
private theorem sub_10_4_0 : span (valid_10 4) 4 0 = true := by decide +kernel
private theorem done_10_4 (i : Nat) (hi : i < 4) : valid_10 4 i = true := by
  exact span_ok sub_10_4_0 i (by omega) (by omega)
theorem checkedTop (validLayer_9 : L9.Valid 9) : L10.Valid 10 := by
  intro t i hi
  have ht : t < 5 := by
    by_contra hx
    simp [L10,hx] at hi
  have hc : valid_10 t i = true := by
    interval_cases t
    · exact done_10_0 i hi
    · exact done_10_1 i hi
    · exact done_10_2 i hi
    · exact done_10_3 i hi
    · exact done_10_4 i hi
  exact layerNode_sound validLayer_9 hc

theorem rootMatch0 : rootTable 0 L10 = true := by decide +kernel
theorem rootMatch2 : rootTable 2 L10 = true := by decide +kernel
theorem rootMatch3 : rootTable 3 L10 = true := by decide +kernel
end ThetaCut
end CoThetaLayerSanity
