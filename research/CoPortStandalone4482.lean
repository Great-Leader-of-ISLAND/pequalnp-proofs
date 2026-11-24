import Mathlib
import PEqualNP.Defs

/- The backward live-frontier extraction and gate enumeration follow our checked
   seven-coordinate CoThetaFast file, based on the accepted L-meta-1007.
   This specialization has no paid inverters and checks 8-input extremal rows. -/
namespace CoPortEngine4482
abbrev B := BitVec 160
abbrev Sig := B × B
def top : B := BitVec.allOnes 160
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
lemma target_proper : proper target := by unfold proper target zero one top; decide +kernel
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
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
  by_cases hi : i < 160
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 160 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 160
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 160 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 160)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 160) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 160 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 160)] <;> simp [hi]
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

lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
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

lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
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
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
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
  exact Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  cases l with
  | nil =>
    rcases ho with rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.

private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ Live k' t S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
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
        exact ⟨_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live k 0 S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,T,by simp; omega,hu,hT⟩

def bit (side : Bool) (i : Fin 160) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 160).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

lemma b_read (s i) (w : List Sig) (j : Nat) :
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

lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
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

lemma unrestricted {k t : Nat} {S : Finset Sig} (h : Live k t S) : Restricted k t S := by
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

lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
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
end CoPortEngine4482

-- The circuit monotonicity lemmas are from the checked L-meta-1572 (using L-meta-1353).
namespace CoSwitch3302.MonotoneWires3302
open PEqualNP.CircuitLowerBounds
-- The wire evaluation lemmas follow L-meta-1353.

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

abbrev AO (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma wires_mono {n : ℕ} (C : Circuit) (hAO : AO C) (x y : Fin n → Bool)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let p : Fin n := ⟨w, hw⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases h : w < n + C.size
    · let k := w - n
      have hk : k < C.gates.length := by dsimp [k]; unfold Circuit.size at h; omega
      have hwk : w = n + k := by dsimp [k]; omega
      rw [hwk]
      refine gate_mono C k hk (hAO _ (List.getElem_mem hk)).1 x y ?_
      intro r _ hr
      exact ih r (by omega)
    · rw [missing_value C x w (by omega)]
      simp


end CoSwitch3302.MonotoneWires3302


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

namespace CoPortRows4482
open CoPortEngine4482 CoPortSlice4482

def maskGraph (vals : Fin 9 → B) : B :=
  (([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).map (fun n =>
    vals (Fin.ofNat 9 (n/10)) &&& vals (Fin.ofNat 9 (n%10)))).foldr (· ||| ·) 0

private theorem fold_bit (ys : List B) (i : ℕ) :
    (ys.foldr (· ||| ·) 0).getLsbD i = ys.any (fun w => w.getLsbD i) := by
  induction ys with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons,List.any_cons,BitVec.getLsbD_or]
    exact congrArg (fun b => a.getLsbD i || b) ih

theorem graph_bit (v : Fin 9 → B) (i : ℕ) :
    (maskGraph v).getLsbD i = graph (fun j => (v j).getLsbD i) := by
  rw [maskGraph,fold_bit]
  simp [graph,List.any_map,BitVec.getLsbD_and,Function.comp_def]

def lowBits (b : Nat) (xs : Fin 9 → Sig) (j : Fin 9) : B :=
  if b.testBit j.val then (xs j).1 else 0

def highBits (b : Nat) (xs : Fin 9 → Sig) (j : Fin 9) : B :=
  if b.testBit j.val then (xs j).2 else top

def rowCheck (b : Nat) (xs : Fin 9 → Sig) : Bool :=
  maskGraph (lowBits b xs) == 0 && maskGraph (fun j => (xs j).1) == top &&
    maskGraph (fun j => (xs j).2) == 0 && maskGraph (highBits b xs) == top

theorem rows {b : Nat} {xs : Fin 9 → Sig} (ok : rowCheck b xs = true) (i : Fin 160) :
    (graph (low b (row xs true i)) = false ∧ graph (row xs true i) = true) ∧
    (graph (row xs false i) = false ∧ graph (high b (row xs false i)) = true) := by
  simp only [rowCheck,Bool.and_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨⟨l,p⟩,n⟩,h⟩ := ok
  have low_eq : low b (row xs true i) = fun j => (lowBits b xs j).getLsbD i.val := by
    funext j
    cases e : b.testBit j.val <;> simp [low,lowBits,row,bit,e]
  have high_eq : high b (row xs false i) = fun j => (highBits b xs j).getLsbD i.val := by
    funext j
    cases e : b.testBit j.val
    · change _ = (if b.testBit j.val then (xs j).2 else top).getLsbD i.val
      have ht : top.getLsbD i.val=true := by
        change (BitVec.allOnes 160).getLsbD i.val=true
        simp only [BitVec.getLsbD_allOnes,i.isLt,decide_true]
      simp [high,e,ht]
    · simp [high,highBits,row,bit,e]
  rw [low_eq,high_eq]
  have bit_hi (v : Fin 9 → B) (yes : maskGraph v = top) :
      graph (fun j => (v j).getLsbD i.val) = true := by
    rw [←graph_bit,yes]
    simp only [top,BitVec.getLsbD_allOnes,i.isLt,decide_true]
  have bit_lo (v : Fin 9 → B) (no : maskGraph v = 0) :
      graph (fun j => (v j).getLsbD i.val) = false := by
    rw [←graph_bit,no]
    simp
  exact ⟨⟨bit_lo _ l,bit_hi _ p⟩,bit_lo _ n,bit_hi _ h⟩

end CoPortRows4482

namespace CoPortBanks4482
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open CoPortEngine4482 CoPortSlice4482 CoPortRows4482

def pop (u : Nat) := ((List.range 9).filter fun j => u.testBit j).length
abbrev Entry := Nat × (Fin 9 → Sig)
def table : Array Entry := #[
  (31,![(0xfff000000000000000000fff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000fff000,0x3823823823823823823823823823823823823823),(0xfff000000000000000000fff000000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000fff000000000000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000fff000fff000fff000000fff,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000fff000fff000000000000fff000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000ffffff000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffff000000000000fffffffff000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (47,![(0xfff000000000000000000000fff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff000000,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000000000,0x4314314314314314314314314314314314314314),(0xf000000000fff000000000fff000000000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000fff000000000000fff000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000ffffff000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (55,![(0x0,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff000000,0x3823823823823823823823823823823823823823),(0xfff000000fff000000000000fff000000fff,0x4314314314314314314314314314314314314314),(0xf000000000ffffff000000fff000000000ffffff,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000fff000000000000fff000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000ffffff000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (59,![(0x0,0x4544544544544544544544544544544544544544),(0xfff000fff000000000000000fff000fff,0x3823823823823823823823823823823823823823),(0xfff000ffffff000000000000fff000ffffff,0x4314314314314314314314314314314314314314),(0xf000000000fff000000000fff000000000fff000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000fff000000000000fff000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000ffffff000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (61,![(0xfff000000000000000000000fff,0x4544544544544544544544544544544544544544),(0xfffffffff000000000000000fffffffff,0x3823823823823823823823823823823823823823),(0xfff000fff000000000000000fff000fff000,0x4314314314314314314314314314314314314314),(0xf000000000000000000000fff000000000000000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000fff000000000000fff000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000ffffff000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (62,![(0xfffffffff000000000000000000fffffffff,0x4544544544544544544544544544544544544544),(0xfff000000fff000000000000000fff000000fff,0x3823823823823823823823823823823823823823),(0xf000000000000000000000000fff000000000000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000000fff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000fff000fff000000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (79,![(0xfff000fff000000000000000fff000fff,0x4544544544544544544544544544544544544544),(0x0,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000000000,0x4314314314314314314314314314314314314314),(0xf000000000fff000000000fff000000000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000fff000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000ffffff000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (87,![(0xfff000000000000000000000fff000000,0x4544544544544544544544544544544544544544),(0x0,0x3823823823823823823823823823823823823823),(0xfff000000fff000000000000fff000000fff,0x4314314314314314314314314314314314314314),(0xf000000000ffffff000000fff000000000ffffff,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000fff000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000ffffff000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (91,![(0xfff000000000000000000000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000ffffff000000000000fff000ffffff,0x4314314314314314314314314314314314314314),(0xf000000000fff000000000fff000000000fff000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000fff000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000ffffff000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (93,![(0xfff000fff000000000000000000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000ffffff000000000000000fff000ffffff,0x3823823823823823823823823823823823823823),(0xf000000fff000000000000000fff000000fff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000fff000fff000000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (94,![(0xfffffffff000000000000000fffffffff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000000000,0x4314314314314314314314314314314314314314),(0xf000000000000000000000fff000000000000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000fff000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000ffffff000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (103,![(0xfff000000000000000000000fff000,0x4544544544544544544544544544544544544544),(0x0,0x3823823823823823823823823823823823823823),(0xfff000000fff000000000000fff000000fff,0x4314314314314314314314314314314314314314),(0xf000000fff000fff000000fff000000fff000fff,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000ffffff000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (107,![(0xfff000000000000000000000000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xf000000ffffff000000000000fff000000ffffff,0x4314314314314314314314314314314314314314),(0xfff000fff000000000fff000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (109,![(0x7ff001ffc0000000000000000001ffc007ff,0x12a2544a89512a2544a89512a2544a89512a2544),(0xfc00000fffffc00000000000007ff000003fffff,0x8c1182304608c1182304608c1182304608c11823),(0xffe00000000000003ff800000003ff800,0x518a314628c518a314628c518a314628c518a314),(0x3ff80000000000000ffe00000000ffe00000000,0xa4348690d21a4348690d21a4348690d21a434869),(0x3fffff0000000000000000000000fffffc00000,0x4949292524a4949292524a4949292524a4949292),(0x7ff001ffc0000000000000000,0x6c0d81b03606c0d81b03606c0d81b03606c0d81b),(0xfc00000000003ff800000000007ff00000000000,0x706e0dc1b83706e0dc1b83706e0dc1b83706e0dc),(0x1fffff80000000000000,0x82704e09c1382704e09c1382704e09c1382704e0),(0x3fffffffe0000000000000000000,0x380700e01c0380700e01c0380700e01c0380700)]),
  (110,![(0xfff000ffffff000000000000000fff000ffffff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xf000000000000000000000000fff000000000000,0x4314314314314314314314314314314314314314),(0xfff000000000000fff000000000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000000ffffff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000fff000fff000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (115,![(0x0,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000ffffff000000000000fff000ffffff,0x4314314314314314314314314314314314314314),(0xf000000ffffff000000000fff000000ffffff000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000ffffff000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (117,![(0xfff000000000000000000000000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000fff000000ffffff000,0x4314314314314314314314314314314314314314),(0xffff000000000000fff000000000ffffff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (118,![(0xfff000fff000000000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000000000000fff000000000fff000,0x4314314314314314314314314314314314314314),(0xf000fff000000000fff000000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffff000000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (121,![(0xfff000000000000000000000000fff,0x4544544544544544544544544544544544544544),(0xfff000ffffff000000000000000fff000ffffff,0x3823823823823823823823823823823823823823),(0xf000ffffff000000000000000fff000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000fff000000000fff000000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (122,![(0xf000000fff000000000000000ffffff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000fff000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000fff000000000000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (124,![(0xffff000fff000000000000000000ffffff000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000000000000fff000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000000000fff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000fff000fff000000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (143,![(0xfff000fff000000000000000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff000000000,0x3823823823823823823823823823823823823823),(0x0,0x4314314314314314314314314314314314314314),(0xf000000000fff000000000fff000000000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000fff000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000fff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (151,![(0xfff000000000000000000000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff000000000,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff,0x4314314314314314314314314314314314314314),(0xf000000000ffffff000000fff000000000ffffff,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000fff000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000fff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (155,![(0xfff000000000000000000000000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000fff000000000000000fff000000fff,0x3823823823823823823823823823823823823823),(0xf000000ffffff000000000000fff000000ffffff,0x4314314314314314314314314314314314314314),(0xfff000000000fff000000000000fff000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000fff000fff000000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (157,![(0xfff000fff000000000000000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000ffffff000000000000fff000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xf000000000000000000000fff000000000000000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000fff000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000fff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (158,![(0xfffffffff000000000000000fffffffff,0x4544544544544544544544544544544544544544),(0xfff000000fff000000000000fff000000fff,0x3823823823823823823823823823823823823823),(0x0,0x4314314314314314314314314314314314314314),(0xf000000000000000000000fff000000000000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000fff000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000fff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (167,![(0xfff000000000000000000fff000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000fff000000000,0x3823823823823823823823823823823823823823),(0xfff000000000000000000fff,0x4314314314314314314314314314314314314314),(0xfff000fff000fff000000fff000fff000fff,0x9069069069069069069069069069069069069069),(0xffffff000000000000000ffffff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000fff000000000fff000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffff000000000000fffffffff000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (171,![(0xfff000000000000000000000000fff000000,0x4544544544544544544544544544544544544544),(0xf000000000fff000000000000fff000000000fff,0x3823823823823823823823823823823823823823),(0xffffff000000000fff000000000ffffff,0x4314314314314314314314314314314314314314),(0xfff000fff000000000fff000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000fff000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (173,![(0xfff000fff000000000000000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000ffffff000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xf000fff000000000000000fff000fff000000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (174,![(0xfff000ffffff000000000000fff000ffffff,0x4544544544544544544544544544544544544544),(0xfff000000000fff000000000fff000000000fff,0x3823823823823823823823823823823823823823),(0x0,0x4314314314314314314314314314314314314314),(0xf000000fff000000000000fff000000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000fff000000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (179,![(0x0,0x4544544544544544544544544544544544544544),(0xfff000000fff000000000000fff000000fff,0x3823823823823823823823823823823823823823),(0xfff000000ffffff000000000fff000000ffffff,0x4314314314314314314314314314314314314314),(0xf000000ffffff000000000fff000000ffffff000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000fff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (181,![(0xfff000000000000000000000fff,0x4544544544544544544544544544544544544544),(0xfff000000ffffff000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xf000ffffff000000000000fff000ffffff000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (182,![(0xf000fff000fff000000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000000fff000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000000fff000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000000fff000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (185,![(0xfff000000000000000000000fff,0x4544544544544544544544544544544544544544),(0xfff000ffffff000000000000fff000ffffff,0x3823823823823823823823823823823823823823),(0xfff000ffffff000000000000fff000ffffff000,0x4314314314314314314314314314314314314314),(0xf000000fff000000000000fff000000fff000000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000fff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (186,![(0xf000000fff000000000000000ffffff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000fff000000000000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (188,![(0xffffff000fff000000000000ffffff000fff,0x4544544544544544544544544544544544544544),(0xfff000000ffffff000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xf000000000000000000000fff000000000000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000fff000000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (199,![(0xfff000fff000000000000000fff000fff000,0x4544544544544544544544544544544544544544),(0x0,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff,0x4314314314314314314314314314314314314314),(0xf000000fff000fff000000fff000000fff000fff,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xffffff000000000000fff000ffffff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000fff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (203,![(0xfff000000000000000000000fff000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000000ffffff,0x4314314314314314314314314314314314314314),(0xf000fff000000000fff000000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffff000000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (205,![(0xfff000fff000000000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xf000000000000000fff000000000fff000000000,0x9069069069069069069069069069069069069069),(0xffff000000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (206,![(0xfff000ffffff000000000000fff000ffffff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff,0x3823823823823823823823823823823823823823),(0x0,0x4314314314314314314314314314314314314314),(0xf000000fff000000000000fff000000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xffffff000000000000fff000ffffff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000fff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (211,![(0xfff000000000000000000000000fff000000000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xf000000ffffff000000000000fff000000ffffff,0x4314314314314314314314314314314314314314),(0xffffff000000000fff000000000ffffff000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000000fff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000fff000fff000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (213,![(0xfff000000000000000fff000000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xffff000000000000fff000000000ffffff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (214,![(0xf000fff000fff000000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000000fff000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000000fff000ffffff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (217,![(0xf000000fff000000000000000000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000fff000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000fff000000000000fff000000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000fff000fff000000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (218,![(0xf000000fff000000000000000ffffff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000fff000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000fff000000000000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (220,![(0xffffff000fff000000000000000ffffff000fff,0x4544544544544544544544544544544544544544),(0xf000000ffffff000000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000000fff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000fff000fff000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000fff000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (227,![(0xfff000000000000000000000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000ffffff000000000fff000000ffffff,0x4314314314314314314314314314314314314314),(0xf000fff000fff000000000fff000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000fff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (229,![(0xfff000000fff000000000000000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xf000fff000000000000fff000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffff000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (230,![(0xfff000fff000fff000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xf000fff000fff000000000fff000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000fffffffff000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (233,![(0xf000000fff000000000000000000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000fff000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (234,![(0xf000000fff000000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000fff000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (236,![(0xf000fff000fff000000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000fff000000fff000000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000000fff000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (241,![(0xfff000000000000000000000000fff,0x4544544544544544544544544544544544544544),(0xf000000ffffff000000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000ffffff000,0x4314314314314314314314314314314314314314),(0xffffff000000000000fff000000ffffff000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000fff000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (242,![(0xf000000fff000000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000fff000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (244,![(0xf000000fff000000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000fff000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000fff000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (248,![(0xf000000fff000000000000000ffffff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000fff000000000000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (271,![(0xfff000fff000000000000000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff000000000,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000000000000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000fff000000000ffffff000000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffff000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (279,![(0xfff000000000000000000000000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000000fff000000000,0x3823823823823823823823823823823823823823),(0xf000000000fff000000000000fff000000000fff,0x4314314314314314314314314314314314314314),(0xffffff000000fff000000000000ffffff,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000000fff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000fff000fff000000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (283,![(0xfff000000000000000000000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000fff000000000000fff000000fff,0x3823823823823823823823823823823823823823),(0xfff000000ffffff000000000fff000000ffffff,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000fff000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000fff000000000ffffff000000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffff000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (285,![(0xfff000fff000000000000000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000ffffff000000000000fff000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000fff000000000000fff000000fff000,0x4314314314314314314314314314314314314314),(0x0,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000fff000000000ffffff000000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffff000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (286,![(0xfffffffff000000000000000fffffffff,0x4544544544544544544544544544544544544544),(0xfff000000fff000000000000fff000000fff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000000000000,0x4314314314314314314314314314314314314314),(0x0,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000fff000000000ffffff000000fff000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffff000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (295,![(0xfff000000000000000000000fff000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff000000000,0x3823823823823823823823823823823823823823),(0xfff000000000fff000000000fff000000000fff,0x4314314314314314314314314314314314314314),(0xfff000fff000fff000000000fff000fff,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000000000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffff000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (299,![(0xfff000000000000000000000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000000fff000000000fff000000000fff,0x3823823823823823823823823823823823823823),(0xf000000000ffffff000000fff000000000ffffff,0x4314314314314314314314314314314314314314),(0xfff000fff000000000000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000ffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (301,![(0xfff000fff000000000000000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000ffffff000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xf000000000fff000000000fff000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000fff000000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000ffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (302,![(0xfff000ffffff000000000000fff000ffffff,0x4544544544544544544544544544544544544544),(0xfff000000000fff000000000fff000000000fff,0x3823823823823823823823823823823823823823),(0xf000000000000000000000fff000000000000000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000fff000000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000ffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (307,![(0x0,0x4544544544544544544544544544544544544544),(0xfff000000fff000000000000fff000000fff,0x3823823823823823823823823823823823823823),(0xfff000000ffffff000000000fff000000ffffff,0x4314314314314314314314314314314314314314),(0xffffff000000fff000000000ffffff000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000000000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffff000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (309,![(0xfff000000000000000000000000fff,0x4544544544544544544544544544544544544544),(0xf000000ffffff000000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000ffffff000,0x4314314314314314314314314314314314314314),(0xffffff000000000fff000000000ffffff000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000fff000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (310,![(0xfc007ff001ffc00000000000007ff001ffc007ff,0x1142284508a1142284508a1142284508a1142284),(0x1ffc00000000003ff800000000007ff,0x8e11c2384708e11c2384708e11c2384708e11c23),(0xffe00000000001ffc00000000003ff800,0x50ca194328650ca194328650ca194328650ca194),(0x3ff800ffe000007ff00000000000ffe003ff800,0xa4148290520a4148290520a4148290520a414829),(0x3fffff0000000000000000000000fffffc00000,0x4aa9552aa554aa9552aa554aa9552aa554aa9552),(0xfc0000000000000000ffe000007ff00000000000,0x6c0d81b03606c0d81b03606c0d81b03606c0d81b),(0x3ff800000003ff80000000000000,0x702e05c0b81702e05c0b81702e05c0b81702e05c),(0xfffffc0000000000000000,0x8330660cc198330660cc198330660cc198330660),(0x3fffff0000000000000000000000,0x3c0780f01e03c0780f01e03c0780f01e03c0780)]),
  (313,![(0xfff000000000000000000fff,0x4544544544544544544544544544544544544544),(0xfff000ffffff000000000fff000ffffff,0x3823823823823823823823823823823823823823),(0xfff000ffffff000000000fff000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000fff000000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000fff000000000fff000000fff000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000000fff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (314,![(0xffff000000fff000000000000ffffff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000000fff000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000000fff000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (316,![(0xffffff000fff000000000000ffffff000fff,0x4544544544544544544544544544544544544544),(0xfff000000ffffff000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xf000000000fff000000000fff000000000fff000,0x4314314314314314314314314314314314314314),(0x0,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000fff000000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000ffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (327,![(0xfff000fff000000000000000fff000fff000,0x4544544544544544544544544544544544544544),(0x0,0x3823823823823823823823823823823823823823),(0xfff000000000fff000000000fff000000000fff,0x4314314314314314314314314314314314314314),(0xfff000fff000fff000000000fff000fff,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000fff000000000fff000fff000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffff000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (331,![(0xfff000fff000000000000000fff000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xf000000000ffffff000000fff000000000ffffff,0x4314314314314314314314314314314314314314),(0xfff000fff000000000000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000ffffff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000ffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (333,![(0xf000fff000fff000000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000000fff000000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000000fff000000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000ffffff000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (334,![(0xfff000ffffff000000000fff000ffffff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000fff000000000000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000ffffff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xffff000fff000000000ffffff000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000000fff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (339,![(0xfff000000000000000000000fff000000000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000ffffff000000000fff000000ffffff,0x4314314314314314314314314314314314314314),(0xffffff000000fff000000000ffffff000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000fff000000000fff000fff000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffff000000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (341,![(0xfff000000000000000fff000000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xffff000000000fff000000000000ffffff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (342,![(0xf000fff000fff000000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000000000fff000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000fff000000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000fff000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (345,![(0xfff000000fff000000000000fff000000fff,0x4544544544544544544544544544544544544544),(0xfff000000ffffff000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xf000000ffffff000000000fff000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000fff000000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000ffffff000000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000ffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (346,![(0xffffff000000fff000000000ffffff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000000ffffff,0x3823823823823823823823823823823823823823),(0xf000000ffffff000000000fff000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000fff000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000ffffff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000ffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (348,![(0xffffff000fff000000000000ffffff000fff,0x4544544544544544544544544544544544544544),(0xfff000000ffffff000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xf000000000fff000000000fff000000000fff000,0x4314314314314314314314314314314314314314),(0x0,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000ffffff000000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000ffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (355,![(0xfff000000000000000000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000ffffff000000fff000000ffffff,0x4314314314314314314314314314314314314314),(0xf000000fff000fff000fff000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000ffffff000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000000fff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (357,![(0xfff000000fff000000000000000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xf000fff000000fff000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffff000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (358,![(0xfff000fff000fff000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xf000000000fff000000000fff000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000fff000fff000000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000ffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (361,![(0xfff000000fff000000000000fff000000fff,0x4544544544544544544544544544544544544544),(0xf000000000ffffff000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0x0,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (362,![(0xf000fff000000fff000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000000fff000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0x0,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (364,![(0xfff000fff000fff000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xf000000000ffffff000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000fff000000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000fff000000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000fff000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0x0,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (369,![(0xfff000000000000000000000fff,0x4544544544544544544544544544544544544544),(0xfff000000ffffff000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xf000000ffffff000000000fff000000ffffff000,0x4314314314314314314314314314314314314314),(0xffffff000000fff000000000ffffff000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000ffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (370,![(0xfff000000fff000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xf000fff000000fff000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffff000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (372,![(0xf000000fff000000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000fff000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000fff000000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (376,![(0xffffff000000fff000000000ffffff000000fff,0x4544544544544544544544544544544544544544),(0xf000000000ffffff000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000fff000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000fff000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0x0,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (391,![(0xfff000fff000000000000000000fff000fff000,0x4544544544544544544544544544544544544544),(0xf000000000000000000000000fff000000000000,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000000fff,0x4314314314314314314314314314314314314314),(0xfff000fff000000fff000000000fff000fff,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000000ffffff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000fff000fff000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000fff000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (395,![(0xfc007ff00000000000000000007ff001ffc00000,0x91522a4548a91522a4548a91522a4548a91522a4),(0x1ffc00000000003ff800000000007ff,0x4e09c1382704e09c1382704e09c1382704e09c13),(0xfffffc00000001ffc00000000003fffff,0x10c2184308610c2184308610c2184308610c2184),(0x3ff800ffe0000000000000000000ffe003ff800,0xe41c8390720e41c8390720e41c8390720e41c839),(0x3fffff0000000000000000000000fffffc00000,0xaa1542a8550aa1542a8550aa1542a8550aa1542),(0xfc00000000000007ffffe000007ff00000000000,0x2c0580b01602c0580b01602c0580b01602c0580b),(0x3ff800000003ff80000000000000,0xb03606c0d81b03606c0d81b03606c0d81b03606c),(0xfffffc0000000000000000,0xc338670ce19c338670ce19c338670ce19c338670),(0x3fffff0000000000000000000000,0x3c0780f01e03c0780f01e03c0780f01e03c0780)]),
  (397,![(0xf000fff000fff000000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000000fff000000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000000ffffff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (398,![(0xfff000ffffff000000000000fff000ffffff,0x4544544544544544544544544544544544544544),(0xfff000000000fff000000000fff000000000fff,0x3823823823823823823823823823823823823823),(0x0,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000fff000000000000ffffff000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000fff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (403,![(0xf000000000000000000000000000fff000000000,0x4544544544544544544544544544544544544544),(0xfff000000000000000fff000000000fff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000000ffffff,0x4314314314314314314314314314314314314314),(0xffffff000000000fff000000000000ffffff000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000000000fff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000fff000fff000000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (405,![(0xfff000000000000000fff000000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xffff000000000000fff000000000ffffff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (406,![(0xfff000fff000000000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000000000fff000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xf000fff000000000fff000000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffff000000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (409,![(0xfff000000fff000000000000000fff000000fff,0x4544544544544544544544544544544544544544),(0xf000000ffffff000000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000000fff000000,0x9069069069069069069069069069069069069069),(0x0,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000ffffff000000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000fff000000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (410,![(0xf000000fff000000000000000ffffff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000000000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xffffff000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (412,![(0xffffff000fff000000000000ffffff000fff,0x4544544544544544544544544544544544544544),(0xfff000000ffffff000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0x0,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000fff000000000000ffffff000fff000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000fff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (419,![(0xfff000000000000000000000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000000fff000000000fff000000000fff,0x3823823823823823823823823823823823823823),(0xf000000000ffffff000000fff000000000ffffff,0x4314314314314314314314314314314314314314),(0xfff000fff000000fff000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0x0,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000fff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (421,![(0xfff000000fff000000000000fff000000fff,0x4544544544544544544544544544544544544544),(0xf000000000ffffff000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000000fff000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0x0,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000000fff000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (422,![(0xfff000fff000fff000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xf000000000000fff000000fff000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000fff000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000000fff000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (425,![(0xfff000000fff000000000000fff000000fff,0x4544544544544544544544544544544544544544),(0xf000000000ffffff000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0x0,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000000fff000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (426,![(0xfff000000fff000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000fff000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000fff000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xf000fff000000000000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffff000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000fff000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (428,![(0xfff000fff000fff000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000000ffffff000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000fff000000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xffff000000000000000ffffff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xf000000000000000000fff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (433,![(0xfff000000000000000000000fff,0x4544544544544544544544544544544544544544),(0xfff000000ffffff000000000fff000000ffffff,0x3823823823823823823823823823823823823823),(0xf000000ffffff000000000fff000000ffffff000,0x4314314314314314314314314314314314314314),(0xffffff000000000fff000000ffffff000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0x0,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000fff000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000fff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (434,![(0xf000000fff000000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000fff000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000fff000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000fff000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (436,![(0xfff000000fff000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000fff000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xf000fff000000000fff000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffff000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000fff000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (440,![(0xffffff000000fff000000000ffffff000000fff,0x4544544544544544544544544544544544544544),(0xf000000000ffffff000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000fff000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000000fff000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (451,![(0xf000fff000000000000000000fff000fff000000,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xffffff000000000fff000000000ffffff,0x4314314314314314314314314314314314314314),(0xfff000fff000000fff000000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000fff000fff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (453,![(0xf000000fff000000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000fff000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (454,![(0xfff000fff000fff000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xfff000000000000000000000fff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000fff000000fff000fff000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xffff000000000000fff000ffffff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xf000000000000000000000fff000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (457,![(0xf000000fff000000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000fff000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xffffff000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (458,![(0xfff000000fff000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xf000fff000000000000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffff000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xffffff000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (460,![(0xfff000fff000fff000000000fff000fff000fff,0x4544544544544544544544544544544544544544),(0xf000000000ffffff000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xfff000000000000000000000fff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000fff000000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000ffffff000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (465,![(0xfff000000000000000fff000000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xffff000000000fff000000000000ffffff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (466,![(0xf000000fff000000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000fff000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (468,![(0xf000000fff000000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000fff000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xf000000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (472,![(0xffff000000fff000000000000ffffff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000000000000000000000000fff000000,0x9069069069069069069069069069069069069069),(0xfff000000000000000000000000fff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000ffffff000000fff000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (481,![(0xfff000000fff000000000000fff000000fff,0x4544544544544544544544544544544544544544),(0xf000000000ffffff000000fff000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000fff000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0x0,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xf000000000000000000000fff000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (482,![(0xf000fff000000fff000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000fff000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000fff000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000000000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0x0,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (484,![(0xf000fff000000fff000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000fff000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000fff000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000000000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0x0,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (488,![(0xf000fff000000fff000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000fff000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000fff000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xfff000fff000000000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffffff000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xf000000000000000000000fff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0x0,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)]),
  (496,![(0xfff000000fff000000000fff000fff000000fff,0x4544544544544544544544544544544544544544),(0xffffff000000fff000000000000ffffff,0x3823823823823823823823823823823823823823),(0xffffff000000fff000000000000ffffff000,0x4314314314314314314314314314314314314314),(0xf000fff000000fff000000000fff000fff000000,0x9069069069069069069069069069069069069069),(0xffff000000000000000000000ffffff000000000,0x2a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000000000000000,0xb01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000000000,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00)])]
def maskArray : Array Nat := #[31,47,55,59,61,62,79,87,91,93,94,103,107,109,110,115,117,118,121,122,124,143,151,155,157,158,167,171,173,174,179,181,182,185,186,188,199,203,205,206,211,213,214,217,218,220,227,229,230,233,234,236,241,242,244,248,271,279,283,285,286,295,299,301,302,307,309,310,313,314,316,327,331,333,334,339,341,342,345,346,348,355,357,358,361,362,364,369,370,372,376,391,395,397,398,403,405,406,409,410,412,419,421,422,425,426,428,433,434,436,440,451,453,454,457,458,460,465,466,468,472,481,482,484,488,496]

def entry (j : Fin 126) : Entry := table[j.val]'(by
  have h : table.size = 126 := by decide +kernel
  omega)

def verified (j : Fin 126) : Bool :=
  let e := entry j
  rowCheck e.1 e.2 && decide (wires e.2).Nodup && check e.2

def maskAt (j : Fin 126) : Nat := maskArray[j.val]'(by
  have h : maskArray.size=126 := by decide +kernel
  omega)

theorem at_mask : ∀ i : Fin 126, (entry i).1=maskAt i := by decide +kernel

theorem present : ∀ b : Fin 512, pop b.val=5 → ∃ j : Fin 126, (entry j).1=b.val := by
  have hits : ∀ b : Fin 512, pop b.val=5 →
      ∃ j : Fin 126, maskAt j = b.val := by decide +kernel
  intro b hb
  obtain ⟨j,h⟩ := hits b hb
  exact ⟨j,(at_mask j).trans h⟩

end CoPortBanks4482

namespace CoPortProof4482
open CoPortEngine4482 CoPortSlice4482 CoPortRows4482 CoPortBanks4482
open PEqualNP.CircuitLowerBounds CoSwitch3302.MonotoneWires3302
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all_cases (i : Fin 126) : verified i = true := by
  fin_cases i <;> decide +kernel

theorem one_computed (b : Fin 512) (five : pop b.val=5) (gs : List Gate)
    (len : gs.length≤7) (legal : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (z : Nat) : ∃ x y : Input, graph x ≠ graph y ∧ sameOn b.val x y ∧
      value (whole gs) x z = value (whole gs) y z := by
  obtain ⟨j,e⟩ := present b five
  have h := all_cases j
  simp only [verified,Bool.and_eq_true,decide_eq_true_eq] at h
  have rv := rows h.1.1
  have no := no_decision (entry j).1 (entry j).2 h.1.2 h.2
    (fun i => (rv i).1) (fun i => (rv i).2) gs len legal z
  rw [e] at no
  by_contra bad
  apply no
  intro x y seen eq
  by_contra ne
  exact bad ⟨x,y,ne,seen,eq⟩

def widened : Array (Fin 512) := #[31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,55,55,55,55,55,55,55,55,59,59,59,59,61,61,62,63,79,79,79,79,79,79,79,79,79,79,79,79,79,79,79,79,87,87,87,87,87,87,87,87,91,91,91,91,93,93,94,95,103,103,103,103,103,103,103,103,107,107,107,107,109,109,110,111,115,115,115,115,117,117,118,119,121,121,122,123,124,125,126,127,143,143,143,143,143,143,143,143,143,143,143,143,143,143,143,143,151,151,151,151,151,151,151,151,155,155,155,155,157,157,158,159,167,167,167,167,167,167,167,167,171,171,171,171,173,173,174,175,179,179,179,179,181,181,182,183,185,185,186,187,188,189,190,191,199,199,199,199,199,199,199,199,203,203,203,203,205,205,206,207,211,211,211,211,213,213,214,215,217,217,218,219,220,221,222,223,227,227,227,227,229,229,230,231,233,233,234,235,236,237,238,239,241,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,271,271,271,271,271,271,271,271,271,271,271,271,271,271,271,271,279,279,279,279,279,279,279,279,283,283,283,283,285,285,286,287,295,295,295,295,295,295,295,295,299,299,299,299,301,301,302,303,307,307,307,307,309,309,310,311,313,313,314,315,316,317,318,319,327,327,327,327,327,327,327,327,331,331,331,331,333,333,334,335,339,339,339,339,341,341,342,343,345,345,346,347,348,349,350,351,355,355,355,355,357,357,358,359,361,361,362,363,364,365,366,367,369,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,391,391,391,391,391,391,391,391,395,395,395,395,397,397,398,399,403,403,403,403,405,405,406,407,409,409,410,411,412,413,414,415,419,419,419,419,421,421,422,423,425,425,426,427,428,429,430,431,433,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,451,451,451,451,453,453,454,455,457,457,458,459,460,461,462,463,465,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,481,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511]

def extendMask (b : Fin 512) : Fin 512 := widened[b.val]'(by
  have h : widened.size=512 := by decide +kernel
  omega)

theorem extension : ∀ b : Fin 512, pop b.val≤5 → pop (extendMask b).val=5 ∧
    ∀ i : Fin 9, b.val.testBit i.val=true → (extendMask b).val.testBit i.val=true := by decide +kernel

theorem at_most_five (b : Fin 512) (small : pop b.val≤5) (gs : List Gate)
    (len : gs.length≤7) (legal : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (z : Nat) : ∃ x y : Input, graph x ≠ graph y ∧ sameOn b.val x y ∧
      value (whole gs) x z = value (whole gs) y z := by
  obtain ⟨sz,more⟩ := extension b small
  obtain ⟨x,y,ne,s,e⟩ := one_computed (extendMask b) sz gs len legal z
  exact ⟨x,y,ne,fun i h => s i (more i h),e⟩

theorem wire_observations {ports : Finset Nat} (b : Fin 512) (small : pop b.val≤5)
    (gs : List Gate) (len : gs.length≤7)
    (legal : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) (z : Nat)
    (covered : ∀ u∈ports, u=z ∨ ∃ j : Fin 9, u=j.val ∧ b.val.testBit j.val=true) :
    ∃ x y : Input, graph x≠graph y ∧ ∀u∈ports,
      ((whole gs).wires (List.ofFn x)).getD u false = ((whole gs).wires (List.ofFn y)).getD u false := by
  obtain ⟨x,y,ne,seen,e⟩ := at_most_five b small gs len legal z
  refine ⟨x,y,ne,?_⟩
  intro u hu
  rcases covered u hu with rfl|⟨j,rfl,on⟩
  · exact e
  · change value _ x j = value _ y j
    simpa only [input_value] using seen j on

#print axioms wire_observations

#print axioms one_computed
end CoPortProof4482


namespace CoPortStatement4482
open PEqualNP.CircuitLowerBounds CoPortSlice4482 CoPortBanks4482 CoPortProof4482
open CoSwitch3302.MonotoneWires3302

private def pack (f : Fin 9 → Bool) : Fin 512 :=
  (BitVec.ofBoolListLE (List.ofFn f)).toFin.cast (by simp [List.length_ofFn])

private theorem pack_bit (f : Fin 9 → Bool) (i : Fin 9) : (pack f).val.testBit i.val=f i := by
  change (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

private def rawSet (b : Fin 512) : Finset (Fin 9) :=
  Finset.univ.filter fun i => b.val.testBit i.val = true

private theorem raw_card : ∀ b : Fin 512, (rawSet b).card = pop b.val := by decide +kernel

/-- With OR(0,2) precomputed and at most seven AND/OR gates, at most five
raw readings and any one physical wire cannot determine the graph predicate.
All 512 inputs and the circuit library's true wire evaluation are used. -/
theorem one_computed_wire :
    let f : (Fin 9 → Bool) → Bool := fun x =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun t =>
        x (Fin.ofNat 9 (t/10)) && x (Fin.ofNat 9 (t%10))
    ∀ gs : List Gate, gs.length ≤ 7 →
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      ∀ B : Finset (Fin 9), B.card ≤ 5 → ∀ z : ℕ,
        let C : Circuit := ⟨(⟨.or,[0,2]⟩ : Gate) :: gs,0⟩
        ∃ x y : Fin 9 → Bool, f x ≠ f y ∧ (∀ i∈B, x i = y i) ∧
          (C.wires (List.ofFn x)).getD z false = (C.wires (List.ofFn y)).getD z false := by
  dsimp only
  intro gs n legal B small z
  let b := pack (fun i => decide (i∈B))
  have val (i : Fin 9) : b.val.testBit i.val = decide (i∈B) := pack_bit _ _
  have set_eq : rawSet b = B := by
    ext i
    simp [rawSet,val]
  have sz : pop b.val ≤ 5 := by rw [←raw_card b,set_eq]; exact small
  obtain ⟨x,y,ne,h,e⟩ := at_most_five b sz gs n legal z
  exact ⟨x,y,ne,fun i hi => h i (by simp [val,hi]),e⟩

#print axioms one_computed_wire
end CoPortStatement4482
