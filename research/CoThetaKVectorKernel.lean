import Mathlib
import PEqualNP.Defs


namespace CoThetaWholeBase
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

inductive ReadTree where
  | atom : Sig → ReadTree
  | inv : ReadTree → ReadTree
  | fork : Bool → ReadTree → ReadTree → ReadTree

def ReadTree.value : ReadTree → Sig
  | .atom a => a
  | .inv e => neg e.value
  | .fork d e f => bin d e.value f.value

def ReadTree.sources : ReadTree → Finset Sig
  | .atom a => {a}
  | .inv e => e.sources
  | .fork _ e f => e.sources ∪ f.sources

def ReadTree.linear : ReadTree → Prop
  | .atom _ => True
  | .inv e => e.linear
  | .fork _ e f => e.linear ∧ f.linear ∧ Disjoint e.sources f.sources

def ReadTree.plug : ReadTree → Sig → ReadTree → ReadTree
  | .atom a, z, r => if a = z then r else .atom a
  | .inv e, z, r => .inv (e.plug z r)
  | .fork d e f, z, r => .fork d (e.plug z r) (f.plug z r)

private lemma plug_value (e : ReadTree) {z : Sig} {r : ReadTree} (hr : r.value=z) :
    (e.plug z r).value=e.value := by
  induction e with
  | atom a => by_cases h : a=z <;> simp [ReadTree.plug,ReadTree.value,h,hr]
  | inv e ih => simp [ReadTree.plug,ReadTree.value,ih]
  | fork d e f ih jh => simp [ReadTree.plug,ReadTree.value,ih,jh]

private lemma plug_mem (e : ReadTree) (z w : Sig) (r : ReadTree) :
    w ∈ (e.plug z r).sources ↔ (w ∈ e.sources ∧ w ≠ z) ∨ (z ∈ e.sources ∧ w ∈ r.sources) := by
  induction e with
  | atom a =>
    by_cases h : a=z
    · subst a; simp [ReadTree.plug,ReadTree.sources]
    · have hz : z ≠ a := Ne.symm h
      by_cases hw : w=a <;> simp_all [ReadTree.plug,ReadTree.sources]
  | inv e ih => exact ih
  | fork d e f ih jh =>
    simp only [ReadTree.plug,ReadTree.sources,Finset.mem_union,ih,jh]; tauto

private lemma plug_linear (e : ReadTree) {z : Sig} {r : ReadTree} (he : e.linear) (hr : r.linear)
    (fresh : ∀ w ∈ r.sources, w ∈ e.sources → w = z) : (e.plug z r).linear := by
  induction e with
  | atom a => by_cases ha : a=z <;> simp [ReadTree.plug,ReadTree.linear,ha,hr]
  | inv e ih => exact ih he fresh
  | fork d e f ih jh =>
    obtain ⟨h1,h2,h3⟩ := he
    refine ⟨ih h1 (fun w hw hs => fresh w hw (Finset.mem_union_left _ hs)),
      jh h2 (fun w hw hs => fresh w hw (Finset.mem_union_right _ hs)), ?_⟩
    rw [Finset.disjoint_left] at h3 ⊢
    intro w hw hv
    rcases (plug_mem e z w r).mp hw with ⟨he,hn⟩ | ⟨hz,hr'⟩ <;>
      rcases (plug_mem f z w r).mp hv with ⟨hf,hm⟩ | ⟨hz',hr''⟩
    · exact h3 he hf
    · exact hn (fresh w hr'' (Finset.mem_union_left _ he))
    · exact hm (fresh w hr' (Finset.mem_union_right _ hf))
    · exact h3 hz hz'

theorem tight_tree {k t S} (h : Live k t S) (tight : S.card+t=k+1) :
    ∃ e : ReadTree, e.value = target ∧ e.linear ∧ e.sources = S := by
  induction h with
  | stop => exact ⟨.atom target,rfl,trivial,rfl⟩
  | @unary k t U a ha hf tail ih =>
    have hn : neg a ∉ U := fun h => hf (Finset.mem_insert_of_mem h)
    have size := (live_size tail).2
    rw [Finset.card_insert_of_notMem hn] at size
    have hu : a ∉ U := by
      intro hh; rw [Finset.insert_eq_of_mem hh] at tight; omega
    rw [Finset.card_insert_of_notMem hu] at tight
    obtain ⟨e,he,hl,hS⟩ := ih (by rw [Finset.card_insert_of_notMem hn]; omega)
    let r : ReadTree := .inv (.atom a)
    refine ⟨e.plug (neg a) r,(plug_value e (show r.value = neg a from rfl)).trans he,
      plug_linear e hl (show r.linear from trivial) ?_, ?_⟩
    · intro w hw old
      have hw' : w=a := by simpa [r,ReadTree.sources] using hw
      subst w
      exact (Finset.mem_insert.mp (hS ▸ old)).resolve_right hu
    · ext w
      rw [plug_mem,hS]
      simp only [r,ReadTree.sources,Finset.mem_singleton,Finset.mem_insert]
      aesop
  | @binary k t U a b d ha hb hab hf tail ih =>
    let z := bin d a b
    have hn : z ∉ U := fun hh => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hh))
    have size := (live_size tail).2
    change (insert z U).card+t ≤ k+1 at size
    rw [Finset.card_insert_of_notMem hn] at size
    have na : a ∉ insert b U := by
      intro h'
      rw [Finset.insert_eq_of_mem h'] at tight
      have ch := Finset.card_insert_le b U
      omega
    rw [Finset.card_insert_of_notMem na] at tight
    have nb : b ∉ U := by intro h'; rw [Finset.insert_eq_of_mem h'] at tight; omega
    rw [Finset.card_insert_of_notMem nb] at tight
    have au : a ∉ U := fun ah => na (Finset.mem_insert_of_mem ah)
    obtain ⟨e,he,hl,hS⟩ := ih (by change (insert z U).card+t=k+1; rw [Finset.card_insert_of_notMem hn]; omega)
    let r : ReadTree := .fork d (.atom a) (.atom b)
    have vr : r.linear := by simpa [r,ReadTree.linear,ReadTree.sources] using hab
    refine ⟨e.plug z r,(plug_value e (show r.value=z from rfl)).trans he,plug_linear e hl vr ?_,?_⟩
    · intro w hw old
      have hm : w=a ∨ w=b := by simpa [r,ReadTree.sources] using hw
      rcases Finset.mem_insert.mp (hS ▸ old) with eq | u
      · exact eq
      · rcases hm with rfl | rfl
        · exact (au u).elim
        · exact (nb u).elim
    · ext w
      rw [plug_mem,hS]
      simp only [r,ReadTree.sources,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert]
      change (((w = z ∨ w ∈ U) ∧ w ≠ z) ∨ ((z = z ∨ z ∈ U) ∧ (w = a ∨ w = b))) ↔ _
      aesop

abbrev Row := Bool × Fin 256

def rowValue (r : Row) (a : Sig) := bit r.1 r.2 a

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

theorem span_range {f : Nat → Bool} {n o : Nat} (h : span f n o=true) :
    ∀ i, o ≤ i → i < o+n → f i=true := span_ok h

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

namespace TwoInputs

abbrev T := BitVec 4
def tx : T := 12
def ty : T := 10
def top4 : T := 15
def phase4 (b : Bool) (t : T) : T := if b then ~~~t else t
def op4 (d : Bool) (a b : T) : T := if d then a ||| b else a &&& b
def unary4 (t : T) := t=0 ∨ t=15 ∨ t=12 ∨ t=3 ∨ t=10 ∨ t=5

inductive Profile where
  | flat
  | x : Bool → Profile
  | y : Bool → Profile
  | pair : T → Profile

def Profile.main : Profile → T
  | .flat => 0
  | .x n => phase4 n tx
  | .y n => phase4 n ty
  | .pair t => t

def Profile.hasX : Profile → Bool | .x _ | .pair _ => true | _ => false
def Profile.hasY : Profile → Bool | .y _ | .pair _ => true | _ => false

def Profile.allow (s : Profile) (v : T) : Prop :=
  match s with
  | .flat => v=0 ∨ v=15
  | .pair m => unary4 v ∨ v=m
  | _ => v=0 ∨ v=15 ∨ v=s.main

def rev : Profile → Profile
  | .flat => .flat
  | .x n => .x (!n)
  | .y n => .y (!n)
  | .pair v => .pair (~~~v)

def combine (d : Bool) (s t : Profile) : Profile :=
  match s,t with
  | .flat,_ => t
  | _,.flat => s
  | _,_ => .pair (op4 d s.main t.main)

def compatible (s t : Profile) :=
  ¬ (s.hasX=true ∧ t.hasX=true) ∧ ¬ (s.hasY=true ∧ t.hasY=true)

private lemma marks_rev (s : Profile) : (rev s).hasX = s.hasX ∧ (rev s).hasY = s.hasY := by
  cases s <;> decide +revert

private lemma marks_combine (d : Bool) (s t : Profile) (h : compatible s t) :
    (combine d s t).hasX = (s.hasX || t.hasX) ∧ (combine d s t).hasY = (s.hasY || t.hasY) := by
  cases s <;> cases t <;> simp [compatible,combine,Profile.hasX,Profile.hasY] at *

private lemma allow_rev (s : Profile) (w : T) (h : s.allow w) : (rev s).allow (~~~w) := by
  cases s <;> simp only [rev,Profile.allow,Profile.main,phase4,tx,ty,unary4] at * <;> decide +revert +kernel

private lemma allow_combine (d : Bool) (s t : Profile) (a b : T)
    (h : compatible s t) (ha : s.allow a) (hb : t.allow b) : (combine d s t).allow (op4 d a b) := by
  cases s <;> cases t <;> cases d <;>
    simp [compatible,Profile.hasX,Profile.hasY,combine,op4,Profile.allow,Profile.main,phase4,tx,ty,unary4] at * <;> decide +revert +kernel

private lemma allow_or_main (s : Profile) (t : T) (h : s.allow t) : unary4 t ∨ t=s.main := by
  cases s <;> simp only [Profile.allow,Profile.main,phase4,tx,ty,unary4] at * <;> decide +revert +kernel

def atomProfile (a b x : Sig) : Profile := if x=a then .x false else if x=b then .y false else .flat

def describe (a b : Sig) : ReadTree → Profile
  | .atom x => atomProfile a b x
  | .inv e => rev (describe a b e)
  | .fork d e f => combine d (describe a b e) (describe a b f)

def interpret (assign : Sig → T) : ReadTree → T
  | .atom a => assign a
  | .inv e => ~~~(interpret assign e)
  | .fork d e f => op4 d (interpret assign e) (interpret assign f)

theorem profile_sound (a b : Sig) (hab : a≠b) (e : ReadTree) (linear : e.linear) :
    ((describe a b e).hasX=true ↔ a ∈ e.sources) ∧ ((describe a b e).hasY=true ↔ b ∈ e.sources) ∧
    ∀ env : Sig → T, (∀ w ∈ e.sources, (atomProfile a b w).allow (env w)) →
      (describe a b e).allow (interpret env e) := by
  induction e with
  | atom w =>
    refine ⟨?_,?_,fun env h => h w (Finset.mem_singleton_self w)⟩ <;>
      simp only [describe,atomProfile,ReadTree.sources,Finset.mem_singleton] <;>
      split_ifs <;> simp only [Profile.hasX,Profile.hasY] <;> grind
  | inv e ih =>
    obtain ⟨hx,hy,hh⟩ := ih linear
    refine ⟨?_,?_,fun env h => allow_rev _ _ (hh env h)⟩
    · change (rev _).hasX=true ↔ _; rw [(marks_rev _).1]; exact hx
    · change (rev _).hasY=true ↔ _; rw [(marks_rev _).2]; exact hy
  | fork d e f ih jh =>
    obtain ⟨le_,lf,dis⟩ := linear
    obtain ⟨ex,ey,he⟩ := ih le_
    obtain ⟨fx,fy,hf⟩ := jh lf
    have hc : compatible (describe a b e) (describe a b f) := by
      rw [Finset.disjoint_left] at dis
      exact ⟨fun h => dis (ex.mp h.1) (fx.mp h.2),fun h => dis (ey.mp h.1) (fy.mp h.2)⟩
    obtain ⟨mx,my⟩ := marks_combine d _ _ hc
    refine ⟨?_,?_,?_⟩
    · simp only [describe,mx,Bool.or_eq_true,ex,fx,ReadTree.sources,Finset.mem_union]
    · simp only [describe,my,Bool.or_eq_true,ey,fy,ReadTree.sources,Finset.mem_union]
    · intro env h
      exact allow_combine d _ _ _ _ hc (he env (fun w hw => h w (Finset.mem_union_left _ hw)))
        (hf env (fun w hw => h w (Finset.mem_union_right _ hw)))

theorem same_interaction (a b : Sig) (hab : a≠b) (e : ReadTree) (linear : e.linear)
    (env1 env2 : Sig → T) (h1 : ∀ w ∈ e.sources, (atomProfile a b w).allow (env1 w))
    (h2 : ∀ w ∈ e.sources, (atomProfile a b w).allow (env2 w))
    (n1 : ¬ unary4 (interpret env1 e)) (n2 : ¬ unary4 (interpret env2 e)) :
    interpret env1 e = interpret env2 e := by
  have H := (profile_sound a b hab e linear).2.2
  exact ((allow_or_main _ _ (H env1 h1)).resolve_left n1).trans
    ((allow_or_main _ _ (H env2 h2)).resolve_left n2).symm

end TwoInputs

namespace TwoInputs

structure Group where
  anchor : Row
  samples : List (Row × Fin 4)

def inputTable (a b : Sig) (r : Row) (w : Sig) : T :=
  if w = a then tx else if w=b then ty else if rowValue r w then 15 else 0

private theorem input_allowed (a b : Sig) (r : Row) (w : Sig) :
    (atomProfile a b w).allow (inputTable a b r w) := by
  unfold atomProfile inputTable
  split_ifs <;> simp [Profile.allow,Profile.main,phase4]

def Group.valid (g : Group) (v : List Sig) (a b : Sig) :=
  g.samples.all fun rc => v.all fun w =>
    (inputTable a b g.anchor w).getLsbD rc.2.val == rowValue rc.1 w

def Group.accept (g : Group) (t : T) :=
  g.samples.all fun rc => t.getLsbD rc.2.val == rc.1.1

instance (t : T) : Decidable (unary4 t) := by unfold unary4; infer_instance

def twoGroups (v : List Sig) (a b : Sig) (g h : Group) :=
  decide (a≠b ∧ g.valid v a b=true ∧ h.valid v a b=true ∧
    (∀ t : T, unary4 t → g.accept t=false ∧ h.accept t=false) ∧
    (∀ t : T, ¬(g.accept t=true ∧ h.accept t=true)))

private theorem interpret_bit (e : ReadTree) (env : Sig → T) (r : Row) (i : Fin 4)
    (h : ∀ w ∈ e.sources, (env w).getLsbD i.val = rowValue r w) :
    (interpret env e).getLsbD i.val = rowValue r e.value := by
  induction e with
  | atom a => exact h a (Finset.mem_singleton_self _)
  | inv e ih =>
    change (~~~interpret env e).getLsbD i.val = bit r.1 r.2 (neg e.value)
    rw [BitVec.getLsbD_not,bit_neg]
    simpa only [rowValue,i.isLt,decide_true,Bool.true_and] using congrArg Bool.not (ih h)
  | fork d e f ih jh =>
    have he := ih (fun w hw => h w (Finset.mem_union_left _ hw))
    have hf := jh (fun w hw => h w (Finset.mem_union_right _ hw))
    cases d <;> simp only [interpret,op4,ReadTree.value,rowValue,bit_bin,Bool.false_eq_true,↓reduceIte,
      BitVec.getLsbD_and,BitVec.getLsbD_or] <;> unfold rowValue at he hf <;> rw [he,hf]

private lemma target_side (r : Row) : rowValue r target = r.1 := by
  obtain ⟨d,i⟩ := r
  cases d
  · change (0 : B).getLsbD i.val = false; simp
  · change (BitVec.allOnes 256).getLsbD i.val=true
    rw [BitVec.getLsbD_allOnes]; simp

private lemma accepts_tree (g : Group) (v : List Sig) (a b : Sig) (e : ReadTree)
    (he : e.value=target) (hs : e.sources=v.toFinset) (hg : g.valid v a b=true) :
    g.accept (interpret (inputTable a b g.anchor) e)=true := by
  apply List.all_eq_true.mpr
  intro rc hr
  have hv := List.all_eq_true.mp hg rc hr
  apply beq_iff_eq.mpr
  have hk := interpret_bit e (inputTable a b g.anchor) rc.1 rc.2 (fun w hw =>
    beq_iff_eq.mp (List.all_eq_true.mp hv w (List.mem_toFinset.mp (hs ▸ hw))))
  rw [he] at hk
  exact hk.trans (target_side rc.1)

theorem exclude_conflicting_groups (k t : Nat) (v : List Sig) (hn : v.Nodup)
    (tight : v.length+t=k+1) (a b : Sig) (g h : Group) (cert : twoGroups v a b g h=true) :
    Impossible k t v := by
  intro m hm live
  have bound := (live_size live.live).2
  rw [List.toFinset_card_of_nodup hn] at bound
  obtain ⟨e,he,hl,hs⟩ := tight_tree live.live (by rw [List.toFinset_card_of_nodup hn]; omega)
  obtain ⟨hne,hg,hh,huni,hdiff⟩ := of_decide_eq_true cert
  have ag := accepts_tree g v a b e he hs hg
  have ah := accepts_tree h v a b e he hs hh
  have eq := same_interaction a b hne e hl (inputTable a b g.anchor) (inputTable a b h.anchor)
    (fun w _ => input_allowed _ _ _ _) (fun w _ => input_allowed _ _ _ _)
    (fun hu => Bool.false_ne_true ((huni _ hu).1.symm.trans ag))
    (fun hu => Bool.false_ne_true ((huni _ hu).2.symm.trans ah))
  rw [eq] at ag
  exact hdiff _ ⟨ag,ah⟩

end TwoInputs

inductive NodeCertificate where
  | ordinary (program : List Gate)
  | merge (a b : Sig) (g h : TwoInputs.Group)
  | tree (P N : List (Fin 256))
  | step

def supportedOp : GateOp → Bool
  | .and | .or | .not => true
  | _ => false

def goodGate (g : Gate) : Bool := supportedOp g.op && decide (g.inputs.length ≤ 2)

private theorem goodGate_legal (g : Gate) (h : goodGate g=true) :
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  cases g with
  | mk op pins => cases op <;> simp [goodGate,supportedOp] at h ⊢ <;> assumption

def nodeTest (next : Layer) (k t : Nat) (v : List Sig) : NodeCertificate → Bool
  | .ordinary _ => false
  | .merge a b g h => decide (v.Nodup ∧ v.length+t=(k+1)+1) && TwoInputs.twoGroups v a b g h
  | .tree _ _ => false
  | .step => layerNode next k t v

theorem nodeTest_sound {next : Layer} {k t : Nat} {v : List Sig} {c : NodeCertificate}
    (good : next.Valid k) (check : nodeTest next k t v c = true) : Impossible (k+1) t v := by
  cases c with
  | ordinary gs => simp [nodeTest] at check
  | merge a b g h =>
    simp only [nodeTest,Bool.and_eq_true,decide_eq_true_eq] at check
    exact TwoInputs.exclude_conflicting_groups _ _ _ check.1.1 check.1.2 _ _ _ _ check.2
  | tree P N => simp [nodeTest] at check
  | step => exact layerNode_sound good check

def emptyLayer : Layer := ⟨fun _ => 0,fun _ _ => [],fun _ _ => 0⟩
theorem emptyLayer_ok (k : Nat) : emptyLayer.Valid k := fun _ _ h => (Nat.not_lt_zero _ h).elim

namespace CertifiedData
open TwoInputs PEqualNP.CircuitLowerBounds

def words (width : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel+1, z => if z=0 then [] else (z % 2^width) :: words width fuel (z >>> width)

def stored (bits offset packed : Nat) := (packed >>> (bits*offset)) % (2^bits)

def asGate (g : Nat) : Gate :=
  let u := (g >>> 2) % 32
  let v := (g >>> 7) % 32
  if g%4 = 3 then ⟨.not,[u]⟩ else ⟨if g%4=1 then .and else .or,[u,v]⟩

def sampleGroup (rowAt : Nat → Row) (packed : Nat) : Group :=
  let samples := (words 10 4 packed).map fun z =>
    (rowAt ((z-1)/4),Fin.ofNat 4 ((z-1)%4))
  ⟨(samples.head?.map Prod.fst).getD (false,0),samples⟩

def readCert (sig : Nat → Sig) (bits : Nat) (rowAt : Nat → Row) (z : Nat) : NodeCertificate :=
  let tag := z % 4
  let p := z >>> 2
  if tag=0 then .step
  else if tag=1 then .ordinary ((words 12 10 p).map asGate)
  else if tag=2 then
    let a := sig (p % 2^bits)
    let b := sig ((p >>> bits) % 2^bits)
    let groups := p >>> (2*bits)
    .merge a b (sampleGroup rowAt (groups % 2^40)) (sampleGroup rowAt (groups >>> 40))
  else
    let rows := ((List.range 128).filter fun r => p.testBit r).map rowAt
    .tree ((rows.filter fun r => r.1).map Prod.snd) ((rows.filter fun r => !r.1).map Prod.snd)

def seek (keys : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, l, _ => l
  | fuel+1, l, n =>
      if n ≤ 1 then l else
        let half := n/2
        if h < keys (l+half) then seek keys h fuel l half
        else seek keys h fuel (l+half) (n-half)

end CertifiedData

abbrev Hint := Nat → Nat → List Sig → NodeCertificate

def knownAt (L : Layer) (hint : Hint) (k t : Nat) (v : List Sig) : Bool :=
  nodeTest emptyLayer k t v (hint (k+1) t v) || L.matchState t v

private theorem knownAt_sound {L : Layer} {hint : Hint} {k t : Nat} {v : List Sig}
    (valid : L.Valid (k+1)) (check : knownAt L hint k t v=true) : Impossible (k+1) t v := by
  rcases Bool.or_eq_true_iff.mp check with leaf | indexed
  · exact nodeTest_sound (emptyLayer_ok _) leaf
  · exact Layer.checked valid indexed

def internalPass (L : Layer) (hint : Hint) (k t : Nat) (v : List Sig) : Bool :=
  decide v.Nodup && !stepTest (k+1) t v
    (fun w => !knownAt L hint k (t-1) w) (fun w => !knownAt L hint k t w)

theorem internalPass_sound {L : Layer} {hint : Hint} {k t : Nat} {v : List Sig}
    (valid : L.Valid (k+1)) (check : internalPass L hint k t v = true) : Impossible (k+2) t v := by
  simp only [internalPass,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at check
  apply exclude_step check.1 _ _ check.2
  · intro w hw; exact knownAt_sound valid (by simpa using hw)
  · intro w hw; exact knownAt_sound valid (by simpa using hw)

def compactRoot (j : Fin 7) (L : Layer) (hint : Hint) : Bool := (raw j).sublists.all fun ws =>
  (List.range (12-ws.length)).all fun t =>
    if unionSep (decide (0<t)) ws = top then knownAt L hint 9 t ws else true

theorem exclusion_from_compact (j : Fin 7) (L : Layer) (hint : Hint) (hv : L.Valid 10)
    (cert : compactRoot j L hint = true) (C : Circuit) (hs : C.size ≤ 10) (hf : PEqualNP.MetaComplexity.FanInTwo C) :
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
  exact knownAt_sound hv hc k hbudget (heq.symm ▸ unrestricted hl)

def maskCovers (m : Sig) (g : TwoInputs.Group) : Bool :=
  rowValue g.anchor m && g.samples.all fun rc => rowValue rc.1 m

def maskedUniform (m w : Sig) : Bool :=
  let x := w.1 &&& m.1
  let y := w.2 &&& m.2
  ((x == 0) && (y == 0)) || ((x == m.1) && (y == m.2))

private theorem low_bit {w m : B} {r : Fin 256} (masked : w &&& m=0)
    (hit : m.getLsbD r.val=true) : w.getLsbD r.val=false := by
  have h := congrArg (fun x : B => x.getLsbD r.val) masked
  simpa only [BitVec.getLsbD_and,hit,Bool.and_true,BitVec.getLsbD_zero] using h

private theorem high_bit {w m : B} {r : Fin 256} (masked : w &&& m=m)
    (hit : m.getLsbD r.val=true) : w.getLsbD r.val=true := by
  have h := congrArg (fun x : B => x.getLsbD r.val) masked
  simpa only [BitVec.getLsbD_and,hit,Bool.and_true] using h

private theorem uniform_rows {m w : Sig} (h : maskedUniform m w=true) :
    ∃ d : Bool, ∀ r : Row, rowValue r m=true → rowValue r w=d := by
  simp only [maskedUniform,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at h
  rcases h with ⟨x,y⟩ | ⟨x,y⟩
  · refine ⟨false,?_⟩
    rintro ⟨b,i⟩ hit
    cases b
    · exact low_bit y hit
    · exact low_bit x hit
  · refine ⟨true,?_⟩
    rintro ⟨b,i⟩ hit
    cases b
    · exact high_bit y hit
    · exact high_bit x hit

private theorem four_bits_on (i : Fin 4) : (15 : TwoInputs.T).getLsbD i.val=true := by decide +revert

private theorem group_from_mask (g : TwoInputs.Group) (a b m : Sig) (v : List Sig)
    (covers : maskCovers m g=true) (coordinates : g.valid [a,b] a b=true)
    (clean : ∀ w ∈ v, w=a ∨ w=b ∨ maskedUniform m w=true) : g.valid v a b=true := by
  have cv := Bool.and_eq_true_iff.mp covers
  apply List.all_eq_true.mpr
  intro rc hr
  apply List.all_eq_true.mpr
  intro w hw
  have base := List.all_eq_true.mp coordinates rc hr
  rcases clean w hw with rfl | rfl | hh
  · exact List.all_eq_true.mp base _ (by simp)
  · exact List.all_eq_true.mp base _ (by simp)
  by_cases ha : w=a
  · exact List.all_eq_true.mp base _ (by simp [ha])
  by_cases hb : w=b
  · exact List.all_eq_true.mp base _ (by simp [hb])
  obtain ⟨d,hd⟩ := uniform_rows hh
  have h1 := hd g.anchor cv.1
  have h2 := hd rc.1 (List.all_eq_true.mp cv.2 rc hr)
  cases d <;> simp [TwoInputs.inputTable,ha,hb,h1,h2,four_bits_on,rc.2.isLt]

structure FixedPair where
  a : Sig
  b : Sig
  g : TwoInputs.Group
  h : TwoInputs.Group
  gm : Sig
  hm : Sig

def FixedPair.intrinsic (c : FixedPair) : Prop :=
  c.a≠c.b ∧ (∀ z : TwoInputs.T, TwoInputs.unary4 z → c.g.accept z=false ∧ c.h.accept z=false) ∧
    (∀ z : TwoInputs.T, ¬ (c.g.accept z=true ∧ c.h.accept z=true)) ∧
    maskCovers c.gm c.g=true ∧ maskCovers c.hm c.h=true ∧
    c.g.valid [c.a,c.b] c.a c.b=true ∧ c.h.valid [c.a,c.b] c.a c.b=true

instance (c : FixedPair) : Decidable c.intrinsic := by unfold FixedPair.intrinsic; infer_instance

def FixedPair.fits (c : FixedPair) (v : List Sig) :=
  v.all fun w => (maskedUniform c.gm w && maskedUniform c.hm w) || w == c.a || w == c.b

theorem FixedPair.block {c : FixedPair} {k t : Nat} {v : List Sig} (hn : v.Nodup)
    (ht : v.length+t=k+1) (ok : c.intrinsic) (fits : c.fits v=true) : Impossible k t v := by
  obtain ⟨ab,unary,disjoint,cg,ch,ag,ah⟩ := ok
  have both (w : Sig) (hw : w ∈ v) : w=c.a ∨ w=c.b ∨
      (maskedUniform c.gm w=true ∧ maskedUniform c.hm w=true) := by
    have h := List.all_eq_true.mp fits w hw
    simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at h
    tauto
  have vg := group_from_mask c.g c.a c.b c.gm v cg ag (fun w hw => by
    rcases both w hw with x | x | ⟨x,_⟩
    · exact Or.inl x
    · exact Or.inr (Or.inl x)
    · exact Or.inr (Or.inr x))
  have vh := group_from_mask c.h c.a c.b c.hm v ch ah (fun w hw => by
    rcases both w hw with x | x | ⟨_,x⟩
    · exact Or.inl x
    · exact Or.inr (Or.inl x)
    · exact Or.inr (Or.inr x))
  apply TwoInputs.exclude_conflicting_groups k t v hn ht c.a c.b c.g c.h
  unfold TwoInputs.twoGroups
  simp only [decide_eq_true_eq]
  exact ⟨ab,vg,vh,unary,disjoint⟩

structure Book where
  count : Nat
  entry : Nat → FixedPair
  choose : Nat → Nat → List Sig → Nat

def Book.Valid (b : Book) := ∀ i, i < b.count → (b.entry i).intrinsic

def bookKnown (L : Layer) (b : Book) (k t : Nat) (v : List Sig) : Bool :=
  ((v.length+t == k+1) &&
    (let i := b.choose k t v; decide (i < b.count) && (b.entry i).fits v)) || L.matchState t v

private theorem bookKnown_ok {L : Layer} {b : Book} {k t : Nat} {v : List Sig}
    (hl : L.Valid k) (hb : b.Valid) (hn : v.Nodup) (check : bookKnown L b k t v=true) : Impossible k t v := by
  rcases Bool.or_eq_true_iff.mp check with leaf | indexed
  · simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at leaf
    exact FixedPair.block hn leaf.1 (hb _ leaf.2.1) leaf.2.2
  · exact Layer.checked hl indexed

def bookPass (L : Layer) (b : Book) (k t : Nat) (v : List Sig) : Bool :=
  decide v.Nodup && !stepTest k t v (fun w => !bookKnown L b k (t-1) w) (fun w => !bookKnown L b k t w)

theorem bookPass_ok {L : Layer} {b : Book} {k t : Nat} {v : List Sig}
    (hl : L.Valid k) (hb : b.Valid) (check : bookPass L b k t v=true) : Impossible (k+1) t v := by
  simp only [bookPass,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at check
  intro m hm h
  apply Bool.false_ne_true
  apply check.2.symm.trans
  apply reduced_step h hm check.1 rfl
  · intro w hn j hj run
    cases hc : bookKnown L b k (t-1) w
    · rfl
    · exact (bookKnown_ok hl hb hn hc j hj run).elim
  · intro w hn j hj run
    cases hc : bookKnown L b k t w
    · rfl
    · exact (bookKnown_ok hl hb hn hc j hj run).elim

def bookRoot (j : Fin 7) (L : Layer) (b : Book) : Bool := (raw j).sublists.all fun ws =>
  (List.range (12-ws.length)).all fun t =>
    if unionSep (decide (0<t)) ws = top then bookKnown L b 10 t ws else true

theorem exclusion_from_book (j : Fin 7) (L : Layer) (b : Book) (hv : L.Valid 10) (hb : b.Valid)
    (cert : bookRoot j L b = true) (C : Circuit) (hs : C.size ≤ 10) (hf : PEqualNP.MetaComplexity.FanInTwo C) :
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
  exact bookKnown_ok hv hb hn hc k hbudget (heq.symm ▸ unrestricted hl)

end CoThetaWholeBase


namespace CoThetaWholeBase
open PEqualNP.CircuitLowerBounds

def renamePin (f : Fin 7 → Fin 7) (k : Nat) := if h : k < 7 then (f ⟨k,h⟩).val else k

def renameGate (f : Fin 7 → Fin 7) (g : Gate) : Gate := ⟨g.op,g.inputs.map (renamePin f)⟩

def relabeled (f : Fin 7 → Fin 7) (c : Circuit) : Circuit :=
  ⟨c.gates.map (renameGate f),renamePin f c.output⟩

private def rowRun (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun a => v.getD a false)]) w

private lemma rename_run (f : Fin 7 → Fin 7) (gs : List Gate) (v w : List Bool)
    (h7 : 7 ≤ v.length) (hl : v.length = w.length)
    (hv : ∀ k, w.getD (renamePin f k) false = v.getD k false) (k : Nat) :
    (rowRun (gs.map (renameGate f)) w).getD (renamePin f k) false = (rowRun gs v).getD k false := by
  induction gs generalizing v w with
  | nil => exact hv k
  | cons g gs ih =>
    have hgate : (renameGate f g).op.eval ((renameGate f g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      change g.op.eval ((g.inputs.map (renamePin f)).map fun i => w.getD i false) = _
      rw [List.map_map]
      exact congrArg (fun p : Nat → Bool => g.op.eval (g.inputs.map p)) (funext hv)
    change (rowRun (gs.map (renameGate f)) (w ++ [_])).getD _ false = (rowRun gs (v ++ [_])).getD _ false
    rw [hgate]
    apply ih (v ++ [_]) (w ++ [_]) (by simp; omega) (by simp [hl])
    intro i
    by_cases hi : i < v.length
    · have hr : renamePin f i < w.length := by
        unfold renamePin; split
        · have h := (f ⟨i,by assumption⟩).isLt; omega
        · omega
      rw [List.getD_append _ _ _ _ hr,List.getD_append _ _ _ _ hi,hv]
    · have hp : ¬i<7 := by omega
      simp only [renamePin,dif_neg hp,List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega : w.length ≤ i),
        List.getElem?_append_right (by omega : v.length ≤ i), hl]

private lemma read_ofFn {n : Nat} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD,i.isLt]

private lemma initial_rename (f : Fin 7 → Fin 7) (j : Fin 7) (x : Fin 7 → Bool) (k : Nat) :
    (List.ofFn x ++ [!(x (f j))]).getD (renamePin f k) false =
    (List.ofFn (fun i => x (f i)) ++ [!(x (f j))]).getD k false := by
  by_cases h : k<7
  · simp only [renamePin,dif_pos h]
    rw [List.getD_append _ _ _ _ (by simpa using (f ⟨k,h⟩).isLt),
      List.getD_append _ _ _ _ (by simpa using h)]
    exact (read_ofFn x (f ⟨k,h⟩)).trans (read_ofFn (fun i => x (f i)) ⟨k,h⟩).symm
  · simp only [renamePin,dif_neg h,List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h),
      List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)]
    simp

def reverseEnds : Fin 7 → Fin 7 := ![1,0,2,4,3,6,5]
def swapLongPaths : Fin 7 → Fin 7 := ![0,1,2,5,6,3,4]
def toRepresentative : Fin 7 → Fin 7 → Fin 7 :=
  ![id,reverseEnds,id,id,reverseEnds,swapLongPaths,reverseEnds ∘ swapLongPaths]

def orbitHead : Fin 7 → Fin 7 := ![0,0,2,3,3,3,3]

private lemma rep_head : ∀ j : Fin 7, toRepresentative j j = orbitHead j := by decide +kernel
private lemma rep_target (j : Fin 7) (x : Fin 7 → Bool) : theta (fun i => x (toRepresentative j i)) = theta x := by
  have table : ∀ (j : Fin 7) (a b c d e f g : Bool),
      let y : Fin 7 → Bool := ![a,b,c,d,e,f,g]
      theta (fun i => y (toRepresentative j i)) = theta y := by decide +kernel
  have hx : x = ![x 0,x 1,x 2,x 3,x 4,x 5,x 6] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  exact table j (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def NoSignedTail (j : Fin 7) : Prop := ∀ c : Circuit, c.size ≤ 10 →
  PEqualNP.MetaComplexity.FanInTwo c → ¬ ∀ x : Fin 7 → Bool,
    c.eval (List.ofFn x ++ [!(x j)]) = theta x

theorem all_heads_from (r0 : NoSignedTail 0) (r2 : NoSignedTail 2) (r3 : NoSignedTail 3)
    (j : Fin 7) : NoSignedTail j := by
  intro c hsize hfan hag
  let f := toRepresentative j
  have hr : NoSignedTail (f j) := by
    change NoSignedTail (toRepresentative j j)
    rw [rep_head]
    have ids : ∀ i : Fin 7, orbitHead i = 0 ∨ orbitHead i = 2 ∨ orbitHead i = 3 := by decide +kernel
    rcases ids j with h | h | h
    · rw [h]; exact r0
    · rw [h]; exact r2
    · rw [h]; exact r3
  apply hr (relabeled f c) (by simpa [relabeled,Circuit.size] using hsize) ?_
  · intro x
    have hrow := rename_run f c.gates (List.ofFn (fun i => x (f i)) ++ [!(x (f j))])
      (List.ofFn x ++ [!(x (f j))]) (by simp) (by simp) (initial_rename f j x) c.output
    exact hrow.trans ((hag (fun i => x (f i))).trans (rep_target j x))
  · intro g hg
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hg
    simpa [renameGate] using hfan old hold

theorem physical_of_signed_tail (j : Fin 7) (cert : NoSignedTail j) (g : Gate)
    (gs : List Gate) (o : Nat) (hf : PEqualNP.MetaComplexity.FanInTwo ⟨g :: gs,o⟩)
    (hs : (Circuit.mk (g :: gs) o).size ≤ 11)
    (head : ∀ x : Fin 7 → Bool,
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = !(x j)) :
    ¬ ∀ x : Fin 7 → Bool, (Circuit.mk (g :: gs) o).eval (List.ofFn x) = theta x := by
  intro h
  apply cert (Circuit.mk gs o) (by
    change gs.length ≤ 10
    change (g :: gs).length ≤ 11 at hs
    simp only [List.length_cons] at hs
    omega)
    (fun g' hg => hf g' (List.mem_cons_of_mem _ hg))
  intro x
  have he := h x
  change (gs.foldl (fun w g' => w ++ [g'.op.eval (g'.inputs.map fun i => w.getD i false)])
    (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD o false = _ at he
  rw [head x] at he
  exact he

end CoThetaWholeBase
