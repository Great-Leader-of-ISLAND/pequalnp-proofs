import Mathlib
import PEqualNP.Defs
import PEqualNP.CoPaid3143

namespace PEqualNP.Outside.L_meta_4358_aux

namespace CoAO3143
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

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

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
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

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

def bit (side : Bool) (i : Fin 160) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

def gateAvailable (v : List Sig) (g : Sig) : Bool :=
  !(v.contains g) && g != zero && g != one

abbrev Row := Fin 160
end CoAO3143

namespace CoAO3143.ProtocolProof

def separates (p n : Row) (a : Sig) : Prop :=
  bit true p a = true ∧ bit false n a = false

private def child (d : Bool) (a b : Sig) (p n : Row) : Sig :=
  if d then (if bit true p a then a else b) else (if bit false n a then b else a)

theorem width {k t S} (h : Live k t S) : S.card+t ≤ k+1 := by
  induction h with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

end CoAO3143.ProtocolProof

namespace CoAO3143.ProtocolProof

structure Certificate where
  a : Sig
  b : Sig
  p : Row
  q₁ : Row
  q₂ : Row
  n : Row
  m₁ : Row
  m₂ : Row

end CoAO3143.ProtocolProof

namespace CoNum4358

structure Gate where
  isOr : Bool
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

def Gate.phys (g : Gate) : PEqualNP.CircuitLowerBounds.Gate :=
  ⟨if g.isOr then .or else .and, [g.a,g.b]⟩

def Gate.lifted (g : Gate) (marks : Bool × Bool) : PEqualNP.CircuitLowerBounds.Gate :=
  ⟨if g.isOr then .or else .and,
    [if marks.1 then 0 else g.a+1, if marks.2 then 0 else g.b+1]⟩

def Gate.sane (g : Gate) (width : Nat) : Prop :=
  g.a < width ∧ g.b < width ∧ g.a ≠ g.b

def Gate.reads2 (g : Gate) : Bool := g.isOr && [g.a,g.b].contains 2

abbrev Marked := Gate × (Bool × Bool)

def Allowed (s t : Nat) (r : Marked) : Prop :=
  (r.2.1 = true → r.1.a = s ∨ r.1.a = t) ∧
  (r.2.2 = true → r.1.b = s ∨ r.1.b = t)

def op (k x y : Bool) : Bool := if k then x || y else x && y

def Gate.val (g : Gate) (w : List Bool) : Bool :=
  op g.isOr (w.getD g.a false) (w.getD g.b false)

def Marked.val (r : Marked) (w : List Bool) : Bool :=
  op r.1.isOr (r.2.1 || w.getD r.1.a false) (r.2.2 || w.getD r.1.b false)

def ordinary (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.val ws]) w

def raised (ds : List Marked) (w : List Bool) : List Bool :=
  ds.foldl (fun ws d => ws ++ [Marked.val d ws]) w

end CoNum4358

namespace CoNum4358
open PEqualNP.MetaComplexity CoThetaFreeCore CoThetaNine CoThetaPhysical

abbrev PhysGate := PEqualNP.CircuitLowerBounds.Gate
abbrev PhysCircuit := PEqualNP.CircuitLowerBounds.Circuit

def target (x : Fin 7 → Bool) : Bool :=
  ([1,12,4,15,26,35,46,36] : List Nat).any fun e =>
    x (Fin.ofNat 7 (e/10)) && x (Fin.ofNat 7 (e % 10))

def ren : Fin 7 → Fin 7 := ![3,0,2,6,4,5,1]
def raw (i : Fin 7) (r : SmallInput) := raw7 (ren i) r
def input : List (SmallInput → Bool) := List.ofFn raw
def seed : List (SmallInput → Bool) := absentBit :: (fun _ => true) :: input

theorem input_known : ∀ a∈input,a∈seed := by
  intro a ha
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha)

theorem constants (b : Bool) : (fun _ : SmallInput => b)∈seed := by
  cases b
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem seed_norm : ∀ a∈seed,norm (0 : SmallInput) a∈vertices7 := by
  intro a h
  rcases List.mem_cons.mp h with rfl | h
  · exact List.mem_cons_self
  rcases List.mem_cons.mp h with rfl | h
  · exact List.mem_cons_self
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
  have hr : norm (0 : SmallInput) (raw i)=raw7 (ren i) := by
    funext r
    have z : raw7 (ren i) 0=false := by simp [raw7]
    simp [raw,CoThetaFreeCore.norm,CoThetaFreeCore.phase,z]
  rw [hr]
  exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨_,rfl⟩)

theorem normalized {n w} (h : Ordinary seed n w) :
    ∃ ys,Free vertices7 n ys ∧ ∀ a∈w,norm (0 : SmallInput) a∈ys := by
  induction h with
  | start => exact ⟨_,Free.start,seed_norm⟩
  | @inv n ws a pre ha ih =>
    obtain ⟨ys,hys,sub⟩ := ih
    refine ⟨ys,hys,?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | old
    · rw [normalize_unary]
      exact sub a ha
    · exact sub z old
  | @binary n ws a b pre join ha hb ih =>
    obtain ⟨ys,hys,sub⟩ := ih
    have step := Free.binary hys (normalizedKind join (a 0) (b 0)) (sub a ha) (sub b hb)
    refine ⟨_,step,?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | old
    · rw [normalize_binary]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub z old)

private theorem read_map {α : Type} (ws : List (α → Bool)) (i : Nat) (r : α) :
    (ws.map (fun f => f r)).getD i false = ws.getD i absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? <;> rfl

theorem sample_target : ∀ r : SmallInput,target (fun i => raw i r)=ans7 r := by
  decide +kernel

theorem physical_price (lower : SignedLower) (C : PhysCircuit) (fan : FanInTwo C)
    (agrees : ∀ x : Fin 7 → Bool,C.eval (List.ofFn x)=target x) :
    11 ≤ cost (C.gates.map gateForm) := by
  let fs := C.gates.map gateForm
  let ws := execute fs input
  let out := ws.getD C.output absentBit
  have word : out=ans7 := by
    funext r
    have ev := congrArg (fun b : List Bool => b.getD C.output false) (circuit_rows C fan input r)
    change (ws.map (fun f => f r)).getD C.output false=C.eval (input.map (fun f => f r)) at ev
    rw [read_map] at ev
    have h0 : input.map (fun f => f r) = List.ofFn (fun i => raw i r) := by
      simp [input,List.map_ofFn]
    rw [h0] at ev
    exact ev.trans ((agrees _).trans (sample_target r))
  obtain ⟨ys,prog,known⟩ := pins_to_program fs input seed seed 0 Ordinary.start constants input_known
  have member : out∈ys := by
    cases ee : ws[C.output]? with
    | none =>
      have eq : out=absentBit := by simp [out,List.getD_eq_getElem?_getD,ee]
      have nx : ans7 (5 : SmallInput) ≠ absentBit (5 : SmallInput) := by decide +kernel
      exact (nx (congrFun (word.symm.trans eq) _)).elim
    | some a =>
      have eq : out=a := by simp [out,List.getD_eq_getElem?_getD,ee]
      rw [eq]
      exact known a (List.mem_of_getElem? ee)
  obtain ⟨zs,hzs,sub⟩ := normalized prog
  have n0 : norm (0 : SmallInput) ans7=ans7 := by
    have e : ans7 0=false := by decide +kernel
    funext r
    simp [CoThetaFreeCore.norm,CoThetaFreeCore.phase,e]
  have hi := sub out member
  rw [word,n0] at hi
  simpa [fs] using lower hzs hi

private theorem one_charge (gs : List PhysGate)
    (tight : gs.length ≤ cost (gs.map gateForm)) :
    ∀ g∈gs,(gateForm g).binaryCost=1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hlen := pin_cost_length (gs.map gateForm)
    have hgate : (gateForm g).binaryCost≤1 := by cases gateForm g <;> simp [PinForm.binaryCost]
    simp only [List.map_cons,List.length_cons,cost] at tight
    rw [List.length_map] at hlen
    intro x hx
    rcases List.mem_cons.mp hx with rfl | old
    · omega
    · exact ih (by omega) _ old

theorem all_binary (lower : SignedLower) (C : PhysCircuit) (fan : FanInTwo C)
    (size : C.size=11) (agrees : ∀ x : Fin 7 → Bool,C.eval (List.ofFn x)=target x) :
    ∀ g∈C.gates,∃ b : Gate,b.phys=g := by
  have price := physical_price lower C fan agrees
  change C.gates.length=11 at size
  have all := one_charge C.gates (by omega)
  intro g hg
  have charged := all g hg
  have len := (fan g hg).2
  obtain ⟨kind,pins⟩ := g
  change pins.length≤2 at len
  cases pins with
  | nil => cases kind <;> simp [gateForm,PinForm.binaryCost] at charged
  | cons a tail =>
    cases tail with
    | nil => cases kind <;> simp [gateForm,PinForm.binaryCost] at charged
    | cons b tail =>
      cases tail with
      | nil =>
        cases kind <;> simp [gateForm,PinForm.binaryCost] at charged
        · exact ⟨⟨false,a,b⟩,rfl⟩
        · exact ⟨⟨true,a,b⟩,rfl⟩
      | cons u us => simp at len

def Shape (s t : Nat) (g h : PhysGate) : Prop :=
  g.op=h.op ∧ List.Forall₂ (fun a b : Nat => b=a+1 ∨ b=0 ∧ (a=s ∨ a=t)) g.inputs h.inputs

private theorem pin_mark {s t a b : Nat} (h : b=a+1 ∨ b=0 ∧ (a=s ∨ a=t)) :
    ∃ m : Bool,(if m then 0 else a+1)=b ∧ (m=true → a=s ∨ a=t) := by
  rcases h with eq | ⟨eq,allowed⟩
  · exact ⟨false,eq.symm,by simp⟩
  · exact ⟨true,eq.symm,fun _ => allowed⟩

private theorem pair_mark {s t : Nat} (g : Gate) (h : PhysGate) (ok : Shape s t g.phys h) :
    ∃ m : Bool×Bool,g.lifted m=h ∧ Allowed s t (g,m) := by
  obtain ⟨kind,pins⟩ := h
  obtain ⟨hk,hp⟩ := ok
  change g.phys.op=kind at hk
  subst kind
  change List.Forall₂ _ [g.a,g.b] pins at hp
  cases hp with
  | cons ha htail =>
    cases htail with
    | cons hb hend =>
      cases hend
      obtain ⟨ma,ea,wa⟩ := pin_mark ha
      obtain ⟨mb,eb,wb⟩ := pin_mark hb
      exact ⟨(ma,mb),by simp [Gate.lifted,Gate.phys,ea,eb],wa,wb⟩

theorem decode_paired {s t : Nat} {gs hs : List PhysGate}
    (binary : ∀ g∈gs,∃ b : Gate,b.phys=g)
    (matchPins : List.Forall₂ (Shape s t) gs hs) :
    ∃ ps : List Marked,ps.map (fun p => p.1.phys)=gs ∧
      ps.map (fun p => p.1.lifted p.2)=hs ∧ ∀ p∈ps,Allowed s t p := by
  induction matchPins with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | @cons g h gs hs head tail ih =>
    obtain ⟨b,eq⟩ := binary g (by simp)
    obtain ⟨mark,hm,ha⟩ := pair_mark b h (by simpa only [eq] using head)
    obtain ⟨ps,p1,p2,p3⟩ := ih (fun x hx => binary x (List.mem_cons_of_mem _ hx))
    refine ⟨(b,mark)::ps,by simp [eq,p1],by simp [hm,p2],?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | old
    · exact ha
    · exact p3 _ old

private theorem physical_one (g : Gate) (ws : List Bool) :
    g.phys.op.eval (g.phys.inputs.map (fun i => ws.getD i false))=g.val ws := by
  obtain ⟨k,a,b⟩ := g
  cases k <;> simp [Gate.phys,Gate.val,op,PEqualNP.CircuitLowerBounds.GateOp.eval]

private theorem physical_lift (p : Marked) (ws : List Bool) :
    (p.1.lifted p.2).op.eval ((p.1.lifted p.2).inputs.map (fun i =>
      (true::ws).getD i false))=Marked.val p ws := by
  obtain ⟨⟨k,a,b⟩,ma,mb⟩ := p
  cases k <;> cases ma <;> cases mb <;>
    simp [Gate.lifted,Marked.val,op,PEqualNP.CircuitLowerBounds.GateOp.eval,
      List.getD_eq_getElem?_getD]

theorem ordinary_rows (ps : List Marked) (ws : List Bool) :
    (ps.map (fun p => p.1.phys)).foldl (fun w (g : PhysGate) =>
      w++[g.op.eval (g.inputs.map (fun i => w.getD i false))]) ws =
    ordinary (ps.map Prod.fst) ws := by
  induction ps generalizing ws with
  | nil => rfl
  | cons g tail ih =>
    simpa only [List.map_cons,List.foldl_cons,ordinary,physical_one] using
      ih (ws++[g.1.val ws])

theorem raised_rows (ps : List Marked) (ws : List Bool) :
    (ps.map (fun p => p.1.lifted p.2)).foldl (fun w (g : PhysGate) =>
      w++[g.op.eval (g.inputs.map (fun i => w.getD i false))]) (true::ws) =
    true::raised ps ws := by
  induction ps generalizing ws with
  | nil => rfl
  | cons g tail ih =>
    simpa only [List.map_cons,List.foldl_cons,raised,physical_lift,List.cons_append] using
      ih (ws++[Marked.val g ws])

theorem reader_count (ps : List Marked) :
    ((ps.map (fun p => p.1.phys)).filter (fun g =>
      g.op.eval [true,false] && g.inputs.contains 2)).length =
    ((ps.map Prod.fst).filter Gate.reads2).length := by
  induction ps with
  | nil => rfl
  | cons g tail ih =>
    have e : (g.1.phys.op.eval [true,false] && g.1.phys.inputs.contains 2) = g.1.reads2 := by
      obtain ⟨⟨k,a,b⟩,m⟩ := g
      cases k <;> rfl
    simp only [List.map_cons,List.filter_cons,e]
    split <;> simp only [List.length_cons,ih]

end CoNum4358

namespace CoNum4358

def Marked.ordered (r : Marked) : Marked :=
  if r.1.b < r.1.a then (⟨r.1.isOr,r.1.b,r.1.a⟩,(r.2.2,r.2.1)) else r

theorem ordered_le (r : Marked) : (Marked.ordered r).1.a ≤ (Marked.ordered r).1.b := by
  by_cases h : r.1.b < r.1.a
  · simpa only [Marked.ordered,if_pos h] using Nat.le_of_lt h
  · have le : r.1.a ≤ r.1.b := by omega
    simpa only [Marked.ordered,if_neg h] using le

private theorem op_comm (k a b : Bool) : op k a b = op k b a := by
  cases k <;> cases a <;> cases b <;> rfl

theorem ordered_gate (r : Marked) (w : List Bool) :
    (Marked.ordered r).1.val w=r.1.val w := by
  unfold Marked.ordered
  split
  · exact op_comm _ _ _
  · rfl

theorem ordered_mark (r : Marked) (w : List Bool) :
    Marked.val (Marked.ordered r) w=Marked.val r w := by
  unfold Marked.ordered
  split
  · exact op_comm _ _ _
  · rfl

theorem ordered_reader (r : Marked) : (Marked.ordered r).1.reads2=r.1.reads2 := by
  unfold Marked.ordered
  split
  · obtain ⟨⟨k,a,b⟩,m⟩ := r
    simp [Gate.reads2,Bool.or_comm,or_comm]
  · rfl

theorem ordered_ordinary (ps : List Marked) (w : List Bool) :
    ordinary ((ps.map Marked.ordered).map Prod.fst) w=ordinary (ps.map Prod.fst) w := by
  induction ps generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.map_cons,ordinary,List.foldl_cons,ordered_gate] using ih (w++[x.1.val w])

theorem ordered_raised (ps : List Marked) (w : List Bool) :
    raised (ps.map Marked.ordered) w=raised ps w := by
  induction ps generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.map_cons,raised,List.foldl_cons,ordered_mark] using ih (w++[Marked.val x w])

theorem ordered_count (ps : List Marked) :
    (((ps.map Marked.ordered).map Prod.fst).filter Gate.reads2).length =
    ((ps.map Prod.fst).filter Gate.reads2).length := by
  induction ps with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.filter_cons,ordered_reader]
    split <;> simp only [List.length_cons,ih]

end CoNum4358

namespace CoNum4358
open PEqualNP.MetaComplexity CoThetaNine

structure Paired (C D : PhysCircuit) (s t : Nat) where
  slots : List Marked
  original : slots.map (fun p => p.1.phys)=C.gates
  lifted : slots.map (fun p => p.1.lifted p.2)=D.gates
  permitted : ∀ p∈slots,Allowed s t p

theorem extract (lower : SignedLower) (C D : PhysCircuit) (s t : Nat)
    (fan : FanInTwo C) (size : C.size=11) (computes : circuitFun 7 C=target)
    (links : List.Forall₂ (Shape s t) C.gates D.gates) :
    Nonempty (Paired C D s t) := by
  have correct (x : Fin 7 → Bool) : C.eval (List.ofFn x)=target x := congrFun computes x
  obtain ⟨slots,raw,up,allow⟩ := decode_paired (all_binary lower C fan size correct) links
  exact ⟨⟨slots,raw,up,allow⟩⟩

theorem Paired.len {C D s t} (p : Paired C D s t) : p.slots.length=C.size := by
  simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using congrArg List.length p.original

theorem Paired.rawRows {C D s t} (p : Paired C D s t) (xs : List Bool) :
    C.wires xs=ordinary (p.slots.map Prod.fst) xs := by
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires
  rw [←p.original]
  exact ordinary_rows p.slots xs

theorem Paired.upRows {C D s t} (p : Paired C D s t) (xs : List Bool) :
    D.wires (true::xs)=true::raised p.slots xs := by
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires
  rw [←p.lifted]
  exact raised_rows p.slots xs

theorem Paired.readers {C D s t} (p : Paired C D s t) :
    (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length =
      ((p.slots.map Prod.fst).filter Gate.reads2).length := by
  rw [←p.original]
  exact reader_count _

theorem Paired.shifted {C D s t} (p : Paired C D s t) (xs : List Bool) (o : Nat) :
    (D.wires (true::xs)).getD (o+1) false=(raised p.slots xs).getD o false := by
  rw [p.upRows]
  simp [List.getD_eq_getElem?_getD]

namespace Transfer

def liftRow : Fin 6 → Nat := ![1,8,96,66,18,52]
def atRow (r : Nat) (j : Fin 7) : Bool := r.testBit j.val
def sixBit (f : Fin 6 → Bool) : BitVec 6 :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem raised_result (ps : List Marked) (o : Nat)
    (correct : ∀ x : Fin 7 → Bool,(raised ps (List.ofFn x)).getD o false =
      (target x || x 0 || x 3)) :
    sixBit (fun i => (raised ps (List.ofFn (atRow (liftRow i)))).getD o false)=3 := by
  have eq : (fun i => (raised ps (List.ofFn (atRow (liftRow i)))).getD o false) =
      (fun i => let x := atRow (liftRow i); target x || x 0 || x 3) := by
    funext i
    exact correct (atRow (liftRow i))
  rw [eq]
  decide +kernel

theorem from_shifted {C D s t} (p : Paired C D s t)
    (h : ∀ x : Fin 7 → Bool,(D.wires (true::List.ofFn x)).getD (C.output+1) false =
      (target x || x 0 || x 3)) :
    sixBit (fun i =>
      (raised (p.slots.map Marked.ordered) (List.ofFn (atRow (liftRow i)))).getD C.output false)=3 := by
  apply raised_result
  intro x
  rw [ordered_raised,←p.shifted]
  exact h x

end Transfer
end CoNum4358

namespace CoNum4358
open CoAO3143

def rawKW : List CoAO3143.Sig := [
  (0x1fc07f000000001fc07f000000001fc07f,0x264c993264c993264c993264c993264c993264c9),
  (0xfe03fff0000000fe03fff0000000fe03fff,0x8912244891224489122448912244891224489122),
  (0x7f0003f80000007f0003f80000007f0003f80,0x74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d),
  (0x3f800000000fe03f800000000fe03f800000000,0x1c3870e1c3870e1c3870e1c3870e1c3870e1c387),
  (0xfc00001fc00001fc00001fc00001fc00001fc000,0x58b162c58b162c58b162c58b162c58b162c58b16),
  (0x3f80fe000000003f80fe000000003f80fe00000,0x62c58b162c58b162c58b162c58b162c58b162c58),
  (0xfc07f0000000fffc07f0000000fffc07f0000000,0x83060c183060c183060c183060c183060c183060)]

def lookupKW (bank : List Sig) (i : Nat) := bank.getD i zero

def Gate.kw (g : Gate) (bank : List Sig) : Sig :=
  bin g.isOr (lookupKW bank g.a) (lookupKW bank g.b)

def bankKW (bank : List Sig) : List Gate → List Sig
  | [] => bank
  | g::gs => bankKW (bank ++ [g.kw bank]) gs

abbrev LiftVal := BitVec 6
abbrev LiftSet := List LiftVal

def rawLoose : List LiftSet := [[1,63],[24,63],[32,63],[2,63],[48,63],[36,63],[12,63]]
def looseGate (d : Bool) (xs ys : LiftSet) : LiftSet :=
  63 :: (xs.flatMap fun x => ys.map fun y => if d then x ||| y else x &&& y).eraseDups
def Gate.loose (g : Gate) (bank : List LiftSet) : LiftSet :=
  looseGate g.isOr (bank.getD g.a []) (bank.getD g.b [])
def bankLoose (bank : List LiftSet) : List Gate → List LiftSet
  | [] => bank
  | g::gs => bankLoose (bank ++ [g.loose bank]) gs

inductive DirTrail : Nat → List Gate → Finset Nat → Prop
  | done {off : Nat} : DirTrail off [] {off-1}
  | step {off : Nat} {gs : List Gate} {U : Finset Nat} (g : Gate)
      (sane : g.sane off) (fresh : off∉U)
      (tail : DirTrail (off+1) gs (insert off U)) :
      DirTrail off (g::gs) (insert g.a (insert g.b U))

end CoNum4358

namespace CoNum4358.Original
open CoAO3143

def row (s : Bool) (i : Fin 160) (j : Fin 7) :=
  bit s i (lookupKW rawKW j.val)

private theorem raw_list : ∀ (s : Bool) (i : Fin 160),
    List.ofFn (row s i)=rawKW.map (bit s i) := by decide +kernel

private theorem row_target : ∀ (s : Bool) (i : Fin 160),
    CoNum4358.target (row s i)=s := by decide +kernel

private theorem reader (ws : List Sig) (j : Nat) (s : Bool) (i : Fin 160) :
    (ws.map (bit s i)).getD j false = bit s i (lookupKW ws j) := by
  simp only [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[j]? with
  | none => cases s <;> simp [bit,zero]
  | some a => rfl

private theorem bval (g : Gate) (ws : List Sig) (s : Bool) (i : Fin 160) :
    bit s i (g.kw ws) = g.val (ws.map (bit s i)) := by
  simp only [Gate.kw,Gate.val,reader]
  cases s <;> cases h : g.isOr <;> simp [bit,CoAO3143.bin,op,h,BitVec.getLsbD_and,BitVec.getLsbD_or]

private theorem rows (ws : List Sig) (gs : List Gate) (s : Bool) (i : Fin 160) :
    (bankKW ws gs).map (bit s i) = ordinary gs (ws.map (bit s i)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simpa only [bankKW,ordinary,List.foldl_cons,List.map_append,List.map_cons,List.map_nil,bval]
      using ih (ws++[g.kw ws])

theorem hit {C D s t} (p : Paired C D s t)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = CoNum4358.target x) :
    lookupKW (bankKW rawKW ((p.slots.map Marked.ordered).map Prod.fst)) C.output = CoAO3143.target := by
  let gs := ((p.slots.map Marked.ordered).map Prod.fst)
  let w := lookupKW (bankKW rawKW gs) C.output
  have bits (b : Bool) (i : Fin 160) : bit b i w = b := by
    change bit b i (lookupKW (bankKW rawKW gs) C.output) = b
    rw [←reader,rows,←raw_list]
    dsimp only [gs]
    rw [ordered_ordinary,←p.rawRows]
    exact (computes (row b i)).trans (row_target b i)
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h := bits true ⟨j,hj⟩
    change w.1.getLsbD j = true at h
    change w.1.getLsbD j = (BitVec.allOnes 160).getLsbD j
    rw [BitVec.getLsbD_allOnes]
    simpa only [hj,decide_true] using h
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h := bits false ⟨j,hj⟩
    simpa [w,gs,bit,CoAO3143.target] using h

end CoNum4358.Original

namespace CoNum4358.Transfer

abbrev SixWire := Fin 6 → Bool

theorem sixBit_bit (f : SixWire) (i : Nat) (hi : i < 6) :
    (sixBit f).getLsbD i = f ⟨i,hi⟩ := by
  rw [sixBit,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  have h : i < (List.ofFn f).length := by simpa only [List.length_ofFn] using hi
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

theorem sixBit_op (d : Bool) (a b : SixWire) :
    sixBit (fun i => op d (a i) (b i))=
      (if d then sixBit a ||| sixBit b else sixBit a &&& sixBit b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  cases d <;> simp only [op,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,
    BitVec.getLsbD_or,sixBit_bit _ _ hj]

def sixRaw : List SixWire := List.ofFn (fun (j : Fin 7) (i : Fin 6) => atRow (liftRow i) j)
def zeroWire : SixWire := fun _ => false

def sixGate (p : Marked) (ws : List SixWire) : SixWire := fun i =>
  op p.1.isOr (p.2.1 || ws.getD p.1.a zeroWire i) (p.2.2 || ws.getD p.1.b zeroWire i)

def sixRun : List Marked → List SixWire → List SixWire
  | [],ws => ws
  | p::ps,ws => sixRun ps (ws++[sixGate p ws])

private theorem atIndex (ws : List SixWire) (a : Nat) (i : Fin 6) :
    (ws.map (fun f => f i)).getD a false = ws.getD a zeroWire i := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[a]? <;> rfl

theorem mapSix (ps : List Marked) (ws : List SixWire) (i : Fin 6) :
    (sixRun ps ws).map (fun f => f i) = raised ps (ws.map (fun f => f i)) := by
  induction ps generalizing ws with
  | nil => rfl
  | cons p ps ih =>
    have localEq : sixGate p ws i=Marked.val p (ws.map (fun f => f i)) := by
      unfold sixGate Marked.val
      rw [atIndex,atIndex]
    simpa only [sixRun,raised,List.foldl_cons,List.map_append,List.map_cons,List.map_nil,localEq]
      using ih (ws++[sixGate p ws])

def Captures (ws : List SixWire) (sets : List LiftSet) : Prop :=
  List.Forall₂ (fun f s => sixBit f∈s ∧ (63 : LiftVal)∈s) ws sets

private theorem initial : Captures sixRaw rawLoose := by
  unfold Captures
  refine (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)))))))
  all_goals decide +kernel

private theorem capture_read {ws sets} (h : Captures ws sets) (j : Nat) (hj : j<sets.length) :
    sixBit (ws.getD j zeroWire)∈sets.getD j [] ∧ (63 : LiftVal)∈sets.getD j [] := by
  induction h generalizing j with
  | nil => simp at hj
  | cons first rest ih =>
    cases j with
    | zero => exact first
    | succ j => exact ih j (by simpa using hj)

private theorem capture_push {ws sets f s} (h : Captures ws sets)
    (a : sixBit f∈s ∧ (63 : LiftVal)∈s) : Captures (ws++[f]) (sets++[s]) := by
  induction h with
  | nil => exact List.Forall₂.cons a List.Forall₂.nil
  | cons first _ ih => exact List.Forall₂.cons first ih

private theorem capture_force (v : SixWire) (m : Bool) (s : LiftSet)
    (h : sixBit v∈s ∧ (63 : LiftVal)∈s) : sixBit (fun i => m || v i)∈s := by
  cases m
  · simpa using h.1
  · have one : sixBit (fun _ => true)=63 := by decide +kernel
    simpa [one] using h.2

private theorem loose_member (d : Bool) {xs ys : LiftSet} {x y : LiftVal}
    (hx : x∈xs) (hy : y∈ys) : (if d then x ||| y else x &&& y)∈looseGate d xs ys := by
  apply List.mem_cons_of_mem
  have h : (if d then x ||| y else x &&& y) ∈
      xs.flatMap (fun x => ys.map fun y => if d then x ||| y else x &&& y) :=
    List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨y,hy,rfl⟩⟩
  simpa using h

private theorem capture_gate {ws sets} (h : Captures ws sets) (r : Marked)
    (ok : r.1.sane sets.length) :
    sixBit (sixGate r ws)∈r.1.loose sets ∧ (63 : LiftVal)∈r.1.loose sets := by
  refine ⟨?_,List.mem_cons_self⟩
  unfold sixGate
  rw [sixBit_op]
  exact loose_member _ (capture_force _ _ _ (capture_read h _ ok.1))
    (capture_force _ _ _ (capture_read h _ ok.2.1))

theorem capture_run (ps : List Marked) {ws sets} (start : Captures ws sets)
    {S} (trace : DirTrail sets.length (ps.map Prod.fst) S) :
    Captures (sixRun ps ws) (bankLoose sets (ps.map Prod.fst)) := by
  induction ps generalizing ws sets S with
  | nil => exact start
  | cons p ps ih =>
    cases trace with
    | step _ sane _ tail =>
      apply ih (capture_push start (capture_gate start p sane))
      simpa using tail

theorem loose_length (gs : List Gate) (bank : List LiftSet) :
    (bankLoose bank gs).length=bank.length+gs.length := by
  induction gs generalizing bank with
  | nil => simp [bankLoose]
  | cons g gs ih => simp [bankLoose,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem six_mem (ps : List Marked) {S : Finset Nat} {o : Nat}
    (trace : DirTrail 7 (ps.map Prod.fst) S) (bound : o < 7+ps.length) :
    sixBit (fun i => (raised ps (List.ofFn (atRow (liftRow i)))).getD o false) ∈
      (bankLoose rawLoose (ps.map Prod.fst)).getD o [] := by
  have h := capture_run ps initial trace
  have size : o < (bankLoose rawLoose (ps.map Prod.fst)).length := by
    simpa [loose_length,rawLoose] using bound
  have mem := (capture_read h o size).1
  have e : (sixRun ps sixRaw).getD o zeroWire =
      (fun i => (raised ps (List.ofFn (atRow (liftRow i)))).getD o false) := by
    funext i
    rw [←atIndex,mapSix]
    simp [sixRaw,List.map_ofFn]
  rw [e] at mem
  exact mem

theorem three_mem {C D s t} (p : Paired C D s t) {S}
    (trace : DirTrail 7 ((p.slots.map Marked.ordered).map Prod.fst) S)
    (bound : C.output < 7+p.slots.length)
    (agree : ∀ x : Fin 7 → Bool,(D.wires (true::List.ofFn x)).getD (C.output+1) false =
      (target x || x 0 || x 3)) :
    (3 : LiftVal)∈(bankLoose rawLoose ((p.slots.map Marked.ordered).map Prod.fst)).getD C.output [] := by
  have v := six_mem (p.slots.map Marked.ordered) trace (by simpa only [List.length_map] using bound)
  rwa [from_shifted p agree] at v

end CoNum4358.Transfer

namespace CoNum4358
open CoAO3143

def OK (xs : List Sig) (a : Sig) := a = zero ∨ a = one ∨ a ∈ xs

inductive Run (roots : List Sig) : Nat → List Sig → Prop
  | start : Run roots 0 roots
  | add {k bank a b} (pre : Run roots k bank) (d : Bool)
      (ha : OK bank a) (hb : OK bank b) :
      Run roots (k+1) (bin d a b :: bank)

def Price (xs : List Sig) (n : Nat) := ∀ k ys, Run xs k ys → OK ys CoAO3143.target → n ≤ k

private theorem old {ws : List Sig} {w : Sig} (a : Sig) (hw : OK ws w) : OK (a::ws) w := by
  rcases hw with eq|eq|mem
  · exact Or.inl eq
  · exact Or.inr (Or.inl eq)
  · exact Or.inr (Or.inr (List.mem_cons_of_mem _ mem))

private theorem from_mem {as bs : List Sig} (h : ∀ x ∈ as, OK bs x) :
    ∀ x, OK as x → OK bs x := by
  intro x hx
  rcases hx with eq|eq|mem
  · exact Or.inl eq
  · exact Or.inr (Or.inl eq)
  · exact h x mem

theorem lookup_ok (ws : List Sig) (i : Nat) : OK ws (lookupKW ws i) := by
  simp only [lookupKW,List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact Or.inl rfl
  | some w => exact Or.inr (Or.inr (List.mem_of_getElem? e))

private theorem lookup_append_eq (ws : List Sig) (w : Sig) :
    lookupKW (ws++[w]) ws.length = w := by
  simp [lookupKW,List.getD_eq_getElem?_getD]

private theorem lookup_append_ne (ws : List Sig) (w : Sig) (i : Nat) (ne : i ≠ ws.length) :
    lookupKW (ws++[w]) i = lookupKW ws i := by
  by_cases less : i < ws.length
  · simp [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_append,less]
  · have gt : ws.length + 1 ≤ i := by omega
    have past : (ws++[w]).length ≤ i := by simpa using gt
    simp [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_eq_none past,
      List.getElem?_eq_none (Nat.le_of_not_gt less)]

theorem continue_run {roots xs : List Sig} {k} (pre : Run roots k xs)
    (ws : List Sig) (known : ∀ x ∈ ws, OK xs x) (gs : List Gate) :
    ∃ ys, Run roots (k+gs.length) ys ∧ ∀ x ∈ bankKW ws gs, OK ys x := by
  induction gs generalizing xs ws k with
  | nil => exact ⟨xs,by simpa using pre,known⟩
  | cons g gs ih =>
    have a := from_mem known _ (lookup_ok ws g.a)
    have b := from_mem known _ (lookup_ok ws g.b)
    have run := Run.add pre g.isOr a b
    change Run roots (k+1) (g.kw ws::xs) at run
    have all (x) (hx : x ∈ ws++[g.kw ws]) : OK (g.kw ws::xs) x := by
      rcases List.mem_append.mp hx with before|last
      · exact old _ (known _ before)
      · exact Or.inr (Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp last))))
    obtain ⟨ys,h,mem⟩ := ih run (ws++[g.kw ws]) all
    have e : (k+1)+gs.length = k+(g::gs).length := by simp only [List.length_cons]; omega
    exact ⟨ys,e ▸ h,mem⟩

theorem replay {ws xs : List Sig} {k} (run : Run ws k xs) {roots base : List Sig} {n}
    (pre : Run roots n base) (known : ∀ x ∈ ws, OK base x) :
    ∃ ys, Run roots (n+k) ys ∧ ∀ x ∈ xs, OK ys x := by
  induction run with
  | start => exact ⟨_,by simpa using pre,known⟩
  | add _ d ha hb ih =>
    obtain ⟨ys,r,mem⟩ := ih
    refine ⟨_,by simpa only [Nat.add_assoc] using Run.add r d (from_mem mem _ ha) (from_mem mem _ hb),?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with eq|m
    · exact Or.inr (Or.inr (List.mem_cons.mpr (Or.inl eq)))
    · exact old _ (mem _ m)

theorem tail_price {ws : List Sig} {n : Nat} (p : Price ws (n+1)) (g : Gate) :
    Price (ws++[g.kw ws]) n := by
  intro k ys r out
  have base : Run ws 1 (g.kw ws::ws) :=
    Run.add Run.start g.isOr (lookup_ok ws g.a) (lookup_ok ws g.b)
  have known (x) (hx : x∈ws++[g.kw ws]) : OK (g.kw ws::ws) x := by
    rcases List.mem_append.mp hx with m|e
    · exact Or.inr (Or.inr (List.mem_cons_of_mem _ m))
    · exact Or.inr (Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp e))))
  obtain ⟨zs,c,sub⟩ := replay r base known
  have := p _ zs c (from_mem sub _ out)
  omega

theorem fresh_gate {ws : List Sig} {g : Gate} {gs : List Gate} {out : Nat}
    (low : Price ws (gs.length+1)) (hit : lookupKW (bankKW (ws++[g.kw ws]) gs) out=CoAO3143.target) :
    ¬ OK ws (g.kw ws) := by
  intro bad
  have known (x) (hx : x∈ws++[g.kw ws]) : OK ws x := by
    rcases List.mem_append.mp hx with m|e
    · exact Or.inr (Or.inr m)
    · exact (List.mem_singleton.mp e) ▸ bad
  obtain ⟨ys,r,mem⟩ := continue_run (roots:=ws) Run.start _ known gs
  have h := from_mem mem _ (lookup_ok _ out)
  rw [hit] at h
  have := low _ ys r h
  omega

def need (off out : Nat) : List Gate → Finset Nat
  | [] => {out}
  | g::gs =>
    let T := need (off+1) out gs
    if off∈T then insert g.a (insert g.b (T.erase off)) else T

def liveCount (off out : Nat) : List Gate → Nat
  | [] => 0
  | _::gs => liveCount (off+1) out gs + if off∈need (off+1) out gs then 1 else 0

theorem count_le (off out : Nat) (gs : List Gate) : liveCount off out gs ≤ gs.length := by
  induction gs generalizing off with
  | nil => simp [liveCount]
  | cons g gs ih =>
    have h := ih (off+1)
    simp only [liveCount,List.length_cons]
    split <;> omega

theorem cone_run {roots xs : List Sig} {k} (pre : Run roots k xs)
    (ws : List Sig) (gs : List Gate) (out : Nat)
    (known : ∀ i ∈ need ws.length out gs, OK xs (lookupKW ws i)) :
    ∃ ys, Run roots (k+liveCount ws.length out gs) ys ∧
      OK ys (lookupKW (bankKW ws gs) out) := by
  induction gs generalizing ws xs k with
  | nil => exact ⟨_,by simpa [liveCount] using pre,known _ (by simp [need])⟩
  | cons g gs ih =>
    let next := ws++[g.kw ws]
    have len : next.length = ws.length+1 := by simp [next]
    by_cases used : ws.length∈(need (ws.length+1) out gs)
    · have hknown : ∀ i ∈ insert g.a (insert g.b ((need (ws.length+1) out gs).erase ws.length)), OK xs (lookupKW ws i) := by
        simpa only [need,if_pos used] using known
      have a := hknown g.a (Finset.mem_insert_self _ _)
      have b := hknown g.b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have r : Run roots (k+1) (g.kw ws::xs) := Run.add pre g.isOr a b
      have keep (i) (hi : i∈need next.length out gs) : OK (g.kw ws::xs) (lookupKW next i) := by
        rw [len] at hi
        by_cases e : i=ws.length
        · subst i
          rw [show lookupKW next ws.length = g.kw ws from lookup_append_eq _ _]
          exact Or.inr (Or.inr List.mem_cons_self)
        · rw [show lookupKW next i = lookupKW ws i from lookup_append_ne _ _ i e]
          exact old _ (hknown _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e,hi⟩))))
      obtain ⟨ys,rr,h⟩ := ih r next keep
      rw [len] at rr
      refine ⟨ys,?_,h⟩
      convert rr using 1 <;> simp only [liveCount,if_pos used] <;> omega
    · have keep (i) (hi : i∈need next.length out gs) : OK xs (lookupKW next i) := by
        rw [len] at hi
        have e : i≠ws.length := fun eq => used (eq ▸ hi)
        rw [show lookupKW next i = lookupKW ws i from lookup_append_ne _ _ i e]
        apply known
        simpa only [need,if_neg used] using hi
      obtain ⟨ys,rr,h⟩ := ih pre next keep
      rw [len] at rr
      refine ⟨ys,?_,h⟩
      simpa only [liveCount,if_neg used,Nat.add_zero] using rr

theorem no_dead {ws : List Sig} {gs : List Gate} {out : Nat} (p : Price ws gs.length)
    (hit : lookupKW (bankKW ws gs) out = CoAO3143.target) : liveCount ws.length out gs = gs.length := by
  obtain ⟨ys,r,h⟩ := cone_run (roots:=ws) Run.start ws gs out (fun i _ => lookup_ok ws i)
  rw [hit] at h
  have := p _ ys r h
  have := count_le ws.length out gs
  omega

end CoNum4358

namespace CoNum4358.KWPrice
open CoAO3143 CoThetaFreeCore CoThetaNine

def pRow : Fin 8 → SmallInput := ![9,5,24,33,6,96,18,66]
def nRow : Fin 7 → SmallInput := ![76,81,84,44,52,3,42]
def below (r s : SmallInput) : Prop := ∀ j : Fin 7, raw7 j r = true → raw7 j s = true
local instance (r s : SmallInput) : Decidable (below r s) := by unfold below; infer_instance
def rising (f : SmallInput → Bool) := ∀ r s, below r s → f r = true → f s = true

def fits (w : Sig) (f : SmallInput → Bool) : Prop :=
  (∀ p : Fin 8, f (pRow p) = w.1.getLsbD (7*p.val)) ∧
  (∀ n : Fin 7, f (nRow n) = w.2.getLsbD n.val)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem boundary : ∀ r : SmallInput,
    (ans7 r = true → ∃ p : Fin 8, below (pRow p) r) ∧
    (ans7 r = false → ∃ n : Fin 7, below r (nRow n)) := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem unique (f : SmallInput → Bool) (hf : rising f) (eq : fits CoAO3143.target f) :
    f = ans7 := by
  funext r
  obtain ⟨pos,neg⟩ := boundary r
  cases h : ans7 r with
  | true =>
    obtain ⟨p,le⟩ := pos h
    have i : 7*p.val < 160 := by have := p.isLt; omega
    have on := eq.1 p
    change f (pRow p) = (BitVec.allOnes 160).getLsbD (7 * p.val) at on
    simp only [BitVec.getLsbD_allOnes,i,decide_true] at on
    exact hf _ _ le on
  | false =>
    obtain ⟨n,le⟩ := neg h
    have off := eq.2 n
    simp [CoAO3143.target] at off
    cases val : f r with
    | false => rfl
    | true => exact Bool.noConfusion ((hf _ _ le val).symm.trans off)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem rise_op (b : Bool) (f g : SmallInput → Bool) (hf : rising f) (hg : rising g) :
    rising (fun i => base b (f i) (g i)) := by
  intro r s le h
  have x := hf r s le
  have y := hg r s le
  cases e₁ : f r <;> cases e₂ : f s <;> cases e₃ : g r <;> cases e₄ : g s <;>
    cases b <;> simp_all [base]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem fit_op (b : Bool) {u v : Sig} {f g : SmallInput → Bool} (hf : fits u f)
    (hg : fits v g) : fits (bin b u v) (fun i => base b (f i) (g i)) := by
  constructor
  · intro i
    cases b <;> simp only [base,bin,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_or,
      BitVec.getLsbD_and,hf.1 i,hg.1 i]
  · intro i
    cases b <;> simp only [base,bin,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_or,
      BitVec.getLsbD_and,hf.2 i,hg.2 i]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
def model (fs : List (SmallInput → Bool)) (w : Sig) :=
  ∃ f∈fs, rising f ∧ fits w f

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem keep {fs f w} (h : model fs w) : model (f::fs) w := by
  obtain ⟨g,hg,r,e⟩ := h
  exact ⟨g,List.mem_cons_of_mem _ hg,r,e⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem cfit : fits zero (fun _ => false) ∧ fits one (fun _ => true) := by
  unfold fits
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem inputs : ∀ i : Fin 7, fits (rawKW.getD i.val zero) (raw i) := by
  unfold fits
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem reflect_run {k ws} (r : Run rawKW k ws) :
    ∃ fs, Ordinary seed k fs ∧ ∀ w, OK ws w → model fs w := by
  induction r with
  | start =>
    refine ⟨seed,Ordinary.start,?_⟩
    intro w hw
    rcases hw with rfl|rfl|m
    · exact ⟨_,constants false,fun _ _ _ => id,cfit.1⟩
    · exact ⟨_,constants true,fun _ _ _ => id,cfit.2⟩
    · obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp m
      have lim : i<7 := by simpa only [show rawKW.length=7 by decide] using hi
      let j : Fin 7 := ⟨i,lim⟩
      have e : rawKW.getD j.val zero = w := by
        change rawKW.getD i zero=w
        simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using eq
      exact ⟨raw j,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨j,rfl⟩)),
        fun x y le h => le (ren j) h, e ▸ inputs j⟩
  | @add k bank a b pre d ha hb ih =>
    obtain ⟨fs,prog,lookup⟩ := ih
    obtain ⟨f,mf,rf,ef⟩ := lookup _ ha
    obtain ⟨g,mg,rg,eg⟩ := lookup _ hb
    refine ⟨_,Ordinary.binary prog d mf mg,?_⟩
    intro w hw
    rcases hw with eq|eq|m
    · exact keep (lookup _ (Or.inl eq))
    · exact keep (lookup _ (Or.inr (Or.inl eq)))
    · rcases List.mem_cons.mp m with rfl|old
      · exact ⟨_,List.mem_cons_self,rise_op _ _ _ rf rg,fit_op _ ef eg⟩
      · exact keep (lookup _ (Or.inr (Or.inr old)))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem lower (price : SignedLower) : Price rawKW 11 := by
  intro k ws run goal
  obtain ⟨fs,prog,lookup⟩ := reflect_run run
  obtain ⟨f,m,r,e⟩ := lookup _ goal
  have eq := unique f r e
  obtain ⟨zs,hz,all⟩ := normalized prog
  have mem := all _ m
  rw [eq] at mem
  have z : norm (0 : SmallInput) ans7=ans7 := by
    have b : ans7 0=false := by decide +kernel
    funext u
    simp [CoThetaFreeCore.norm,phase,b]
  rw [z] at mem
  exact price hz mem

end CoNum4358.KWPrice

namespace CoNum4358
open CoAO3143

private theorem zero_l (d : Bool) (w : Sig) : bin d zero w = zero ∨ bin d zero w=w := by
  rcases w with ⟨x,y⟩
  cases d <;> simp [CoAO3143.bin,zero]
private theorem zero_r (d : Bool) (w : Sig) : bin d w zero = zero ∨ bin d w zero=w := by
  rcases w with ⟨x,y⟩
  cases d <;> simp [CoAO3143.bin,zero]
private theorem idem (d : Bool) (w : Sig) : bin d w w = w := by
  rcases w with ⟨x,y⟩
  cases d <;> simp [CoAO3143.bin]

private theorem bad_read (ws : List Sig) (i : Nat) (bad : Nat.le ws.length i) :
    lookupKW ws i = zero := by
  simp [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_eq_none bad]

theorem sane_of_fresh {ws : List Sig} {g : Gate} (fresh : ¬OK ws (g.kw ws)) :
    g.sane ws.length := by
  constructor
  · by_contra! h
    rcases zero_l g.isOr (lookupKW ws g.b) with e|e
    · exact fresh (Or.inl (by simpa only [Gate.kw,bad_read ws g.a h] using e))
    · have eq : g.kw ws = lookupKW ws g.b := by simpa only [Gate.kw,bad_read ws g.a h] using e
      exact fresh (eq ▸ lookup_ok ws g.b)
  constructor
  · by_contra! h
    rcases zero_r g.isOr (lookupKW ws g.a) with e|e
    · exact fresh (Or.inl (by simpa only [Gate.kw,bad_read ws g.b h] using e))
    · have eq : g.kw ws = lookupKW ws g.a := by simpa only [Gate.kw,bad_read ws g.b h] using e
      exact fresh (eq ▸ lookup_ok ws g.a)
  · intro same
    have eq : g.kw ws = lookupKW ws g.b := by simp only [Gate.kw,same,idem]
    exact fresh (eq ▸ lookup_ok ws g.b)

def Clean (ws : List Sig) : List Gate → Prop
  | [] => True
  | g::gs => g.sane ws.length ∧ ¬OK ws (g.kw ws) ∧ Clean (ws++[g.kw ws]) gs

theorem all_clean {ws : List Sig} {gs : List Gate} {out : Nat}
    (p : Price ws gs.length) (hit : lookupKW (bankKW ws gs) out=CoAO3143.target) :
    Clean ws gs := by
  induction gs generalizing ws with
  | nil => trivial
  | cons g gs ih =>
    have f := fresh_gate p hit
    exact ⟨sane_of_fresh f,f,ih (tail_price p g) hit⟩

private theorem count_cons {off out : Nat} {g : Gate} {gs : List Gate}
    (h : liveCount off out (g::gs)=(g::gs).length) :
    off∈need (off+1) out gs ∧ liveCount (off+1) out gs=gs.length := by
  have le := count_le (off+1) out gs
  simp only [liveCount,List.length_cons] at h
  split at h <;> rename_i e
  · exact ⟨e,by omega⟩
  · omega

theorem last_output (off out : Nat) (g : Gate) (gs : List Gate)
    (all : liveCount off out (g::gs)=(g::gs).length) : out=off+gs.length := by
  induction gs generalizing off g with
  | nil =>
    have m := (count_cons all).1
    simpa only [need,Finset.mem_singleton,List.length_nil,Nat.add_zero,eq_comm] using m
  | cons u us ih =>
    have e := ih (off+1) u (count_cons all).2
    simp only [List.length_cons]
    omega

theorem to_trail (ws : List Sig) (gs : List Gate) (out : Nat)
    (valid : Clean ws gs) (live : liveCount ws.length out gs=gs.length)
    (last : out=ws.length+gs.length-1) : DirTrail ws.length gs (need ws.length out gs) := by
  induction gs generalizing ws with
  | nil =>
    have e : out=ws.length-1 := by simpa using last
    simpa only [need,e] using (DirTrail.done (off:=ws.length))
  | cons g gs ih =>
    have used : ws.length∈(need (ws.length+1) out gs) := (count_cons live).1
    have len : (ws++[g.kw ws]).length=ws.length+1 := by simp
    have tail := ih (ws++[g.kw ws]) valid.2.2 (by rw [len]; exact (count_cons live).2)
      (by rw [len]; change out=ws.length+(g::gs).length-1 at last; simp only [List.length_cons] at last; omega)
    rw [len] at tail
    change DirTrail (ws.length+1) gs (need (ws.length+1) out gs) at tail
    have split : insert ws.length ((need (ws.length+1) out gs).erase ws.length)=(need (ws.length+1) out gs) := Finset.insert_erase used
    have tr := DirTrail.step (U:=(need (ws.length+1) out gs).erase ws.length) g valid.1 (Finset.notMem_erase _ _) (split.symm ▸ tail)
    simpa only [need,if_pos used] using tr

theorem need_bounded (ws : List Sig) (gs : List Gate) (out : Nat) (valid : Clean ws gs)
    (cap : out<ws.length+gs.length) : ∀ i∈need ws.length out gs, i<ws.length := by
  induction gs generalizing ws with
  | nil => simpa [need] using cap
  | cons g gs ih =>
    have len : (ws++[g.kw ws]).length=ws.length+1 := by simp
    have b := ih (ws++[g.kw ws]) valid.2.2 (by rw [len]; simp only [List.length_cons] at cap; omega)
    rw [len] at b
    intro i h
    simp only [need] at h
    split at h <;> rename_i use
    · simp only [Finset.mem_insert,Finset.mem_erase] at h
      rcases h with rfl|rfl|⟨ne,m⟩
      · exact valid.1.1
      · exact valid.1.2.1
      · have := b _ m; omega
    · have := b _ h
      have ne : i≠ws.length := fun eq => use (eq ▸ h)
      omega

end CoNum4358

namespace CoAO3143.Memo
end CoAO3143.Memo

namespace CoNum4358
open CoAO3143

def project (bk : List Sig) (S : Finset Nat) : Finset Sig := S.image (lookupKW bk)

def charge (g : Gate) : Nat := if g.isOr && (g.a == 2 || g.b == 2) then 1 else 0

inductive Walk : Nat → Nat → List Sig → List LiftSet → Finset Nat → Prop
  | done (q : Nat) (bk : List Sig) (bs : List LiftSet) (i : Nat)
      (orig : lookupKW bk i = CoAO3143.target) (raised : (3 : LiftVal) ∈ bs.getD i []) :
      Walk 0 q bk bs {i}
  | step {k q : Nat} {bk : List Sig} {bs : List LiftSet} {U : Finset Nat}
      (g : Gate) (sorted : g.a < g.b) (budget : charge g ≤ q)
      (fresh : gateAvailable bk (g.kw bk) = true)
      (live : Live (k+1) 0 (project bk (insert g.a (insert g.b U))))
      (child : Walk k (q-charge g) (bk ++ [g.kw bk]) (bs ++ [g.loose bs]) (insert bk.length U)) :
      Walk (k+1) q bk bs (insert g.a (insert g.b U))

end CoNum4358

namespace CoNum4358.Routes
open CoAO3143

theorem trail_bounded {off gs S} (t : DirTrail off gs S) (pos : 0<off) :
    ∀ i∈S, i<off := by
  induction t with
  | done => simp only [Finset.mem_singleton]; intro i eq; omega
  | @step off gs U g sane notIn tail ih =>
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|h
    · exact sane.1
    rcases Finset.mem_insert.mp h with rfl|h
    · exact sane.2.1
    have b := ih (by omega) i (Finset.mem_insert_of_mem h)
    have ne : i ≠ off := fun eq => notIn (eq ▸ h)
    omega

private theorem at_pin {bk : List Sig} {i : Nat} (hi : i < bk.length) :
    lookupKW bk i ∈ bk := by
  simp only [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

private theorem before {bk : List Sig} {i : Nat} (hi : i < bk.length) (z : Sig) :
    lookupKW (bk++[z]) i=lookupKW bk i := by
  simp [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_append,hi]

private theorem after (bk : List Sig) (z : Sig) : lookupKW (bk++[z]) bk.length=z := by
  simp [lookupKW,List.getD_eq_getElem?_getD]

private theorem projected {bk : List Sig} {off : Nat} {U : Finset Nat}
    (len : bk.length=off) (bound : ∀ i∈U, i<off) (z : Sig) :
    project (bk++[z]) (insert off U) = insert z (project bk U) := by
  subst off
  unfold project
  rw [Finset.image_insert,after]
  congr 1
  exact Finset.image_congr fun i hi => before (bound i hi) z

private theorem projected_old (bk : List Sig) (g : Gate) (U : Finset Nat) :
    project bk (insert g.a (insert g.b U)) =
      insert (lookupKW bk g.a) (insert (lookupKW bk g.b) (project bk U)) := by
  simp [project,Finset.image_insert]

theorem extract {off gs S} (trace : DirTrail off gs S) (pos : 0<off)
    (bk : List Sig) (bs : List LiftSet) (q : Nat)
    (len : bk.length=off) (regular : ∀ w∈bk,proper w)
    (clean : Clean bk gs) (ordered : ∀ g∈gs,g.a≤g.b)
    (limit : (gs.map charge).sum≤q)
    (hit : lookupKW (bankKW bk gs) (off+gs.length-1)=CoAO3143.target)
    (lifted : (3 : LiftVal)∈(bankLoose bs gs).getD (off+gs.length-1) []) :
    Live gs.length 0 (project bk S) ∧ Walk gs.length q bk bs S := by
  induction trace generalizing bk bs q with
  | @done off =>
    have yes : lookupKW bk (off-1) = CoAO3143.target := by simpa [bankKW] using hit
    have mem : (3 : LiftVal)∈bs.getD (off-1) [] := by simpa [bankLoose] using lifted
    exact ⟨by simpa [project,yes] using (Live.stop),Walk.done q bk bs (off-1) yes mem⟩
  | @step off gs U g sane noff tail ih =>
    let next := bk++[g.kw bk]
    have cap : next.length=off+1 := by simp [next,len]
    have fresh := clean.2.1
    have pr : proper (g.kw bk) := ⟨fun h => fresh (Or.inl h),fun h => fresh (Or.inr (Or.inl h))⟩
    have nonmember : g.kw bk∉bk := fun h => fresh (Or.inr (Or.inr h))
    have good (w) (h : w∈next) : proper w := by
      rcases List.mem_append.mp h with m|e
      · exact regular _ m
      · exact List.mem_singleton.mp e ▸ pr
    have eq : off+1+gs.length-1 = off+(g::gs).length-1 := by simp only [List.length_cons]; omega
    have cost : charge g + (gs.map charge).sum≤q := by simpa only [List.map_cons,List.sum_cons] using limit
    obtain ⟨small,walk⟩ := ih (by omega) next (bs++[g.loose bs]) (q-charge g) cap good clean.2.2
      (fun t h => ordered t (List.mem_cons_of_mem _ h)) (by omega) (eq.symm ▸ hit) (eq.symm ▸ lifted)
    have earlier (i) (hi : i∈U) : i<off := by
      have h := trail_bounded tail (by omega) i (Finset.mem_insert_of_mem hi)
      have n : i≠off := fun eq => noff (eq ▸ hi)
      omega
    have s : project next (insert off U) = insert (g.kw bk) (project bk U) := projected len earlier _
    rw [s] at small
    have ma := at_pin (bk:=bk) (i:=g.a) (len ▸ sane.1)
    have mb := at_pin (bk:=bk) (i:=g.b) (len ▸ sane.2.1)
    have diff : lookupKW bk g.a ≠ lookupKW bk g.b := by
      intro same
      have z : g.kw bk = lookupKW bk g.b := by
        dsimp [Gate.kw]
        rw [same]
        rcases lookupKW bk g.b with ⟨x,y⟩
        cases g.isOr <;> simp [CoAO3143.bin]
      exact nonmember (z ▸ mb)
    have unused : g.kw bk ∉ insert (lookupKW bk g.a) (insert (lookupKW bk g.b) (project bk U)) := by
      intro m
      rcases Finset.mem_insert.mp m with e|m
      · exact nonmember (e ▸ ma)
      rcases Finset.mem_insert.mp m with e|m
      · exact nonmember (e ▸ mb)
      obtain ⟨i,hi,e⟩ := Finset.mem_image.mp m
      exact nonmember (e ▸ at_pin (bk:=bk) (len ▸ earlier _ hi))
    have live : Live (g::gs).length 0 (project bk (insert g.a (insert g.b U))) := by
      rw [projected_old]
      exact Live.binary (regular _ ma) (regular _ mb) diff unused small
    have ga : gateAvailable bk (g.kw bk)=true := by simp [gateAvailable,nonmember,pr.1,pr.2]
    have order := ordered g List.mem_cons_self
    have w : Walk (gs.length+1) q bk bs (insert g.a (insert g.b U)) :=
      Walk.step g (by have := sane.2.2; omega) (by omega) ga live (by simpa only [len] using walk)
    exact ⟨live,w⟩

end CoNum4358.Routes

namespace CoNum4358.Routes
open CoAO3143

private theorem only_full : ∀ xs∈(List.range 7).sublists,
    unionSep false (xs.map (lookupKW rawKW)) = top → xs=List.range 7 := by
  decide +kernel

theorem all_inputs {S : Finset Nat} (bound : S⊆Finset.range 7)
    (h : Live 11 0 (project rawKW S)) : S=Finset.range 7 := by
  classical
  let xs := (List.range 7).filter fun i => i∈S
  have members : xs.toFinset=S := by
    ext i
    simp only [xs,List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact ⟨And.right,fun hi => ⟨Finset.mem_range.mp (bound hi),hi⟩⟩
  have eq : (xs.map (lookupKW rawKW)).toFinset=project rawKW S := by
    rw [←members]
    ext w
    simp [project]
  have cov : unionSep false (xs.map (lookupKW rawKW))=top := live_cover h eq
  have sub : xs ∈ (List.range 7).sublists := List.mem_sublists.mpr (List.filter_sublist)
  have full := only_full xs sub cov
  rw [←members,full]
  decide +kernel

end CoNum4358.Routes

namespace CoNum4358
open CoAO3143

private theorem reading (g : Gate) : g.reads2 = (g.isOr && (g.a==2 || g.b==2)) := by
  rcases g with ⟨d,a,b⟩
  by_cases ha : a=2
  · subst a
    simp [Gate.reads2,List.contains_cons]
  · have hA : 2≠a := Ne.symm ha
    by_cases hb : b=2
    · subst b
      simp [Gate.reads2,List.contains_cons,ha,hA]
    · have hB : 2≠b := Ne.symm hb
      simp [Gate.reads2,List.contains_cons,ha,hA,hb,hB]

private theorem cost_count (gs : List Gate) :
    (gs.map charge).sum=(gs.filter Gate.reads2).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases r : g.reads2 <;> simp [charge,←reading g,r,ih,Nat.add_comm]

private theorem raw_good : ∀ w ∈ rawKW, proper w := by
  intro w hw
  have all : rawKW.all (fun x => decide (x ≠ zero ∧ x ≠ one))=true := by decide +kernel
  change w≠zero ∧ w≠one
  exact of_decide_eq_true (List.all_eq_true.mp all w hw)

private theorem output_of_count (off out : Nat) (gs : List Gate)
    (positive : 0<gs.length) (count : liveCount off out gs=gs.length) :
    out=off+gs.length-1 := by
  cases gs with
  | nil => exact (Nat.not_lt_zero _ positive).elim
  | cons u us =>
    have last := last_output off out u us count
    simp only [List.length_cons]
    omega

private theorem raw_length : rawKW.length=7 := by decide

private theorem ordered_slots (ps : List Marked) :
    ∀ g ∈ (ps.map Marked.ordered).map Prod.fst, g.a≤g.b := by
  intro g hg
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hg
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hr
  exact ordered_le t

theorem exclusion (signed : CoThetaNine.SignedLower)
    (checked : ¬Walk 11 1 rawKW rawLoose (Finset.range 7))
    (C D : PhysCircuit) (a b : Nat) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (size : C.size=11) (agrees : PEqualNP.MetaComplexity.circuitFun 7 C = CoNum4358.target)
    (links : List.Forall₂ (Shape a b) C.gates D.gates)
    (promote : ∀ x : Fin 7 → Bool, (D.wires (true::List.ofFn x)).getD (C.output+1) false =
      (CoNum4358.target x || x 0 || x 3)) :
    (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length ≥ 2 := by
  classical
  by_contra! small
  obtain ⟨p⟩ := extract signed C D a b fan size agrees links
  let gs := (p.slots.map Marked.ordered).map Prod.fst
  have len : gs.length=11 := by simpa [gs] using p.len.trans size
  have rawlen := raw_length
  have low : Price rawKW gs.length := by rw [len]; exact KWPrice.lower signed
  have hit : lookupKW (bankKW rawKW gs) C.output=CoAO3143.target := Original.hit p (fun x => congrFun agrees x)
  have tidy := all_clean low hit
  have count := no_dead low hit
  have positive : 0<gs.length := len.symm ▸ (by decide : 0<11)
  have last := output_of_count rawKW.length C.output gs positive count
  have trail := to_trail _ _ _ tidy count last
  have bound : C.output<7+p.slots.length := by rw [p.len,size]; omega
  have raised := Transfer.three_mem p (rawlen ▸ trail) bound promote
  have sorted : ∀ g∈gs,g.a≤g.b := ordered_slots p.slots
  have budget : (gs.map charge).sum≤1 := by
    rw [cost_count]
    change (((p.slots.map Marked.ordered).map Prod.fst).filter Gate.reads2).length≤1
    rw [ordered_count,←p.readers]
    omega
  obtain ⟨live,w⟩ := Routes.extract trail (by omega) rawKW rawLoose 1 rfl raw_good tidy sorted budget
    (by rw [←last]; exact hit) (by rw [←last]; exact raised)
  have cap : C.output<rawKW.length+gs.length := by omega
  have subset : need rawKW.length C.output gs ⊆ Finset.range 7 := by
    intro i hi
    apply Finset.mem_range.mpr
    exact rawlen ▸ need_bounded _ _ _ tidy cap i hi
  rw [len] at live w
  have all := Routes.all_inputs subset live
  exact checked (all ▸ w)

end CoNum4358

namespace CoNum4358
open CoAO3143

structure Flag where
  original : Bool
  separates : Bool
  deriving DecidableEq, Repr, Inhabited

def mergeFlag (d : Bool) (a b : Flag) : Flag :=
  if d then
    let no := a.original || b.original
    ⟨no,(a.separates || b.separates) && !no⟩
  else ⟨a.original && b.original,a.separates || b.separates⟩

abbrev PairFlag := Flag × Flag

def mergePair (d : Bool) (a b : PairFlag) : PairFlag :=
  (mergeFlag d a.1 b.1,mergeFlag d a.2 b.2)

def rawFlag (v : Nat) (p n : Nat) : Flag := ⟨n.testBit v,p.testBit v && !(n.testBit v)⟩
def rawPair : List PairFlag :=
  (List.range 7).map fun i => (rawFlag i 1 96,rawFlag i 8 18)

def represents (f : Flag) (p n : Bool) : Prop :=
  (f.original=true → n=true) ∧ (p=true → n=false → f.separates=true)

private theorem rep_top (f : Flag) : represents f true true := by simp [represents]

private theorem rep_merge (d : Bool) (a b : Flag) (ap an bp bn : Bool)
    (ha : represents a ap an) (hb : represents b bp bn) :
    represents (mergeFlag d a b) (if d then ap||bp else ap&&bp)
      (if d then an||bn else an&&bn) := by
  obtain ⟨ao,ac⟩ := a
  obtain ⟨bo,bc⟩ := b
  cases d <;> simp only [represents,mergeFlag,Bool.false_eq_true,↓reduceIte] at *
  all_goals cases an <;> cases bn <;> cases ao <;> cases bo <;> simp_all <;> tauto

def governs (t : PairFlag) (v : LiftVal) : Prop :=
  represents t.1 (v.getLsbD 0) (v.getLsbD 2) ∧
  represents t.2 (v.getLsbD 1) (v.getLsbD 4)

def governsSet (t : PairFlag) (vs : LiftSet) : Prop := ∀ v∈vs, governs t v

theorem governs_gate {a b : PairFlag} {xs ys : LiftSet}
    (ha : governsSet a xs) (hb : governsSet b ys) (d : Bool) :
    governsSet (mergePair d a b) (looseGate d xs ys) := by
  intro v hv
  rcases List.mem_cons.mp hv with h | mem
  · subst v
    exact ⟨rep_top _,rep_top _⟩
  · simp only [List.mem_eraseDups,List.mem_flatMap,List.mem_map] at mem
    obtain ⟨x,hx,y,hy,rfl⟩ := mem
    have ax := ha x hx
    have bys := hb y hy
    have p := rep_merge d a.1 b.1 _ _ _ _ ax.1 bys.1
    have q := rep_merge d a.2 b.2 _ _ _ _ ax.2 bys.2
    cases d <;> simpa [governs,mergePair,BitVec.getLsbD_or,BitVec.getLsbD_and] using And.intro p q

abbrev Tracks := List.Forall₂ governsSet

theorem Tracks.lookup {ts vs} (h : Tracks ts vs) (i : Nat) :
    governsSet (ts.getD i default) (vs.getD i []) := by
  induction h generalizing i with
  | nil => simp [governsSet]
  | cons h _ ih =>
    cases i with
    | zero => exact h
    | succ i => exact ih i

def Gate.pair (g : Gate) (ts : List PairFlag) : PairFlag :=
  mergePair g.isOr (ts.getD g.a default) (ts.getD g.b default)

private theorem tracks_snoc {ts vs} (h : Tracks ts vs) {a v} (ok : governsSet a v) :
    Tracks (ts++[a]) (vs++[v]) := by
  induction h with
  | nil => exact .cons ok .nil
  | cons hv _ ih => exact .cons hv ih

theorem Tracks.gate {ts vs} (h : Tracks ts vs) (g : Gate) :
    Tracks (ts++[g.pair ts]) (vs++[g.loose vs]) :=
  tracks_snoc h (governs_gate (h.lookup g.a) (h.lookup g.b) g.isOr)

theorem raw_tracks : Tracks rawPair rawLoose := by
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))))
  all_goals
    intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl <;> unfold governs represents <;> decide +kernel

def capability (side : Bool) (t : PairFlag) : Bool :=
  if side then t.1.separates else t.2.separates

private theorem merge_origin (side d : Bool) (a b : PairFlag)
    (h : capability side (mergePair d a b)=true) :
    capability side a=true ∨ capability side b=true := by
  cases side <;> cases d <;> simp [capability,mergePair,mergeFlag] at * <;> tauto

private theorem lastGet {α : Type} (xs : List α) (v d : α) (i : Nat) :
    (xs++[v]).getD i d = if i=xs.length then v else xs.getD i d := by
  induction xs generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ i => simp
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

theorem live_capability {k q bk bs S} (w : Walk k q bk bs S) (side : Bool)
    (ts : List PairFlag) (ht : Tracks ts bs) (hs : ts.length=bk.length) :
    ∃ i∈S, capability side (ts.getD i default)=true := by
  induction w generalizing ts with
  | done q bk bs i orig raised =>
    have pair := ht.lookup i 3 raised
    refine ⟨i,Finset.mem_singleton_self _,?_⟩
    cases side
    · exact pair.2.2 rfl rfl
    · exact pair.1.2 rfl rfl
  | @step k q bk bs U g sorted budget fresh live child ih =>
    obtain ⟨i,mem,cap⟩ := ih _ (ht.gate g) (by simp [hs])
    rw [lastGet,hs] at cap
    by_cases eqi : i=bk.length
    · rw [if_pos eqi] at cap
      rcases merge_origin side g.isOr _ _ cap with a | b
      · exact ⟨g.a,by simp,a⟩
      · exact ⟨g.b,by simp,b⟩
    · rw [if_neg eqi] at cap
      exact ⟨i,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        ((Finset.mem_insert.mp mem).resolve_left eqi)),cap⟩

end CoNum4358

namespace CoNum4358
open CoAO3143

abbrev AugWire := Sig × PairFlag

def augGate (d : Bool) (a b : AugWire) : AugWire :=
  (bin d a.1 b.1,mergePair d a.2 b.2)

def twoKW : Sig := lookupKW rawKW 2

def augPay (d : Bool) (a b : AugWire) : Nat :=
  if d && (a.1 == twoKW || b.1 == twoKW) then 1 else 0

structure Local (k : Nat) (S : Finset AugWire) : Prop where
  live : Live k 0 (S.image Prod.fst)
  caps : ∀ s : Bool, ∃ w∈S, capability s w.2=true

inductive Shadow : Nat → Nat → Finset AugWire → Prop
  | done (q : Nat) (w : AugWire) (orig : w.1=CoAO3143.target)
      (sep₀ : w.2.1.separates=true) (sep₃ : w.2.2.separates=true) : Shadow 0 q {w}
  | step {k q : Nat} {U : Finset AugWire} (d : Bool) (a b : AugWire)
      (apart : a≠b) (budget : augPay d a b≤q)
      (clean : proper (augGate d a b).1)
      (unused : (augGate d a b).1∉(insert a (insert b U)).image Prod.fst)
      (raw : (augGate d a b).1∉rawKW)
      (localFacts : Local (k+1) (insert a (insert b U)))
      (child : Shadow k (q-augPay d a b) (insert (augGate d a b) U)) :
      Shadow (k+1) q (insert a (insert b U))

def augRoots : List AugWire := rawKW.zip rawPair

end CoNum4358

namespace CoNum4358
open CoAO3143

def augAt (bk : List Sig) (ts : List PairFlag) (i : Nat) : AugWire :=
  (lookupKW bk i,ts.getD i default)

def augProject (bk : List Sig) (ts : List PairFlag) (S : Finset Nat) : Finset AugWire :=
  S.image (augAt bk ts)

private theorem first_image (bk : List Sig) (ts : List PairFlag) (S : Finset Nat) :
    (augProject bk ts S).image Prod.fst=project bk S := by
  simp [augProject,project,augAt,Finset.image_image,Function.comp_def]

private theorem first_mem {k S bk} (live : Live k 0 (project bk S)) {i : Nat} (hi : i∈S) :
    i<bk.length := by
  by_contra! h
  have pr := live_proper live (lookupKW bk i) (Finset.mem_image_of_mem (lookupKW bk) hi)
  have e : lookupKW bk i=zero := by
    simp [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_eq_none h]
  exact pr.1 e

private theorem read_in {bk : List Sig} {i : Nat} (hi : i<bk.length) : lookupKW bk i∈bk := by
  simp only [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

private theorem read_snoc {α : Type} (xs : List α) (v d : α) (i : Nat) :
    (xs++[v]).getD i d = if i=xs.length then v else xs.getD i d := by
  induction xs generalizing i with
  | nil => cases i <;> simp
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ j => simpa using ih j

structure HasRootTags (bk : List Sig) : Prop where
  present : ∀ a∈rawKW,a∈bk
  long : 2<bk.length
  label : ∀ i, i<bk.length → (lookupKW bk i=twoKW ↔ i=2)

private theorem initialTags : HasRootTags rawKW := by
  refine ⟨fun _ h => h,by decide +kernel,?_⟩
  intro i hi
  have test : ∀ j : Fin 7, lookupKW rawKW j.val=twoKW ↔ j.val=2 := by decide +kernel
  exact test ⟨i,hi⟩

private theorem extend_tags {bk : List Sig} (roots : HasRootTags bk) {z : Sig} (fresh : z∉bk) :
    HasRootTags (bk++[z]) := by
  refine ⟨fun a h => List.mem_append_left _ (roots.present a h),by
    simp only [List.length_append,List.length_cons,List.length_nil]
    have := roots.long
    omega,?_⟩
  have zne : z≠twoKW := by
    intro eq
    exact fresh (eq ▸ roots.present twoKW (by decide +kernel))
  intro i hi
  change ((bk++[z]).getD i zero=twoKW ↔ i=2)
  rw [read_snoc]
  by_cases e : i=bk.length
  · rw [if_pos e]
    have neq : i≠2 := by have := roots.long; omega
    simp [zne,neq]
  · rw [if_neg e]
    have lt : i<bk.length := by simp only [List.length_append,List.length_cons,List.length_nil] at hi; omega
    exact roots.label i lt

private theorem tag_bool {bk : List Sig} (roots : HasRootTags bk) {i : Nat} (hi : i<bk.length) :
    (lookupKW bk i==twoKW)=(i==2) := by
  by_cases e : lookupKW bk i=twoKW
  · have eq := (roots.label i hi).mp e
    subst i
    simp [e]
  · have ne : i≠2 := fun h => e ((roots.label i hi).mpr h)
    simp [e,ne]

private theorem project_inputs (bk : List Sig) (ts : List PairFlag) (g : Gate) (U : Finset Nat) :
    augProject bk ts (insert g.a (insert g.b U))=
      insert (augAt bk ts g.a) (insert (augAt bk ts g.b) (augProject bk ts U)) := by
  simp [augProject]

private theorem project_next (bk : List Sig) (ts : List PairFlag) (g : Gate) (U : Finset Nat)
    (len : ts.length=bk.length) (bound : ∀ i∈U,i<bk.length) :
    augProject (bk++[g.kw bk]) (ts++[g.pair ts]) (insert bk.length U) =
      insert (augGate g.isOr (augAt bk ts g.a) (augAt bk ts g.b)) (augProject bk ts U) := by
  unfold augProject
  rw [Finset.image_insert]
  have top : augAt (bk++[g.kw bk]) (ts++[g.pair ts]) bk.length =
      augGate g.isOr (augAt bk ts g.a) (augAt bk ts g.b) := by
    simp [augAt,augGate,Gate.kw,Gate.pair,lookupKW,read_snoc,len]
  rw [top]
  congr 1
  apply Finset.image_congr
  intro i hi
  have hb := bound i hi
  have ht : i<ts.length := by simpa only [len] using hb
  simp only [augAt,lookupKW,List.getD_eq_getElem?_getD,
    List.getElem?_append_left hb,List.getElem?_append_left ht]

theorem shadow_of_walk {k q bk bs S} (walk : Walk k q bk bs S) (ts : List PairFlag)
    (tracks : Tracks ts bs) (len : ts.length=bk.length) (roots : HasRootTags bk) :
    Shadow k q (augProject bk ts S) := by
  induction walk generalizing ts with
  | done q bk bs i orig raised =>
    have pair := tracks.lookup i 3 raised
    have h := Shadow.done q (augAt bk ts i) orig (pair.1.2 rfl rfl) (pair.2.2 rfl rfl)
    simpa [augProject] using h
  | @step k q bk bs U g sorted budget fresh live child ih =>
    let S := insert g.a (insert g.b U)
    have pin (i) (hi : i∈S) : i<bk.length := first_mem live hi
    have ha := pin g.a (by simp [S])
    have hb := pin g.b (by simp [S])
    have ub (i) (hi : i∈U) : i<bk.length := pin _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi))
    have old : g.kw bk∉bk := by
      intro h
      simp [gateAvailable,h] at fresh
    have properZ : proper (g.kw bk) := by
      constructor <;> intro h <;> simp [gateAvailable,h] at fresh
    have apart : augAt bk ts g.a ≠ augAt bk ts g.b := by
      intro eq
      have same : lookupKW bk g.a=lookupKW bk g.b := congrArg Prod.fst eq
      have zz : g.kw bk=lookupKW bk g.b := by
        unfold Gate.kw
        rw [same]
        rcases lookupKW bk g.b with ⟨x,y⟩
        cases g.isOr <;> simp [bin]
      exact old (zz ▸ read_in hb)
    have pay : augPay g.isOr (augAt bk ts g.a) (augAt bk ts g.b)=charge g := by
      simp only [augPay,augAt,tag_bool roots ha,tag_bool roots hb,charge]
    have lf : Local (k+1) (augProject bk ts S) := by
      constructor
      · rw [first_image]
        exact live
      · intro d
        obtain ⟨i,hi,can⟩ := live_capability (Walk.step g sorted budget fresh live child) d ts tracks len
        exact ⟨augAt bk ts i,Finset.mem_image_of_mem _ hi,can⟩
    have absent : (augGate g.isOr (augAt bk ts g.a) (augAt bk ts g.b)).1 ∉
        (augProject bk ts S).image Prod.fst := by
      rw [first_image]
      intro mem
      obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp mem
      change lookupKW bk i=g.kw bk at eq
      apply old
      rw [←eq]
      exact read_in (pin i hi)
    have newRaw : (augGate g.isOr (augAt bk ts g.a) (augAt bk ts g.b)).1 ∉ rawKW :=
      fun hm => old (roots.present _ hm)
    have next := ih (ts++[g.pair ts]) (tracks.gate g) (by simp [len]) (extend_tags roots old)
    rw [project_next bk ts g U len ub,←pay] at next
    change Local (k+1) (augProject bk ts (insert g.a (insert g.b U))) at lf
    rw [project_inputs] at lf
    change (augGate g.isOr (augAt bk ts g.a) (augAt bk ts g.b)).1 ∉
      (augProject bk ts (insert g.a (insert g.b U))).image Prod.fst at absent
    rw [project_inputs] at absent
    rw [project_inputs]
    exact Shadow.step _ _ _ apart (pay ▸ budget) properZ absent newRaw lf next

theorem shadow_root (walk : Walk 11 1 rawKW rawLoose (Finset.range 7)) :
    Shadow 11 1 augRoots.toFinset := by
  have eq : augProject rawKW rawPair (Finset.range 7)=augRoots.toFinset := by decide +kernel
  rw [←eq]
  exact shadow_of_walk walk rawPair raw_tracks (by decide +kernel) initialTags

end CoNum4358

namespace CoNum4358.Tiny
open CoAO3143

abbrev K := BitVec 15
abbrev W := K × PairFlag

def pack (f : Fin 160 → Bool) : B :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem pack_bit (f : Fin 160 → Bool) (i : Nat) (hi : i<160) :
    (pack f).getLsbD i = f ⟨i,hi⟩ := by
  rw [pack,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  have h : i<(List.ofFn f).length := by simpa only [List.length_ofFn] using hi
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

def wide (w : K) : Sig :=
  (pack fun i => w.getLsbD (i.val % 56/7), pack fun i => w.getLsbD (8+i.val % 7))

def lift (w : W) : AugWire := (wide w.1,w.2)

def pos (i : Fin 8) : Row := ⟨i.val*7,by omega⟩
def negRow (i : Fin 7) : Row := ⟨i.val,by omega⟩

theorem pos_bit (w : K) (i : Fin 8) : bit true (pos i) (wide w)=w.getLsbD i.val := by
  change (pack _).getLsbD (i.val*7)=_
  rw [pack_bit _ _ (by omega)]
  have sm : i.val*7<56 := by omega
  have P : (i.val*7) % 56/7=i.val := by rw [Nat.mod_eq_of_lt sm]; omega
  exact congrArg (fun n => w.getLsbD n) P

theorem neg_bit (w : K) (i : Fin 7) : bit false (negRow i) (wide w)=w.getLsbD (8+i.val) := by
  change (pack _).getLsbD i.val=_
  rw [pack_bit _ _ (by omega)]
  simp [Nat.mod_eq_of_lt i.isLt]

theorem wide_inj : Function.Injective wide := by
  intro u v eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i<8
  · let j : Fin 8 := ⟨i,h⟩
    simpa only [pos_bit] using congrArg (bit true (pos j)) eq
  · let j : Fin 7 := ⟨i-8,by omega⟩
    have e := congrArg (bit false (negRow j)) eq
    rw [neg_bit,neg_bit] at e
    have val : 8+j.val=i := by dsimp [j]; omega
    rwa [val] at e

theorem lift_inj : Function.Injective lift := by
  intro x y eq
  exact Prod.ext (wide_inj (congrArg Prod.fst eq)) (congrArg (fun w : AugWire => w.2) eq)

def makeKW (d : Bool) (a b : K) : K := if d then a|||b else a&&&b

theorem wide_bin (d : Bool) (a b : K) : wide (makeKW d a b)=bin d (wide a) (wide b) := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;> cases d <;>
    simp only [wide,makeKW,bin,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_or,
      BitVec.getLsbD_and,pack_bit _ _ hj]

def make (d : Bool) (a b : W) : W := (makeKW d a.1 b.1,mergePair d a.2 b.2)

theorem lift_make (d : Bool) (a b : W) : lift (make d a b)=augGate d (lift a) (lift b) :=
  Prod.ext (wide_bin d a.1 b.1) rfl

def bare : List K := [18693,8715,7442,1952,5700,22568,24784]
def roots : List W := bare.zip rawPair
theorem bare_ground : bare.map wide=rawKW := by decide +kernel
theorem ground : roots.map lift=augRoots := by decide +kernel
theorem middle : wide 7442=twoKW := by decide +kernel
theorem zero_value : wide 0=zero := by decide +kernel
theorem one_value : wide 32767=CoAO3143.one := by decide +kernel
theorem target_value : wide 255=CoAO3143.target := by decide +kernel

def pay (d : Bool) (a b : W) := if d && (a.1==7442 || b.1==7442) then 1 else 0

theorem charge_eq (d : Bool) (a b : W) : pay d a b=augPay d (lift a) (lift b) := by
  have one (v : K) : (wide v==twoKW)=(v==7442) := by
    by_cases eq : v=7442
    · subst v; rw [middle]; simp
    · have neq : wide v≠twoKW := fun e => eq (wide_inj (e.trans middle.symm))
      rw [show (wide v==twoKW)=false from Bool.eq_false_iff.mpr (fun h => neq (beq_iff_eq.mp h)),
        show (v==7442)=false from Bool.eq_false_iff.mpr (fun h => eq (beq_iff_eq.mp h))]
  simp only [pay,augPay,lift,one]

end CoNum4358.Tiny

namespace CoNum4358.Tiny
open CoAO3143

structure Good (k : Nat) (S : Finset W) : Prop where
  live : Live k 0 (S.image fun w => wide w.1)
  caps : ∀ s : Bool, ∃ w∈S, capability s w.2=true

inductive Trace : Nat → Nat → Finset W → Prop
  | done (q : Nat) (w : W) (orig : w.1=255) (sep₀ : w.2.1.separates=true)
      (sep₃ : w.2.2.separates=true) : Trace 0 q {w}
  | step {k q : Nat} {U : Finset W} (d : Bool) (a b : W) (apart : a≠b)
      (budget : pay d a b≤q) (clean : (make d a b).1≠0 ∧ (make d a b).1≠32767)
      (unused : (make d a b).1∉(insert a (insert b U)).image Prod.fst)
      (raw : (make d a b).1∉bare)
      (facts : Good (k+1) (insert a (insert b U)))
      (child : Trace k (q-pay d a b) (insert (make d a b) U)) :
      Trace (k+1) q (insert a (insert b U))

end CoNum4358.Tiny

namespace CoNum4358.Tiny
open CoAO3143

private noncomputable def preimageWire (z : AugWire) : W := by
  classical
  exact if h : ∃ w : W, lift w=z then h.choose else default

private theorem preimage_lift (w : W) : preimageWire (lift w)=w := by
  classical
  unfold preimageWire
  have hw : ∃ v : W, lift v=lift w := ⟨w,rfl⟩
  rw [dif_pos hw]
  exact lift_inj (Classical.choose_spec hw)

private theorem lift_preimage {z : AugWire} (hz : ∃ w : W,lift w=z) :
    lift (preimageWire z)=z := by
  obtain ⟨w,rfl⟩ := hz
  rw [preimage_lift]

private theorem original_fringe {S : Finset AugWire}
    (rep : ∀ z∈S,∃ w : W,lift w=z) :
    (S.image preimageWire).image (fun w => wide w.1) = S.image Prod.fst := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro z hz
  exact congrArg (fun z : AugWire => z.1) (lift_preimage (rep z hz))

private theorem small_good {k S} (fact : Local k S)
    (rep : ∀ z∈S,∃ w : W,lift w=z) : Good k (S.image preimageWire) := by
  constructor
  · rw [original_fringe rep]
    exact fact.live
  · intro s
    obtain ⟨z,hz,flag⟩ := fact.caps s
    refine ⟨preimageWire z,Finset.mem_image_of_mem _ hz,?_⟩
    have bits : (preimageWire z).2 = z.2 := congrArg (fun z : AugWire => z.2) (lift_preimage (rep z hz))
    rwa [bits]

private theorem trace_of_shadow {k q S} (run : Shadow k q S) :
    (∀ z∈S,∃ w : W,lift w=z) → Trace k q (S.image preimageWire) := by
  classical
  induction run with
  | done q z orig sep₀ sep₃ =>
    intro rep
    obtain ⟨x,rfl⟩ := rep z (by simp)
    rw [Finset.image_singleton,preimage_lift]
    exact Trace.done q x (wide_inj (orig.trans target_value.symm)) sep₀ sep₃
  | @step k q U d a b apart bd clean unused noraw facts child ih =>
    intro rep
    obtain ⟨x,rfl⟩ := rep a (by simp)
    obtain ⟨y,rfl⟩ := rep b (by simp)
    have related := lift_make d x y
    have computed : wide (make d x y).1=(augGate d (lift x) (lift y)).1 :=
      congrArg (fun z : AugWire => z.1) related
    have next := ih (by
      intro z hz
      rcases Finset.mem_insert.mp hz with eq | mem
      · exact ⟨make d x y,related.trans eq.symm⟩
      · exact rep z (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem)))
    rw [Finset.image_insert,←related,preimage_lift,←charge_eq] at next
    have localSmall := small_good facts rep
    simp only [Finset.image_insert,preimage_lift] at localSmall ⊢
    apply Trace.step d x y (fun h => apart (congrArg lift h))
      (by simpa only [charge_eq] using bd) _ _ _ localSmall next
    · constructor
      · intro e
        exact clean.1 (computed.symm.trans ((congrArg wide e).trans zero_value))
      · intro e
        exact clean.2 (computed.symm.trans ((congrArg wide e).trans one_value))
    · intro bad
      obtain ⟨v,hv,he⟩ := Finset.mem_image.mp bad
      have inMap : v∈(insert (lift x) (insert (lift y) U)).image preimageWire := by
        simpa only [Finset.image_insert,preimage_lift] using hv
      obtain ⟨z,hz,eq⟩ := Finset.mem_image.mp inMap
      have e : wide (preimageWire z).1=z.1 := congrArg (fun z : AugWire => z.1) (lift_preimage (rep z hz))
      rw [eq,he] at e
      exact unused (Finset.mem_image.mpr ⟨z,hz,e.symm.trans computed⟩)
    · intro bad
      have mem : wide (make d x y).1∈bare.map wide := List.mem_map.mpr ⟨_,bad,rfl⟩
      rw [bare_ground,computed] at mem
      exact noraw mem

theorem shadow_to_tiny (run : Shadow 11 1 augRoots.toFinset) :
    Trace 11 1 roots.toFinset := by
  classical
  have eq : augRoots.toFinset=roots.toFinset.image lift := by
    rw [←ground]
    ext z
    simp
  have rep (z) (hz : z∈augRoots.toFinset) : ∃ w : W,lift w=z := by
    rw [eq] at hz
    obtain ⟨w,_,e⟩ := Finset.mem_image.mp hz
    exact ⟨w,e⟩
  have back : augRoots.toFinset.image preimageWire=roots.toFinset := by
    rw [eq,Finset.image_image]
    ext w
    simp [Function.comp_def,preimage_lift]
  simpa only [back] using trace_of_shadow run rep

end CoNum4358.Tiny

end PEqualNP.Outside.L_meta_4358_aux

open PEqualNP.Outside.L_meta_4358_aux

theorem Co4358AssemblyProbe.conditional (signed : CoThetaNine.SignedLower) (ground : ¬ CoNum4358.Tiny.Trace 11 1 CoNum4358.Tiny.roots.toFinset) : have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (6 : ℕ) → Bool) → List Bool := fun (x2 : Fin (6 : ℕ) → Bool) => [x2 (0 : Fin (6 : ℕ)), x2 (1 : Fin (6 : ℕ)), Bool.false, x2 (2 : Fin (6 : ℕ)), x2 (3 : Fin (6 : ℕ)), x2 (4 : Fin (6 : ℕ)), x2 (5 : Fin (6 : ℕ))]; ∀ (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x3 →     (have x8 : Fin (11 : ℕ) → (Fin (6 : ℕ) → Bool) → Bool := fun (x8 : Fin (11 : ℕ)) (x9 : Fin (6 : ℕ) → Bool) => (x3.wires (x2 x9)).getD ((7 : ℕ) + ↑x8) Bool.false;       ∃ (x9 : Fin (8 : ℕ) → Fin (11 : ℕ)), (∀ (x10 x11 : Fin (8 : ℕ)), x10 ≠ x11 → ∃ (x13 : Fin (6 : ℕ) → Bool), x8 (x9 x10) x13 ≠ x8 (x9 x11) x13) ∧ ∀ (x10 x11 : Fin (8 : ℕ)), ∃ (x12 : Fin (6 : ℕ) → Bool), x8 (x9 x10) x12 ≠ (Bool.false :: Bool.true :: List.ofFn x12).getD (↑x11) Bool.false) →       x3.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x3 = x1 → List.Forall₂ (fun (x11 x12 : PEqualNP.CircuitLowerBounds.Gate) => x11.op = x12.op ∧ List.Forall₂ (fun (x13 x14 : ℕ) => x14 = x13 + (1 : ℕ) ∨ x14 = (0 : ℕ) ∧ (x13 = x5 ∨ x13 = x6)) x11.inputs x12.inputs) x3.gates x4.gates → (∀ (x12 : Fin (7 : ℕ) → Bool), (x4.wires (Bool.true :: List.ofFn x12)).getD (x3.output + (1 : ℕ)) Bool.false = (x1 x12 || x12 (0 : Fin (7 : ℕ)) || x12 (3 : Fin (7 : ℕ)))) → (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false] && x13.inputs.contains (2 : ℕ)) x3.gates).length ≥ (2 : ℕ) := by
  dsimp only
  intro C D a b fan _ size computes links promote
  exact CoNum4358.exclusion signed
    (fun h => ground (CoNum4358.Tiny.shadow_to_tiny (CoNum4358.shadow_root h))) C D a b fan size computes links promote
