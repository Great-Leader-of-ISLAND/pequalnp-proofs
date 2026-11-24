import Mathlib
import PEqualNP.Defs
-- Seven-vertex signed lower bound adapted from rzr1331, L-meta-2163, PR 6406.

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

abbrev Row := Fin 160
end CoAO3143

namespace CoAO3143.ProtocolProof

def separates (p n : Row) (a : Sig) : Prop :=
  bit true p a = true ∧ bit false n a = false

def Rectangle (f : Row → Row → Sig) : Prop :=
  ∀ p q n m, f p m = f q n → f p n = f p m

def Routed (S : Finset Sig) : Prop :=
  ∃ f : Row → Row → Sig, Rectangle f ∧ ∀ p n, f p n ∈ S ∧ separates p n (f p n)

private def child (d : Bool) (a b : Sig) (p n : Row) : Sig :=
  if d then (if bit true p a then a else b) else (if bit false n a then b else a)

private lemma child_mem (d : Bool) (a b : Sig) (p n : Row) :
    child d a b p n = a ∨ child d a b p n = b := by
  cases d <;> cases h : bit true p a <;> cases hn : bit false n a <;> simp [child,h,hn]

private lemma bit_binary (s : Bool) (i : Row) (d : Bool) (a b : Sig) :
    bit s i (bin d a b) =
      (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;>
    simp [bit,bin,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma child_valid {d a b p n} (h : separates p n (bin d a b)) :
    separates p n (child d a b p n) := by
  rcases h with ⟨hp,hn⟩
  rw [bit_binary] at hp hn
  cases d <;> cases ha : bit true p a <;> cases hb : bit false n a <;>
    simp_all [child,separates]

private lemma splice (U : Finset Sig) (a b : Sig) (d : Bool) (ha : a ∉ U) (hb : b ∉ U)
    (h : Routed (insert (bin d a b) U)) : Routed (insert a (insert b U)) := by
  obtain ⟨old,box,sound⟩ := h
  let z := bin d a b
  let new := fun p n => if old p n = z then child d a b p n else old p n
  let parent := fun l : Sig => if l = a ∨ l = b then z else l
  have other (p n) (hne : old p n ≠ z) : old p n ∈ U :=
    (Finset.mem_insert.mp (sound p n).1).resolve_left hne
  have recover (p n) : parent (new p n) = old p n := by
    by_cases h : old p n = z
    · simp [new,h,parent,child_mem]
    · have hu := other p n h
      have hna : old p n ≠ a := fun e => ha (e ▸ hu)
      have hnb : old p n ≠ b := fun e => hb (e ▸ hu)
      simp [new,h,parent,hna,hnb]
  refine ⟨new,?_,?_⟩
  · intro p q n m eq
    have fold := congrArg parent eq
    rw [recover,recover] at fold
    have center := box p q n m fold
    by_cases e : old p m = z
    · have e' : old q n = z := fold.symm.trans e
      have ec : old p n = z := center.trans e
      simp only [new,e,ec,e',if_true] at eq ⊢
      cases d
      · exact eq.symm
      · rfl
    · have ec : old p n ≠ z := fun he => e (center.symm.trans he)
      simpa [new,e,ec] using center
  · intro p n
    by_cases e : old p n = z
    · rw [show new p n = child d a b p n by simp [new,e]]
      have hs := (sound p n).2
      rw [e] at hs
      refine ⟨?_,child_valid hs⟩
      rcases child_mem d a b p n with l | r
      · simp [l]
      · simp [r]
    · rw [show new p n = old p n by simp [new,e]]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (other p n e)),(sound p n).2⟩

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

private theorem route_aux {k t S} (h : Live k t S) (hz : t = 0)
    (tight : S.card+t=k+1) : Routed S := by
  induction h with
  | stop =>
    refine ⟨fun _ _ => target,fun _ _ _ _ _ => rfl,?_⟩
    intro p n
    refine ⟨by simp,?_,?_⟩
    · change (BitVec.allOnes 160).getLsbD p.val = true
      rw [BitVec.getLsbD_allOnes]
      simp
    · simp [bit,target]
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    let z := bin d a b
    have hn : z ∉ U := fun hh => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hh))
    have sz := width tail
    change (insert z U).card+t ≤ k+1 at sz
    rw [Finset.card_insert_of_notMem hn] at sz
    have na : a ∉ insert b U := by
      intro ha
      rw [Finset.insert_eq_of_mem ha] at tight
      have ch := Finset.card_insert_le b U
      omega
    rw [Finset.card_insert_of_notMem na] at tight
    have nb : b ∉ U := by intro ha; rw [Finset.insert_eq_of_mem ha] at tight; omega
    rw [Finset.card_insert_of_notMem nb] at tight
    apply splice U a b d (fun h => na (Finset.mem_insert_of_mem h)) nb
    apply ih hz
    change (insert z U).card+t=k+1
    rw [Finset.card_insert_of_notMem hn]
    omega

theorem tight_routed {k S} (h : Live k 0 S) (tight : S.card=k+1) : Routed S :=
  route_aux h rfl (by omega)

def Forced (S : Finset Sig) (p n : Row) (a : Sig) : Prop :=
  ∀ x ∈ S, separates p n x → x = a

theorem forced_rectangle {k S} (h : Live k 0 S) (tight : S.card=k+1)
    {p q₁ q₂ n m₁ m₂ : Row} {a b : Sig}
    (a₁ : Forced S p m₁ a) (a₂ : Forced S q₁ n a)
    (b₁ : Forced S p m₂ b) (b₂ : Forced S q₂ n b) : a = b := by
  obtain ⟨f,box,ok⟩ := tight_routed h tight
  have atLeaf {i j x} (hh : Forced S i j x) : f i j = x :=
    hh _ (ok i j).1 (ok i j).2
  have left := (box p q₁ n m₁ ((atLeaf a₁).trans (atLeaf a₂).symm)).trans (atLeaf a₁)
  have right := (box p q₂ n m₂ ((atLeaf b₁).trans (atLeaf b₂).symm)).trans (atLeaf b₁)
  exact left.symm.trans right

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

def forcedB (ws : List Sig) (p n : Row) (a : Sig) : Bool :=
  ws.all fun x => x==a || !(bit true p x) || bit false n x

def verify (ws : List Sig) (c : Certificate) : Bool :=
  c.a != c.b && forcedB ws c.p c.m₁ c.a && forcedB ws c.q₁ c.n c.a &&
  forcedB ws c.p c.m₂ c.b && forcedB ws c.q₂ c.n c.b

private theorem forced_ok {ws p n a} (ok : forcedB ws p n a = true) : Forced ws.toFinset p n a := by
  intro x hx hxsep
  have h := List.all_eq_true.mp ok x (List.mem_toFinset.mp hx)
  rcases hxsep with ⟨l,r⟩
  simpa [l,r] using h

theorem verify_false {k ws} (live : Live k 0 ws.toFinset) (width : ws.toFinset.card=k+1)
    (c : Certificate) : verify ws c=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [verify,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨⟨⟨⟨neq,a₁⟩,a₂⟩,b₁⟩,b₂⟩ := h
  exact neq (forced_rectangle live width (forced_ok a₁) (forced_ok a₂) (forced_ok b₁) (forced_ok b₂))

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

namespace CoThetaFreeCore

def phase (sign bit : Bool) : Bool := if sign then !bit else bit

def base (join a b : Bool) : Bool := if join then a || b else a && b

inductive Kind where
  | conj | disj | leftOnly | rightOnly

def applyKind : Kind → Bool → Bool → Bool
  | .conj, a, b => a && b
  | .disj, a, b => a || b
  | .leftOnly, a, b => a && !b
  | .rightOnly, a, b => !a && b

def normalizedKind : Bool → Bool → Bool → Kind
  | false, false, false => .conj
  | false, false, true  => .leftOnly
  | false, true, false  => .rightOnly
  | false, true, true   => .disj
  | true, false, false  => .disj
  | true, false, true   => .rightOnly
  | true, true, false   => .leftOnly
  | true, true, true    => .conj

theorem normalization_table : ∀ join a0 b0 a b : Bool,
    phase (base join a0 b0) (base join a b) =
    applyKind (normalizedKind join a0 b0) (phase a0 a) (phase b0 b) := by decide

theorem inversion_table : ∀ a0 a : Bool, phase (!a0) (!a) = phase a0 a := by decide

variable {ρ : Type}

def norm (empty : ρ) (a : ρ → Bool) : ρ → Bool := fun i => phase (a empty) (a i)

theorem normalize_binary (empty : ρ) (join : Bool) (a b : ρ → Bool) :
    norm empty (fun i => base join (a i) (b i)) =
    fun i => applyKind (normalizedKind join (a empty) (b empty)) (norm empty a i) (norm empty b i) := by
  funext i
  exact normalization_table join (a empty) (b empty) (a i) (b i)

theorem normalize_unary (empty : ρ) (a : ρ → Bool) :
    norm empty (fun i => !(a i)) = norm empty a := by
  funext i
  exact inversion_table (a empty) (a i)

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

inductive Ordinary (raw : List (ρ → Bool)) : Nat → List (ρ → Bool) → Prop
  | start : Ordinary raw 0 raw
  | inv {n ws a} (pre : Ordinary raw n ws) (ha : a ∈ ws) :
      Ordinary raw n ((fun i => !(a i)) :: ws)
  | binary {n ws a b} (pre : Ordinary raw n ws) (join : Bool) (ha : a ∈ ws) (hb : b ∈ ws) :
      Ordinary raw (n+1) ((fun i => base join (a i) (b i)) :: ws)

inductive Free (raw : List (ρ → Bool)) : Nat → List (ρ → Bool) → Prop
  | start : Free raw 0 raw
  | binary {n ws a b} (pre : Free raw n ws) (kind : Kind) (ha : a ∈ ws) (hb : b ∈ ws) :
      Free raw (n+1) ((fun i => applyKind kind (a i) (b i)) :: ws)

def absentBit : ρ → Bool := fun _ => false

end CoThetaFreeCore

namespace CoPetersenThetaGeometry

def theta (m : Nat) : Bool :=
  let x := m.testBit
  (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 1 && x 4) || (x 0 && x 5) || (x 5 && x 6) || (x 1 && x 6)

end CoPetersenThetaGeometry

namespace CoThetaNine

open CoThetaFreeCore

abbrev SmallInput := Fin 128
def raw7 (i : Fin 7) (r : SmallInput) : Bool := r.val.testBit i.val
def ans7 (r : SmallInput) : Bool := CoPetersenThetaGeometry.theta r.val
def vertices7 : List (SmallInput→Bool) := absentBit::List.ofFn raw7

def SignedLower : Prop := ∀ {n ws}, Free vertices7 n ws → ans7∈ws → 11≤n

end CoThetaNine

namespace CoThetaFreeCore

variable {ρ : Type}

inductive PinForm where
  | constant (v : Bool)
  | copy (i : Nat)
  | inv (i : Nat)
  | binary (join : Bool) (i j : Nat)

def PinForm.value : PinForm → List (ρ→Bool) → (ρ→Bool)
  | .constant v, _ => fun _ => v
  | .copy i, w => w.getD i absentBit
  | .inv i, w => fun r => !(w.getD i absentBit r)
  | .binary join i j, w => fun r => base join (w.getD i absentBit r) (w.getD j absentBit r)

def PinForm.binaryCost : PinForm → Nat
  | .binary _ _ _ => 1
  | _ => 0

def cost : List PinForm → Nat
  | [] => 0
  | f::fs => f.binaryCost + cost fs

def execute : List PinForm → List (ρ→Bool) → List (ρ→Bool)
  | [], w => w
  | f::fs, w => execute fs (w ++ [f.value w])

private theorem read_registered (w pool : List (ρ→Bool)) (i : Nat) (hz : absentBit∈pool)
    (known : ∀ v∈w, v∈pool) : w.getD i absentBit∈pool := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact hz
  | some a => exact known a (List.mem_of_getElem? h)

private theorem pin_step (f : PinForm) (w pool raw : List (ρ→Bool)) (n : Nat)
    (pre : Ordinary raw n pool) (consts : ∀ b : Bool, (fun _ : ρ => b) ∈ pool)
    (known : ∀ v∈w, v∈pool) :
    ∃ ys, Ordinary raw (n+f.binaryCost) ys ∧
      (∀ v∈pool, v∈ys) ∧ f.value w∈ys := by
  have reg := read_registered w pool
  have hz : absentBit∈pool := consts false
  cases f with
  | constant v => exact ⟨pool,pre,fun _ h => h,consts _⟩
  | copy i => exact ⟨pool,pre,fun _ h => h,reg i hz known⟩
  | inv i =>
    exact ⟨_, Ordinary.inv pre (reg i hz known),
      fun _ h => List.mem_cons_of_mem _ h,by simp [PinForm.value]⟩
  | binary join i j =>
    exact ⟨_, Ordinary.binary pre join (reg i hz known) (reg j hz known),
      fun _ h => List.mem_cons_of_mem _ h,by simp [PinForm.value]⟩

theorem pins_to_program (fs : List PinForm) (w pool raw : List (ρ→Bool)) (n : Nat)
    (pre : Ordinary raw n pool) (consts : ∀ b : Bool, (fun _ : ρ => b) ∈ pool)
    (known : ∀ v∈w, v∈pool) :
    ∃ ys, Ordinary raw (n+cost fs) ys ∧ ∀ v∈execute fs w, v∈ys := by
  induction fs generalizing w pool n with
  | nil => exact ⟨_,pre,known⟩
  | cons f fs ih =>
    obtain ⟨mid,hmid,old,hw⟩ := pin_step f w pool raw n pre consts known
    have available (v) (h : v∈w++[f.value w]) : v∈mid := by
      rcases List.mem_append.mp h with original | fresh
      · exact old _ (known _ original)
      · exact (congrArg (fun u => u∈mid) (List.mem_singleton.mp fresh)).mpr hw
    obtain ⟨ys,hy,sub⟩ := ih (w++[f.value w]) mid (n+f.binaryCost) hmid
      (fun b => old _ (consts b)) available
    exact ⟨ys,by simpa [cost,Nat.add_assoc] using hy,sub⟩

end CoThetaFreeCore

namespace CoThetaPhysical
open CoThetaFreeCore PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gateForm (g : Gate) : PinForm :=
  match g.op, g.inputs with
  | .and, [] => .constant true
  | .or, [] => .constant false
  | .not, [] => .constant true
  | .and, [i] | .or, [i] => .copy i
  | .not, i::_ => .inv i
  | .and, i::j::_ => .binary false i j
  | .or, i::j::_ => .binary true i j
  | _, _ => .constant false

def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length≤2

private theorem read_word {ρ : Type} (w : List (ρ→Bool)) (i : Nat) (r : ρ) :
    ((w.map (fun f => f r)).getD i false) = w.getD i absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

private theorem read_option {ρ : Type} (o : Option (ρ→Bool)) (r : ρ) :
    (o.map (fun f => f r)).getD false = o.getD absentBit r := by cases o <;> rfl

theorem form_agrees {ρ : Type} (g : Gate) (hg : legal g) (w : List (ρ→Bool)) (r : ρ) :
    (gateForm g).value w r =
    g.op.eval (g.inputs.map fun i => (w.map (fun f => f r)).getD i false) := by
  obtain ⟨op,pins⟩ := g
  obtain ⟨hop,hlen⟩ := hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  change op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not at hop
  change pins.length≤2 at hlen
  rcases hop with rfl | rfl | rfl <;>
    cases pins with
    | nil => rfl
    | cons i xs =>
      cases xs with
      | nil => simp [gateForm,PinForm.value,GateOp.eval,base,read_word,read_option]
      | cons j t =>
        cases t with
        | nil => simp [gateForm,PinForm.value,GateOp.eval,base,read_word,read_option]
        | cons h t => simp at hlen

theorem map_execute {ρ : Type} (gs : List Gate) (w : List (ρ→Bool)) (r : ρ)
    (hg : ∀ g∈gs, legal g) :
    (execute (gs.map gateForm) w).map (fun f => f r) =
    gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)])
      (w.map (fun f => f r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,execute,List.foldl_cons]
    rw [ih _ (fun a ha => hg a (List.mem_cons_of_mem _ ha))]
    simp [form_agrees g (hg _ (by simp)) w r]

theorem circuit_rows {ρ : Type} (C : Circuit) (hf : FanInTwo C) (w : List (ρ→Bool)) (r : ρ) :
    (execute (C.gates.map gateForm) w).map (fun f => f r) = C.wires (w.map (fun f => f r)) :=
  map_execute C.gates w r hf

end CoThetaPhysical

namespace CoThetaFreeCore

theorem pin_cost_length (fs : List PinForm) : cost fs≤fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases f <;> simp only [cost,PinForm.binaryCost,List.length_cons] <;> omega

end CoThetaFreeCore

namespace CoTheta3174Public

private abbrev residualMask0 : Nat := 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf
private abbrev residualMask1 : Nat := 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000
private abbrev residualMask2 : Nat := 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f
private abbrev residualMask3 : Nat := 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff
private abbrev residualMask4 : Nat := 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f
private abbrev residualMask5 : Nat := 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000
private abbrev residualMask6 : Nat := 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc
private abbrev residualMask7 : Nat := 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000
private abbrev residualMask8 : Nat := 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000
private abbrev residualMask9 : Nat := 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000
private abbrev residualMask10 : Nat := 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f
private abbrev residualMask11 : Nat := 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f
private abbrev residualMask12 : Nat := 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive Der {α : Type} (op : Fin 4 → α → α → α) : ℕ → Set α → α → Prop
  | here {W : Set α} {y : α} : y ∈ W → Der op 0 W y
  | weak {k : ℕ} {W : Set α} {y : α} : Der op k W y → Der op (k + 1) W y
  | step {k : ℕ} {W : Set α} {y : α} (t : Fin 4) (a b : α) : a ∈ W → b ∈ W →
      Der op k (insert (op t a b) W) y → Der op (k + 1) W y

theorem Der.mono {α : Type} {op : Fin 4 → α → α → α} {k : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) : ∀ {W' : Set α}, W ⊆ W' → Der op k W' y := by
  induction h with
  | here hy => intro W' hs; exact Der.here (hs hy)
  | weak _ ih => intro W' hs; exact Der.weak (ih hs)
  | step t a b ha hb _ ih =>
    intro W' hs
    exact Der.step t a b (hs ha) (hs hb) (ih (Set.insert_subset_insert hs))

theorem Der.le {α : Type} {op : Fin 4 → α → α → α} {k k' : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) (hk : k ≤ k') : Der op k' W y := by
  induction hk with
  | refl => exact h
  | step _ ih => exact Der.weak ih

theorem Der.map {α β : Type} {op : Fin 4 → α → α → α} {op' : Fin 4 → β → β → β} (e : α → β)
    (he : ∀ t a b, e (op t a b) = op' t (e a) (e b)) {k : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) : Der op' k (e '' W) (e y) := by
  induction h with
  | here hy => exact Der.here ⟨_, hy, rfl⟩
  | weak _ ih => exact Der.weak ih
  | step t a b ha hb _ ih =>
    refine Der.step t (e a) (e b) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ?_
    rwa [Set.image_insert_eq, he] at ih

theorem Der.elim {α β : Type} {op : Fin 4 → α → α → α} {op' : Fin 4 → β → β → β} (e : α → β)
    (he : ∀ t a b, e (op t a b) = op' t (e a) (e b)) (x : α)
    (hl : ∀ t b, op' t (e x) b = e x ∨ op' t (e x) b = b)
    (hr : ∀ t b, op' t b (e x) = e x ∨ op' t b (e x) = b)
    {k : ℕ} {W : Set α} {y : α} (h : Der op k W y) :
    ∀ U : Set α, W ⊆ insert x U → y ≠ x → e x ∈ e '' U →
      Der op k U y ∨ ∃ k', k = k' + 1 ∧ Der op' k' (e '' U) (e y) := by
  induction h with
  | here hy =>
    intro U hs hne _
    exact Or.inl (Der.here ((hs hy).resolve_left hne))
  | weak _ ih =>
    intro U hs hne hx
    rcases ih U hs hne hx with h | ⟨k', rfl, h⟩
    · exact Or.inl (Der.weak h)
    · exact Or.inr ⟨_, rfl, Der.weak h⟩
  | @step k W y t a b ha hb h ih =>
    intro U hs hne hx
    have im (w : α) (hw : w ∈ W) : e w ∈ e '' U := by
      rcases hs hw with rfl | hw
      · exact hx
      · exact ⟨w, hw, rfl⟩
    by_cases hab : a ∈ U ∧ b ∈ U
    · have hs' : insert (op t a b) W ⊆ insert x (insert (op t a b) U) := by
        rintro w (rfl | hw)
        · exact Or.inr (Or.inl rfl)
        · rcases hs hw with rfl | hw
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hw)
      have hx' : e x ∈ e '' insert (op t a b) U := by
        obtain ⟨u, hu, h⟩ := hx; exact ⟨u, Or.inr hu, h⟩
      rcases ih _ hs' hne hx' with hd | ⟨k', hk', hd⟩
      · exact Or.inl (Der.step t a b hab.1 hab.2 hd)
      · refine Or.inr ⟨k' + 1, by rw [hk'], ?_⟩
        rw [Set.image_insert_eq, he] at hd
        exact Der.step t (e a) (e b) ⟨a, hab.1, rfl⟩ ⟨b, hab.2, rfl⟩ hd
    · have hc : e (op t a b) ∈ e '' U := by
        rw [he]
        by_cases hau : a ∈ U
        · have hbx : b = x := by
            rcases hs hb with h | h
            · exact h
            · exact absurd ⟨hau, h⟩ hab
          subst hbx
          rcases hr t (e a) with h | h
          · rw [h]; exact hx
          · rw [h]; exact im a ha
        · have hax : a = x := by
            rcases hs ha with h | h
            · exact h
            · exact absurd h hau
          subst hax
          rcases hl t (e b) with h | h
          · rw [h]; exact hx
          · rw [h]; exact im b hb
      refine Or.inr ⟨k, rfl, (h.map e he).mono ?_⟩
      rintro _ ⟨w, rfl | hw, rfl⟩
      · exact hc
      · exact im w hw

def opB (t : Fin 4) (a b : Bool) : Bool :=
  match t with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | 3 => b && !a

def opF {Ω : Type} (t : Fin 4) (f g : Ω → Bool) : Ω → Bool := fun x => opB t (f x) (g x)

def opN (t : Fin 4) (a b : ℕ) : ℕ :=
  match t with
  | 0 => Nat.land a b
  | 1 => Nat.lor a b
  | 2 => Nat.xor a (Nat.land a b)
  | 3 => Nat.xor b (Nat.land a b)

lemma land_bit (x y i : ℕ) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i

lemma lor_bit (x y i : ℕ) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

lemma xor_bit (x y i : ℕ) : (Nat.xor x y).testBit i = (x.testBit i != y.testBit i) := by
  simpa [bne] using Nat.testBit_xor x y i

lemma shr_bit (x s i : ℕ) : (Nat.shiftRight x s).testBit i = x.testBit (s + i) := by
  have := Nat.testBit_shiftRight (x := x) (i := s) (j := i)
  simpa using this

lemma opN_bit (t : Fin 4) (a b i : ℕ) :
    (opN t a b).testBit i = opB t (a.testBit i) (b.testBit i) := by
  fin_cases t <;> simp only [opN, opB, land_bit, lor_bit, xor_bit] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

lemma Der.agree {Ω : Type} {k : ℕ} {W : Set (Ω → Bool)} {y : Ω → Bool} (h : Der opF k W y)
    (p q : Ω) : (∀ w ∈ W, w p = w q) → y p = y q := by
  induction h with
  | here hy => intro hw; exact hw _ hy
  | weak _ ih => exact ih
  | step t a b ha hb _ ih =>
    intro hw
    refine ih ?_
    rintro w (rfl | hm)
    · simp only [opF, hw a ha, hw b hb]
    · exact hw w hm

structure St where
  t : Fin 4
  a : ℕ
  b : ℕ

def St.val (s : St) : ℕ := opN s.t s.a s.b

def Valid (y : ℕ) : Set ℕ → List St → Prop
  | W, [] => y ∈ W
  | W, s :: l => s.a ∈ W ∧ s.b ∈ W ∧ s.val ∉ W ∧ Valid y (insert s.val W) l

def need (y : ℕ) : List St → Finset ℕ
  | [] => {y}
  | s :: l => insert s.a (insert s.b ((need y l).erase s.val))

def Useful (y : ℕ) : List St → Prop
  | [] => True
  | s :: l => s.val ∈ need y l ∧ Useful y l

def killB (m : ℕ) (s : St) : Bool := Nat.beq (Nat.land s.a m) 0 || Nat.beq (Nat.land s.b m) 0

def kills (m : ℕ) (l : List St) : ℕ := l.countP (killB m)

def Chain : ℕ → List St → Prop
  | _, [] => True
  | p, s :: l => (s.a = p ∨ s.b = p ∨ p ≤ s.val) ∧ Chain s.val l

lemma valid_of_der {k : ℕ} {W : Set ℕ} {y : ℕ} (h : Der opN k W y) :
    ∃ l, l.length ≤ k ∧ Valid y W l := by
  induction h with
  | here hy => exact ⟨[], by simp, hy⟩
  | weak _ ih => obtain ⟨l, h1, h2⟩ := ih; exact ⟨l, by omega, h2⟩
  | @step k W y t a b ha hb _ ih =>
    obtain ⟨l, h1, h2⟩ := ih
    by_cases hc : opN t a b ∈ W
    · rw [Set.insert_eq_of_mem hc] at h2; exact ⟨l, by omega, h2⟩
    · exact ⟨⟨t, a, b⟩ :: l, by simp; omega, ha, hb, hc, h2⟩

lemma need_sub {y : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l → ∀ x ∈ need y l, x ∈ W := by
  induction l with
  | nil => intro W h x hx; rw [need, Finset.mem_singleton] at hx; rw [hx]; exact h
  | cons s l ih =>
    intro W h x hx
    obtain ⟨ha, hb, hc, hv⟩ := h
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with rfl | rfl | ⟨h1, h2⟩
    · exact ha
    · exact hb
    · exact (ih hv x h2).resolve_left h1

lemma valid_drop {y c : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y (insert c W) l →
    c ∉ need y l → Valid y W l := by
  induction l with
  | nil =>
    intro W h hc
    rw [need, Finset.mem_singleton] at hc
    exact h.resolve_left (fun e => hc e.symm)
  | cons s l ih =>
    intro W h hc
    obtain ⟨ha, hb, hf, hv⟩ := h
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hc
    push Not at hc
    obtain ⟨h1, h2, h3⟩ := hc
    have hne : c ≠ s.val := fun e => hf (Or.inl e.symm)
    refine ⟨ha.resolve_left (Ne.symm h1), hb.resolve_left (Ne.symm h2), fun h => hf (Or.inr h), ?_⟩
    rw [Set.insert_comm] at hv
    exact ih hv (h3 hne)

lemma useful_of_min {y : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l →
    (∀ l', Valid y W l' → l.length ≤ l'.length) → Useful y l := by
  induction l with
  | nil => intro W _ _; trivial
  | cons s l ih =>
    intro W h hmin
    obtain ⟨ha, hb, hf, hv⟩ := h
    refine ⟨?_, ih hv fun l' hl' => ?_⟩
    · by_contra hc
      have := hmin l (valid_drop l hv hc)
      simp at this
    · have := hmin (s :: l') ⟨ha, hb, hf, hl'⟩
      simpa using this

lemma need_card {y : ℕ} (l : List St) (h : Useful y l) : (need y l).card ≤ l.length + 1 := by
  induction l with
  | nil => simp [need]
  | cons s l ih =>
    obtain ⟨h1, h2⟩ := h
    have e := Finset.card_erase_of_mem h1
    have i := ih h2
    have c1 := Finset.card_insert_le s.a (insert s.b ((need y l).erase s.val))
    have c2 := Finset.card_insert_le s.b ((need y l).erase s.val)
    have p := Finset.card_pos.mpr ⟨_, h1⟩
    rw [need, List.length_cons]
    omega

lemma need_next {y : ℕ} {s : St} {l : List St} {x : ℕ} (h : x ∈ need y l) :
    x = s.val ∨ x ∈ need y (s :: l) := by
  by_cases hx : x = s.val
  · exact Or.inl hx
  · right; rw [need]; simp [hx, h]

lemma need_agree {y i j : ℕ} (l : List St) (h : ∀ x ∈ need y l, x.testBit i = x.testBit j) :
    y.testBit i = y.testBit j := by
  induction l with
  | nil => exact h y (by simp [need])
  | cons s l ih =>
    refine ih fun x hx => ?_
    rcases need_next (s := s) hx with rfl | hx
    · rw [St.val, opN_bit, opN_bit, h s.a (by simp [need]), h s.b (by simp [need])]
    · exact h x hx

lemma kill_forced {y m x : ℕ} (hy : Nat.land y m ≠ 0) (l : List St) (hx : x ∈ need y l)
    (hm : Nat.land x m = 0) : 1 ≤ kills m l := by
  induction l with
  | nil => rw [need, Finset.mem_singleton] at hx; rw [hx] at hm; exact absurd hm hy
  | cons s l ih =>
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    have hk : killB m s = true → 1 ≤ kills m (s :: l) := fun h => by
      rw [kills, List.countP_cons_of_pos h]; omega
    rcases hx with rfl | rfl | ⟨_, h2⟩
    · exact hk (by unfold killB; rw [hm]; rfl)
    · exact hk (by unfold killB; rw [hm]; exact Bool.or_true _)
    · have := ih h2
      have c : kills m l ≤ kills m (s :: l) := by
        rw [kills, kills, List.countP_cons]; omega
      omega

lemma land_op (t : Fin 4) (a b m : ℕ) :
    Nat.land (opN t a b) m = opN t (Nat.land a m) (Nat.land b m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [land_bit, opN_bit]
  fin_cases t <;> cases a.testBit i <;> cases b.testBit i <;> cases m.testBit i <;> rfl

lemma opN_zero_left (t : Fin 4) (b : ℕ) : opN t 0 b = 0 ∨ opN t 0 b = b := by
  have key (c : Bool → Bool) (h : ∀ i, (opN t 0 b).testBit i = c (b.testBit i))
      (hc : c = (fun _ => false) ∨ c = id) : opN t 0 b = 0 ∨ opN t 0 b = b := by
    rcases hc with rfl | rfl
    · left; apply Nat.eq_of_testBit_eq; intro i; rw [h]; simp
    · right; apply Nat.eq_of_testBit_eq; intro i; rw [h]; rfl
  fin_cases t
  · exact key _ (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)

def swapT : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2

lemma opN_swap (t : Fin 4) (a b : ℕ) : opN t a b = opN (swapT t) b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [opN_bit, opN_bit]
  fin_cases t <;> cases a.testBit i <;> cases b.testBit i <;> rfl

lemma opN_zero_right (t : Fin 4) (b : ℕ) : opN t b 0 = 0 ∨ opN t b 0 = b := by
  rw [opN_swap]; exact opN_zero_left _ _

lemma opN_self (t : Fin 4) (a : ℕ) : opN t a a = 0 ∨ opN t a a = a := by
  have key (c : Bool → Bool) (h : ∀ i, (opN t a a).testBit i = c (a.testBit i))
      (hc : c = (fun _ => false) ∨ c = id) : opN t a a = 0 ∨ opN t a a = a := by
    rcases hc with rfl | rfl
    · left; apply Nat.eq_of_testBit_eq; intro i; rw [h]; simp
    · right; apply Nat.eq_of_testBit_eq; intro i; rw [h]; rfl
  fin_cases t
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)

lemma der_masked {y m : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l → 0 ∈ W →
    ∃ n, n + kills m l = l.length ∧ Der opN n ((fun w => Nat.land w m) '' W) (Nat.land y m) := by
  induction l with
  | nil => intro W h _; exact ⟨0, by simp [kills], Der.here ⟨y, h, rfl⟩⟩
  | cons s l ih =>
    intro W h h0
    obtain ⟨ha, hb, _, hv⟩ := h
    obtain ⟨n, hn, hd⟩ := ih hv (Or.inr h0)
    have im (w : ℕ) (hw : w ∈ W) : Nat.land w m ∈ (fun w => Nat.land w m) '' W := ⟨w, hw, rfl⟩
    have z : 0 ∈ (fun w => Nat.land w m) '' W := ⟨0, h0, by simp [Nat.land]⟩
    by_cases hk : killB m s = true
    · refine ⟨n, ?_, hd.mono ?_⟩
      · rw [kills, List.countP_cons_of_pos hk, List.length_cons]
        rw [kills] at hn; omega
      · rintro _ ⟨w, rfl | hw, rfl⟩
        · show Nat.land s.val m ∈ _
          rw [St.val, land_op]
          rw [killB, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at hk
          rcases hk with h | h
          · rw [h]
            rcases opN_zero_left s.t (Nat.land s.b m) with e | e
            · rw [e]; exact z
            · rw [e]; exact im _ hb
          · rw [h]
            rcases opN_zero_right s.t (Nat.land s.a m) with e | e
            · rw [e]; exact z
            · rw [e]; exact im _ ha
        · exact im w hw
    · refine ⟨n + 1, ?_, ?_⟩
      · rw [kills, List.countP_cons_of_neg hk, List.length_cons]
        rw [kills] at hn; omega
      · refine Der.step s.t _ _ (im _ ha) (im _ hb) ?_
        rw [Set.image_insert_eq] at hd
        have e : Nat.land s.val m = opN s.t (Nat.land s.a m) (Nat.land s.b m) := land_op _ _ _ _
        rw [← e]; exact hd

lemma valid_swap {y : ℕ} (s1 s2 : St) (post : List St) (h1 : s2.a ≠ s1.val) (h2 : s2.b ≠ s1.val)
    (pre : List St) : ∀ {W : Set ℕ}, Valid y W (pre ++ s1 :: s2 :: post) →
      Valid y W (pre ++ s2 :: s1 :: post) := by
  induction pre with
  | nil =>
    intro W h
    obtain ⟨ha, hb, hc, ha2, hb2, hc2, hv⟩ := h
    refine ⟨ha2.resolve_left h1, hb2.resolve_left h2, fun h => hc2 (Or.inr h), Or.inr ha, Or.inr hb,
      ?_, ?_⟩
    · rintro (e | h)
      · exact hc2 (Or.inl e.symm)
      · exact hc h
    · rw [Set.insert_comm]; exact hv
  | cons s pre ih =>
    intro W h
    obtain ⟨ha, hb, hc, hv⟩ := h
    exact ⟨ha, hb, hc, ih hv⟩

def keyN (l : List St) : ℕ := l.foldl (fun acc s => 2 * acc + s.val) 0

lemma fold_lt (l : List St) : ∀ {x x' : ℕ}, x < x' →
    l.foldl (fun acc s => 2 * acc + s.val) x < l.foldl (fun acc s => 2 * acc + s.val) x' := by
  induction l with
  | nil => intro x x' h; exact h
  | cons s l ih =>
    intro x x' h
    exact ih (show 2 * x + s.val < 2 * x' + s.val by omega)

lemma key_swap (pre post : List St) (s1 s2 : St) (h : s2.val < s1.val) :
    keyN (pre ++ s2 :: s1 :: post) < keyN (pre ++ s1 :: s2 :: post) := by
  unfold keyN
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_cons,
    List.foldl_cons]
  exact fold_lt post (by omega)

lemma chain_of {l : List St} : ∀ (p : ℕ),
    (∀ s l', l = s :: l' → (s.a = p ∨ s.b = p ∨ p ≤ s.val)) →
    (∀ pre s1 s2 post, l = pre ++ s1 :: s2 :: post →
      (s2.a = s1.val ∨ s2.b = s1.val ∨ s1.val ≤ s2.val)) → Chain p l := by
  induction l with
  | nil => intro p _ _; trivial
  | cons s l ih =>
    intro p h1 h2
    refine ⟨h1 s l rfl, ih s.val (fun s' l' e => ?_) (fun pre s1 s2 post e => ?_)⟩
    · exact h2 [] s s' l' (by rw [e]; rfl)
    · exact h2 (s :: pre) s1 s2 post (by rw [e]; rfl)

lemma exists_min {α : Type} (S : Set α) (f : α → ℕ) (h : S.Nonempty) :
    ∃ l ∈ S, ∀ l' ∈ S, f l ≤ f l' := by
  obtain ⟨l, hl, hm⟩ := (measure f).wf.has_min S h
  exact ⟨l, hl, fun l' hl' => not_lt.mp (hm l' hl')⟩

def headV : List St → ℕ
  | [] => 0
  | s :: _ => s.val

lemma exists_sorted {y : ℕ} {W : Set ℕ} {k : ℕ} (h : Der opN k W y) :
    ∃ l, l.length ≤ k ∧ Valid y W l ∧ Useful y l ∧ Chain 0 l ∧
      ∀ l', Valid y W l' → l'.length = l.length → headV l ≤ headV l' := by
  obtain ⟨l0, hk0, hv0⟩ := valid_of_der h
  obtain ⟨l1, hv1, hmin⟩ := exists_min {l | Valid y W l} List.length ⟨l0, hv0⟩
  obtain ⟨l2, ⟨hv2, hlen2⟩, hhead⟩ :=
    exists_min {l | Valid y W l ∧ l.length = l1.length} headV ⟨l1, hv1, rfl⟩
  obtain ⟨l, ⟨hv, hlen, hh⟩, hkey⟩ :=
    exists_min {l | Valid y W l ∧ l.length = l1.length ∧ headV l = headV l2} keyN ⟨l2, hv2, hlen2, rfl⟩
  refine ⟨l, ?_, hv, useful_of_min l hv (fun l' hl' => by rw [hlen]; exact hmin l' hl'), ?_, ?_⟩
  · rw [hlen]; exact (hmin l0 hv0).trans hk0
  · refine chain_of 0 (fun s l' _ => Or.inr (Or.inr (Nat.zero_le _))) ?_
    intro pre s1 s2 post e
    by_contra hc
    push Not at hc
    obtain ⟨c1, c2, c3⟩ := hc
    rw [e] at hv hlen hh hkey
    have sv := valid_swap s1 s2 post c1 c2 pre hv
    have sl : (pre ++ s2 :: s1 :: post).length = l1.length := by
      rw [← hlen]; simp
    cases pre with
    | nil =>
      have := hhead _ ⟨sv, sl⟩
      rw [← hh] at this
      change s1.val ≤ s2.val at this
      omega
    | cons p pre =>
      have := hkey _ ⟨sv, sl, by rw [← hh]; rfl⟩
      have := key_swap (p :: pre) post s1 s2 c3
      omega
  · intro l' hl' hl
    rw [hh]; exact hhead l' ⟨hl', by rw [hl, hlen]⟩

lemma step_facts {y : ℕ} {W : Set ℕ} {s : St} {l : List St} (h : Valid y W (s :: l)) (h0 : 0 ∈ W) :
    s.a ≠ 0 ∧ s.b ≠ 0 ∧ s.a ≠ s.b ∧ s.val ≠ 0 ∧ s.val ≠ s.a ∧ s.val ≠ s.b ∧
      s.val ∉ need y (s :: l) := by
  have hn := need_sub (s :: l) h
  obtain ⟨ha, hb, hc, _⟩ := h
  refine ⟨?_, ?_, ?_, fun e => hc (e ▸ h0), fun e => hc (e ▸ ha), fun e => hc (e ▸ hb),
    fun hh => hc (hn _ hh)⟩
  · intro e
    rcases opN_zero_left s.t s.b with h | h
    · exact hc (by rw [St.val, e, h]; exact h0)
    · exact hc (by rw [St.val, e, h]; exact hb)
  · intro e
    rcases opN_zero_right s.t s.a with h | h
    · exact hc (by rw [St.val, e, h]; exact h0)
    · exact hc (by rw [St.val, e, h]; exact ha)
  · intro e
    rcases opN_self s.t s.a with h | h
    · exact hc (by rw [St.val, ← e, h]; exact h0)
    · exact hc (by rw [St.val, ← e, h]; exact ha)

structure Wr where
  w : ℕ
  s : ℕ
  f : ℕ

def sepN (L w : ℕ) : ℕ := Nat.land (Nat.xor w (Nat.shiftRight w 143)) L

def covL : List Wr → ℕ
  | [] => 0
  | a :: l => Nat.lor a.s (covL l)

def flL : List Wr → ℕ
  | [] => 0
  | a :: l => Nat.lor a.f (flL l)

def lenL : List Wr → ℕ
  | [] => 0
  | _ :: l => Nat.succ (lenL l)

def absentL (g : ℕ) : List Wr → Bool
  | [] => true
  | x :: l => cond (Nat.beq x.w g) false (absentL g l)

def app : List Wr → List Wr → List Wr
  | [], m => m
  | a :: l, m => a :: app l m

def sub (a b : ℕ) : Bool := Nat.beq (Nat.land a b) a

def force (x : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun n _ => f (Nat.succ n)) x

lemma force_eq (x : ℕ) (f : ℕ → Bool) : force x f = f x := by cases x <;> rfl

abbrev Next := List Wr → ℕ → ℕ → ℕ → ℕ → Bool

def tryG (L : ℕ) (r : Next) (k m : ℕ) (rest : List Wr) (cr c1 c2 c3 : ℕ) (a b : Wr) (last : ℕ)
    (uses : Bool) (g fg : ℕ) : Bool :=
  cond (Nat.beq g 0) false (cond (Nat.beq g a.w) false (cond (Nat.beq g b.w) false
    (cond (cond uses true (Nat.ble last g))
      (cond (sub fg c1)
        (force (sepN L g) fun sg =>
          force (Nat.lor cr sg) fun base =>
            (cond (Nat.beq base L) (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: rest) c1 c2 c3 g) false)
              false) ||
            (cond (Nat.ble m (Nat.succ k))
              ((cond (sub a.f c1) (cond (Nat.beq (Nat.lor base a.s) L)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: a :: rest) c1 c2 c3 g) false) false) false) ||
               (cond (sub b.f c1) (cond (Nat.beq (Nat.lor base b.s) L)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: b :: rest) c1 c2 c3 g) false) false) false) ||
               (cond (Nat.ble m k) (cond (sub a.f c1) (cond (sub b.f c1)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: a :: b :: rest) c1 c2 c3 g) false) false)
                  false) false))
              false))
        false)
      false)))

def tryP (L : ℕ) (r : Next) (k m c1 c2 c3 last : ℕ) (a b : Wr) (rest : List Wr) : Bool :=
  force (Nat.lor a.f b.f) fun K =>
    cond (sub K c1)
      (force (Nat.lor c2 (Nat.xor c1 (Nat.land c1 K))) fun d1 =>
       force (Nat.lor c3 (Nat.xor c2 (Nat.land c2 K))) fun d2 =>
       force (Nat.xor c3 (Nat.land c3 K)) fun d3 =>
        cond (sub (flL rest) d1)
          (force (covL rest) fun cr =>
            force (Nat.land a.w b.w) fun ab =>
              tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last) ab K ||
              (tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.lor a.w b.w) (Nat.land a.f b.f) ||
              (tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.xor a.w ab) a.f ||
              tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.xor b.w ab) b.f)))
          false)
      false

def pairsB (a : Wr) : List Wr → List Wr → List (Wr × Wr × List Wr)
  | _, [] => []
  | acc, b :: l => (a, b, app acc l) :: pairsB a (b :: acc) l

def pairsA : List Wr → List Wr → List (Wr × Wr × List Wr)
  | _, [] => []
  | acc, a :: l => pairsB a acc l ++ pairsA (a :: acc) l

def anyP (p : Wr → Wr → List Wr → Bool) : List (Wr × Wr × List Wr) → Bool
  | [] => false
  | x :: l => p x.1 x.2.1 x.2.2 || anyP p l

def isT (y : ℕ) : List Wr → Bool
  | [a] => Nat.beq a.w y
  | _ => false

def search (L y : ℕ) : ℕ → Next
  | 0, v, _, _, _, _ => isT y v
  | k + 1, v, c1, c2, c3, last =>
    isT y v || anyP (tryP L (search L y k) k (lenL v) c1 c2 c3 last) (pairsA [] v)

lemma lenL_eq (v : List Wr) : lenL v = v.length := by
  induction v with
  | nil => rfl
  | cons a l ih => rw [lenL, ih]; rfl

lemma app_eq (a b : List Wr) : app a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x l ih => rw [app, ih]; rfl

lemma absent_true {g : ℕ} {l : List Wr} (h : ∀ x ∈ l, x.w ≠ g) : absentL g l = true := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : Nat.beq x.w g = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]; exact h x (by simp)
    rw [absentL, hx]
    exact ih fun u hu => h u (by simp [hu])

lemma sub_true {a b : ℕ} (h : ∀ i, a.testBit i = true → b.testBit i = true) : sub a b = true := by
  rw [sub, Nat.beq_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [land_bit]
  cases ha : a.testBit i
  · rfl
  · rw [h i ha]; rfl

lemma anyP_true {p : Wr → Wr → List Wr → Bool} {l : List (Wr × Wr × List Wr)} {a b : Wr}
    {r : List Wr} (hm : (a, b, r) ∈ l) (hp : p a b r = true) : anyP p l = true := by
  induction l with
  | nil => simp at hm
  | cons x l ih =>
    rw [anyP, Bool.or_eq_true]
    rcases List.mem_cons.mp hm with rfl | h
    · exact Or.inl hp
    · exact Or.inr (ih h)

lemma pairsB_spec (a b : Wr) (l : List Wr) : ∀ acc : List Wr, b ∈ l →
    ∃ r, (a, b, r) ∈ pairsB a acc l ∧ (acc ++ l).Perm (b :: r) := by
  induction l with
  | nil => intro acc h; simp at h
  | cons x l ih =>
    intro acc h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨acc ++ l, by simp [pairsB, app_eq], List.perm_middle⟩
    · obtain ⟨r, h1, h2⟩ := ih (x :: acc) h
      exact ⟨r, by simp [pairsB, h1], List.perm_middle.trans h2⟩

lemma pairsA_spec (a b : Wr) (hab : a ≠ b) (l : List Wr) : ∀ acc : List Wr, a ∈ l → b ∈ l →
    ∃ r, ((a, b, r) ∈ pairsA acc l ∨ (b, a, r) ∈ pairsA acc l) ∧ (acc ++ l).Perm (a :: b :: r) := by
  induction l with
  | nil => intro acc h; simp at h
  | cons x l ih =>
    intro acc ha hb
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with e | hb'
      · exact absurd e.symm hab
      · obtain ⟨r, h1, h2⟩ := pairsB_spec a b l acc hb'
        exact ⟨r, Or.inl (by rw [pairsA]; exact List.mem_append_left _ h1),
          List.perm_middle.trans (h2.cons a)⟩
    · rcases List.mem_cons.mp hb with rfl | hb'
      · obtain ⟨r, h1, h2⟩ := pairsB_spec b a l acc ha'
        exact ⟨r, Or.inr (by rw [pairsA]; exact List.mem_append_left _ h1),
          (List.perm_middle.trans (h2.cons b)).trans (List.Perm.swap a b r)⟩
      · obtain ⟨r, h1, h2⟩ := ih (x :: acc) ha' hb'
        refine ⟨r, ?_, List.perm_middle.trans h2⟩
        rcases h1 with h | h
        · exact Or.inl (by rw [pairsA]; exact List.mem_append_right _ h)
        · exact Or.inr (by rw [pairsA]; exact List.mem_append_right _ h)

structure Rep (L H : ℕ) (mask : ℕ → ℕ) (v : List Wr) (S : Finset ℕ) : Prop where
  nd : (v.map Wr.w).Nodup
  mem : ∀ x, x ∈ S ↔ ∃ u ∈ v, u.w = x
  sep : ∀ u ∈ v, u.s = sepN L u.w
  fl : ∀ u ∈ v, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0

def Bud (H : ℕ) (mask : ℕ → ℕ) (c1 c2 c3 : ℕ) (l : List St) : Prop :=
  ∀ h < H, kills (mask h) l ≤ 3 ∧ (1 ≤ kills (mask h) l → c1.testBit h = true) ∧
    (2 ≤ kills (mask h) l → c2.testBit h = true) ∧ (3 ≤ kills (mask h) l → c3.testBit h = true)

lemma cov_bit (l : List Wr) (i : ℕ) : (covL l).testBit i = l.any fun a => a.s.testBit i := by
  induction l with
  | nil => simp [covL]
  | cons a l ih => rw [covL, lor_bit, ih, List.any_cons]

lemma fl_bit (l : List Wr) (i : ℕ) : (flL l).testBit i = l.any fun a => a.f.testBit i := by
  induction l with
  | nil => simp [flL]
  | cons a l ih => rw [flL, lor_bit, ih, List.any_cons]

lemma sepN_bit (L w i : ℕ) :
    (sepN L w).testBit i = ((w.testBit i != w.testBit (143 + i)) && L.testBit i) := by
  rw [sepN, land_bit, xor_bit, shr_bit]

lemma rep_cov {L H y : ℕ} {mask : ℕ → ℕ}
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i)) {v : List Wr} {l : List St}
    (hr : Rep L H mask v (need y l)) : covL v = L := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [cov_bit]
  cases hi : L.testBit i
  · rw [List.any_eq_false]
    intro u hu
    rw [hr.sep u hu, sepN_bit, hi]; simp
  · rw [List.any_eq_true]
    by_contra hc
    push Not at hc
    refine hL i hi (need_agree l fun x hx => ?_)
    obtain ⟨u, hu, rfl⟩ := (hr.mem x).mp hx
    have := hc u hu
    rw [hr.sep u hu, sepN_bit, hi] at this
    cases h1 : u.w.testBit i <;> cases h2 : u.w.testBit (143 + i) <;> simp_all

lemma rep_len {L H : ℕ} {mask : ℕ → ℕ} {v : List Wr} {S : Finset ℕ} (hr : Rep L H mask v S) :
    v.length = S.card := by
  have e : S = (v.map Wr.w).toFinset := by
    ext x; rw [hr.mem, List.mem_toFinset, List.mem_map]
  rw [e, List.toFinset_card_of_nodup hr.nd, List.length_map]

lemma flag_forced {H y : ℕ} {mask : ℕ → ℕ} (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    {l : List St} {d1 d2 d3 : ℕ} (hb : Bud H mask d1 d2 d3 l) {f x : ℕ} (hx : x ∈ need y l)
    (hf : ∀ h, f.testBit h = true → h < H ∧ Nat.land x (mask h) = 0) : sub f d1 = true := by
  refine sub_true fun h hh => ?_
  obtain ⟨h1, h2⟩ := hf h hh
  exact (hb h h1).2.1 (kill_forced (hy h h1) l hx h2)

lemma tryG_true {L H y k : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    {r : Next} {v rest : List Wr} {a b : Wr} {l : List St} {g fg last d1 d2 d3 m : ℕ} {uses : Bool}
    (hm : m = v.length) (hv : Rep L H mask v (insert a.w (insert b.w ((need y l).erase g))))
    (hp : v.Perm (a :: b :: rest)) (hg : g ∈ need y l) (hg0 : g ≠ 0) (hab : a.w ≠ b.w)
    (hgS : g ∉ insert a.w (insert b.w ((need y l).erase g)))
    (hfg : ∀ h, fg.testBit h = true → h < H ∧ Nat.land g (mask h) = 0)
    (hcard : (need y l).card ≤ k + 1) (hord : uses = true ∨ last ≤ g)
    (hb : Bud H mask d1 d2 d3 l)
    (hr : ∀ v', Rep L H mask v' (need y l) → r v' d1 d2 d3 g = true) :
    tryG L r k m rest (covL rest) d1 d2 d3 a b last uses g fg = true := by
  have hga : g ≠ a.w := fun e => hgS (by simp [e])
  have hgb : g ≠ b.w := fun e => hgS (by simp [e])
  have nd2 : ((a :: b :: rest).map Wr.w).Nodup := (hp.map Wr.w).nodup_iff.mp hv.nd
  simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at nd2
  obtain ⟨⟨_, har⟩, hbr, hrr⟩ := nd2
  have memr (x : ℕ) : x ∈ rest.map Wr.w ↔ x ∈ need y l ∧ x ≠ g ∧ x ≠ a.w ∧ x ≠ b.w := by
    have h1 : (x ∈ insert a.w (insert b.w ((need y l).erase g))) ↔ ∃ u ∈ a :: b :: rest, u.w = x := by
      rw [hv.mem]; exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hp.mem_iff.mp hu, e⟩, fun ⟨u, hu, e⟩ => ⟨u, hp.mem_iff.mpr hu, e⟩⟩
    rw [List.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h2 := h1.mpr ⟨u, by simp [hu], rfl⟩
      have n1 : u.w ≠ a.w := fun e => har (e ▸ List.mem_map_of_mem hu)
      have n2 : u.w ≠ b.w := fun e => hbr (e ▸ List.mem_map_of_mem hu)
      simp only [Finset.mem_insert, Finset.mem_erase] at h2
      rcases h2 with h | h | ⟨h3, h4⟩
      · exact absurd h n1
      · exact absurd h n2
      · exact ⟨h4, h3, n1, n2⟩
    · rintro ⟨h2, h3, h4, h5⟩
      obtain ⟨u, hu, e⟩ := h1.mp (by simp [h2, h3])
      simp only [List.mem_cons] at hu
      rcases hu with rfl | rfl | hu
      · exact absurd e.symm h4
      · exact absurd e.symm h5
      · exact ⟨u, hu, e⟩
  have hgr : g ∉ rest.map Wr.w := fun h => ((memr g).mp h).2.1 rfl
  have sepr : ∀ u ∈ rest, u.s = sepN L u.w := fun u hu => hv.sep u (hp.mem_iff.mpr (by simp [hu]))
  have flr : ∀ u ∈ rest, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0 :=
    fun u hu => hv.fl u (hp.mem_iff.mpr (by simp [hu]))
  have sepa := hv.sep a (hp.mem_iff.mpr (by simp))
  have sepb := hv.sep b (hp.mem_iff.mpr (by simp))
  have fla := hv.fl a (hp.mem_iff.mpr (by simp))
  have flb := hv.fl b (hp.mem_iff.mpr (by simp))
  have len : v.length = rest.length + 2 := by rw [hp.length_eq]; simp
  have b1 : Nat.beq g 0 = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hg0
  have b2 : Nat.beq g a.w = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hga
  have b3 : Nat.beq g b.w = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hgb
  have b4 : (cond uses true (Nat.ble last g)) = true := by
    rcases hord with h | h
    · rw [h]; rfl
    · cases uses
      · exact Nat.ble_eq.mpr h
      · rfl
  have b5 : sub fg d1 = true := flag_forced hy hb hg hfg
  have b6 : absentL g rest = true :=
    absent_true fun x hx e => hgr (e ▸ List.mem_map_of_mem hx)
  set G : Wr := ⟨g, sepN L g, fg⟩ with hG
  unfold tryG
  rw [b1, b2, b3, b4, b5, force_eq, force_eq, b6]
  simp only [cond_false, cond_true]
  by_cases hA : a.w ∈ need y l <;> by_cases hB : b.w ∈ need y l
  · have R : Rep L H mask (G :: a :: b :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨hga, hgb, hgr⟩, ⟨hab, har⟩, hbr, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact ⟨a, by simp, e2.symm⟩
          by_cases e3 : x = b.w
          · exact ⟨b, by simp, e3.symm⟩
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | rfl | rfl | hu
          · exact hg
          · exact hA
          · exact hB
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | rfl | hu
        · rfl
        · exact sepa
        · exact sepb
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | rfl | hu
        · exact hfg
        · exact fla
        · exact flb
        · exact flr u hu
    have hl := rep_len R
    simp only [List.length_cons] at hl
    have c1 : Nat.ble m (Nat.succ k) = true := by rw [Nat.ble_eq]; omega
    have c2 : Nat.ble m k = true := by rw [Nat.ble_eq]; omega
    rw [c1, c2, flag_forced hy hb hA fla, flag_forced hy hb hB flb, hr _ R]
    simp
  · have R : Rep L H mask (G :: a :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨hga, hgr⟩, har, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact ⟨a, by simp, e2.symm⟩
          by_cases e3 : x = b.w
          · exact absurd (e3 ▸ hx) hB
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | rfl | hu
          · exact hg
          · exact hA
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · rfl
        · exact sepa
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · exact hfg
        · exact fla
        · exact flr u hu
    have hl := rep_len R
    simp only [List.length_cons] at hl
    have c1 : Nat.ble m (Nat.succ k) = true := by rw [Nat.ble_eq]; omega
    have cv : Nat.beq (Nat.lor (Nat.lor (covL rest) (sepN L g)) a.s) L = true := by
      rw [Nat.beq_eq]
      refine Eq.trans ?_ (rep_cov hL R)
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [covL, lor_bit, hG]
      cases (covL rest).testBit i <;> cases (sepN L g).testBit i <;> cases a.s.testBit i <;> rfl
    rw [c1, flag_forced hy hb hA fla, cv, hr _ R]
    simp
  · have R : Rep L H mask (G :: b :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨hgb, hgr⟩, hbr, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact absurd (e2 ▸ hx) hA
          by_cases e3 : x = b.w
          · exact ⟨b, by simp, e3.symm⟩
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | rfl | hu
          · exact hg
          · exact hB
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · rfl
        · exact sepb
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · exact hfg
        · exact flb
        · exact flr u hu
    have hl := rep_len R
    simp only [List.length_cons] at hl
    have c1 : Nat.ble m (Nat.succ k) = true := by rw [Nat.ble_eq]; omega
    have cv : Nat.beq (Nat.lor (Nat.lor (covL rest) (sepN L g)) b.s) L = true := by
      rw [Nat.beq_eq]
      refine Eq.trans ?_ (rep_cov hL R)
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [covL, lor_bit, hG]
      cases (covL rest).testBit i <;> cases (sepN L g).testBit i <;> cases b.s.testBit i <;> rfl
    rw [c1, flag_forced hy hb hB flb, cv, hr _ R]
    simp
  · have R : Rep L H mask (G :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons]
        exact ⟨hgr, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact absurd (e2 ▸ hx) hA
          by_cases e3 : x = b.w
          · exact absurd (e3 ▸ hx) hB
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | hu
          · exact hg
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · rfl
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact hfg
        · exact flr u hu
    have cv : Nat.beq (Nat.lor (covL rest) (sepN L g)) L = true := by
      rw [Nat.beq_eq]
      refine Eq.trans ?_ (rep_cov hL R)
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [covL, lor_bit, hG]
      cases (covL rest).testBit i <;> cases (sepN L g).testBit i <;> rfl
    rw [cv, hr _ R]
    simp

lemma kills_cons (m : ℕ) (s : St) (l : List St) :
    kills m (s :: l) = kills m l + if killB m s = true then 1 else 0 := by
  rw [kills, kills, List.countP_cons]

lemma bud_next {H c1 c2 c3 K : ℕ} {mask : ℕ → ℕ} {s : St} {l : List St}
    (hb : Bud H mask c1 c2 c3 (s :: l))
    (hK : ∀ h, K.testBit h = true → h < H ∧ killB (mask h) s = true) :
    sub K c1 = true ∧ Bud H mask (Nat.lor c2 (Nat.xor c1 (Nat.land c1 K)))
      (Nat.lor c3 (Nat.xor c2 (Nat.land c2 K))) (Nat.xor c3 (Nat.land c3 K)) l := by
  constructor
  · refine sub_true fun h hh => ?_
    obtain ⟨h1, h2⟩ := hK h hh
    refine (hb h h1).2.1 ?_
    rw [kills_cons, if_pos h2]; omega
  · intro h hh
    obtain ⟨b0, b1, b2, b3⟩ := hb h hh
    rw [kills_cons] at b0 b1 b2 b3
    simp only [lor_bit, xor_bit, land_bit]
    cases hk : K.testBit h
    · refine ⟨by split_ifs at b0 <;> omega, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
      · rw [b1 (by omega)]; simp
      · rw [b2 (by omega)]; simp
      · rw [b3 (by omega)]; simp
    · rw [if_pos (hK h hk).2] at b0 b1 b2 b3
      refine ⟨by omega, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
      · rw [b2 (by omega)]; simp
      · rw [b3 (by omega)]; simp
      · omega

lemma tryP_true {L H y k : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    {r : Next} {v rest : List Wr} {a b : Wr} {s : St} {l : List St} {last c1 c2 c3 m : ℕ} (t : Fin 4)
    (ht : opN t a.w b.w = s.val) (hm : m = v.length)
    (hv : Rep L H mask v (insert a.w (insert b.w ((need y l).erase s.val))))
    (hp : v.Perm (a :: b :: rest)) (hg : s.val ∈ need y l) (hg0 : s.val ≠ 0) (hab : a.w ≠ b.w)
    (hgS : s.val ∉ insert a.w (insert b.w ((need y l).erase s.val)))
    (hcard : (need y l).card ≤ k + 1) (hord : a.w = last ∨ b.w = last ∨ last ≤ s.val)
    (hkill : ∀ m, Nat.land a.w m = 0 ∨ Nat.land b.w m = 0 → killB m s = true)
    (hb : Bud H mask c1 c2 c3 (s :: l))
    (hr : ∀ v' d1 d2 d3, Rep L H mask v' (need y l) → Bud H mask d1 d2 d3 l →
      r v' d1 d2 d3 s.val = true) :
    tryP L r k m c1 c2 c3 last a b rest = true := by
  have fla := hv.fl a (hp.mem_iff.mpr (by simp))
  have flb := hv.fl b (hp.mem_iff.mpr (by simp))
  have hK : ∀ h, (Nat.lor a.f b.f).testBit h = true → h < H ∧ killB (mask h) s = true := by
    intro h hh
    rw [lor_bit, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨(fla h hh).1, hkill _ (Or.inl (fla h hh).2)⟩
    · exact ⟨(flb h hh).1, hkill _ (Or.inr (flb h hh).2)⟩
  obtain ⟨b1, hb'⟩ := bud_next hb hK
  have b2 : sub (flL rest) (Nat.lor c2 (Nat.xor c1 (Nat.land c1 (Nat.lor a.f b.f)))) = true := by
    refine sub_true fun h hh => ?_
    rw [fl_bit, List.any_eq_true] at hh
    obtain ⟨u, hu, hf⟩ := hh
    have uv := hp.mem_iff.mpr (show u ∈ a :: b :: rest by simp [hu])
    obtain ⟨h1, h2⟩ := hv.fl u uv h hf
    refine (hb' h h1).2.1 (kill_forced (hy h h1) l ?_ h2)
    have hS := (hv.mem u.w).mpr ⟨u, uv, rfl⟩
    have nd2 : ((a :: b :: rest).map Wr.w).Nodup := (hp.map Wr.w).nodup_iff.mp hv.nd
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at nd2
    obtain ⟨⟨_, har⟩, hbr, _⟩ := nd2
    simp only [Finset.mem_insert, Finset.mem_erase] at hS
    rcases hS with e | e | ⟨_, e⟩
    · exact absurd (e ▸ List.mem_map_of_mem hu) har
    · exact absurd (e ▸ List.mem_map_of_mem hu) hbr
    · exact e
  have hord' : (Nat.beq a.w last || Nat.beq b.w last) = true ∨ last ≤ s.val := by
    rcases hord with h | h | h
    · left; rw [h, Nat.beq_refl]; rfl
    · left; rw [h, Nat.beq_refl]; exact Bool.or_true _
    · exact Or.inr h
  have G (fg : ℕ) (hfg : ∀ h, fg.testBit h = true → h < H ∧ Nat.land s.val (mask h) = 0) :=
    tryG_true (m := m) (last := last) (uses := Nat.beq a.w last || Nat.beq b.w last) (fg := fg)
      hy hL hm hv hp hg hg0 hab hgS hfg hcard hord' hb' (fun v' hv' => hr v' _ _ _ hv' hb')
  have z (c x : ℕ) : Nat.land (opN t a.w b.w) c = opN t (Nat.land a.w c) (Nat.land b.w c) :=
    land_op t _ _ c
  unfold tryP
  rw [force_eq, b1]
  simp only [cond_true, force_eq]
  rw [b2]
  simp only [cond_true]
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
  fin_cases t
  · left
    have e : Nat.land a.w b.w = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [lor_bit, Bool.or_eq_true] at hh
    rw [← ht]
    refine ⟨(hK h (by rw [lor_bit, Bool.or_eq_true]; exact hh)).1, ?_⟩
    rw [z _ 0]
    rcases hh with hh | hh
    · rw [(fla h hh).2]
      rcases opN_zero_left 0 (Nat.land b.w (mask h)) with e | e
      · exact e
      · apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
    · rw [(flb h hh).2]
      apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
  · right; left
    have e : Nat.lor a.w b.w = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [land_bit, Bool.and_eq_true] at hh
    rw [← ht]
    refine ⟨(fla h hh.1).1, ?_⟩
    rw [z _ 0, (fla h hh.1).2, (flb h hh.2).2]
    apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
  · right; right; left
    have e : Nat.xor a.w (Nat.land a.w b.w) = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [← ht]
    refine ⟨(fla h hh).1, ?_⟩
    rw [z _ 0, (fla h hh).2]
    apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
  · right; right; right
    have e : Nat.xor b.w (Nat.land a.w b.w) = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [← ht]
    refine ⟨(flb h hh).1, ?_⟩
    rw [z _ 0, (flb h hh).2]
    apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]

lemma level {L H y k : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    {r : Next} {W : Set ℕ} {v : List Wr} {s : St} {l : List St} {last c1 c2 c3 : ℕ}
    (hV : Valid y W (s :: l)) (h0 : 0 ∈ W) (hU : Useful y (s :: l)) (hk : (s :: l).length ≤ k + 1)
    (hC : Chain last (s :: l)) (hv : Rep L H mask v (need y (s :: l)))
    (hb : Bud H mask c1 c2 c3 (s :: l))
    (hr : ∀ v' d1 d2 d3, Rep L H mask v' (need y l) → Bud H mask d1 d2 d3 l →
      r v' d1 d2 d3 s.val = true) :
    anyP (tryP L r k (lenL v) c1 c2 c3 last) (pairsA [] v) = true := by
  obtain ⟨fa, fb, fab, fv, _, _, fS⟩ := step_facts hV h0
  obtain ⟨ua, hua, ea⟩ := (hv.mem s.a).mp (by simp [need])
  obtain ⟨ub, hub, eb⟩ := (hv.mem s.b).mp (by simp [need])
  have hne : ua ≠ ub := fun e => fab (by rw [← ea, ← eb, e])
  obtain ⟨rest, hmem, hperm⟩ := pairsA_spec ua ub hne v [] hua hub
  have hcard : (need y l).card ≤ k + 1 := by
    have := need_card l hU.2
    simp only [List.length_cons] at hk
    omega
  have hg := hU.1
  have eN : need y (s :: l) = insert s.a (insert s.b ((need y l).erase s.val)) := rfl
  rcases hmem with hm | hm
  · refine anyP_true hm (tryP_true hy hL s.t (by rw [ea, eb]; rfl) (lenL_eq v) ?_ hperm hg fv
      (by rw [ea, eb]; exact fab) ?_ hcard ?_ ?_ hb hr)
    · rw [ea, eb]; exact hv
    · rw [ea, eb]; exact fS
    · rw [ea, eb]; exact hC.1
    · intro m h
      rw [ea, eb] at h
      unfold killB
      rcases h with h | h
      · rw [h]; rfl
      · rw [h]; exact Bool.or_true _
  · have hv2 : Rep L H mask v (insert ub.w (insert ua.w ((need y l).erase s.val))) := by
      rw [ea, eb, Finset.insert_comm]; exact hv
    refine anyP_true hm (tryP_true hy hL (swapT s.t) ?_ (lenL_eq v) hv2
      (hperm.trans (List.Perm.swap ub ua rest)) hg fv (by rw [ea, eb]; exact fab.symm) ?_ hcard ?_ ?_
      hb hr)
    · rw [ea, eb, ← opN_swap]; rfl
    · rw [ea, eb, Finset.insert_comm]; exact fS
    · rw [ea, eb]
      rcases hC.1 with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · intro m h
      rw [ea, eb] at h
      unfold killB
      rcases h with h | h
      · rw [h]; exact Bool.or_true _
      · rw [h]; rfl

lemma isT_true {L H y : ℕ} {mask : ℕ → ℕ} {v : List Wr} (hv : Rep L H mask v (need y [])) :
    isT y v = true := by
  have hl := rep_len hv
  rw [need, Finset.card_singleton] at hl
  obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hl
  have : u.w ∈ need y [] := (hv.mem u.w).mpr ⟨u, by simp, rfl⟩
  rw [need, Finset.mem_singleton] at this
  rw [isT, this, Nat.beq_refl]

theorem search_complete {L H y : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i)) (k : ℕ) :
    ∀ (l : List St) (W : Set ℕ) (v : List Wr) (last c1 c2 c3 : ℕ), Valid y W l → 0 ∈ W →
      Useful y l → l.length ≤ k → Chain last l → Rep L H mask v (need y l) →
      Bud H mask c1 c2 c3 l → search L y k v c1 c2 c3 last = true := by
  induction k with
  | zero =>
    intro l W v last c1 c2 c3 hV h0 hU hk hC hv hb
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    exact isT_true hv
  | succ k ih =>
    intro l W v last c1 c2 c3 hV h0 hU hk hC hv hb
    rw [search, Bool.or_eq_true]
    cases l with
    | nil => exact Or.inl (isT_true hv)
    | cons s l =>
      refine Or.inr (level hy hL hV h0 hU hk hC hv hb fun v' d1 d2 d3 hv' hb' => ?_)
      exact ih l _ v' s.val d1 d2 d3 hV.2.2.2 (Or.inr h0) hU.2 (by simpa using hk) hC.2 hv' hb'

lemma need_ne_zero {y : ℕ} (hy : y ≠ 0) (l : List St) : ∀ {W : Set ℕ}, Valid y W l → 0 ∈ W →
    ∀ x ∈ need y l, x ≠ 0 := by
  induction l with
  | nil => intro W _ _ x hx; rw [need, Finset.mem_singleton] at hx; rw [hx]; exact hy
  | cons s l ih =>
    intro W h h0 x hx
    obtain ⟨fa, fb, _⟩ := step_facts h h0
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with rfl | rfl | ⟨_, h2⟩
    · exact fa
    · exact fb
    · exact ih h.2.2.2 (Or.inr h0) x h2

def neededB (L : ℕ) (ws : List Wr) : Bool :=
  ws.all fun u => !(Nat.beq (covL (ws.filter fun x => !(Nat.beq x.w u.w))) L)

lemma root_rep {L H y : ℕ} {mask : ℕ → ℕ}
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i)) (hy : y ≠ 0)
    {ws : List Wr} (hnd : (ws.map Wr.w).Nodup) (hs : ∀ u ∈ ws, u.s = sepN L u.w)
    (hf : ∀ u ∈ ws, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0)
    (hn : neededB L ws = true) {W : Set ℕ} {l : List St} (hV : Valid y W l) (h0 : 0 ∈ W)
    (hW : ∀ x ∈ W, x = 0 ∨ ∃ u ∈ ws, u.w = x) : Rep L H mask ws (need y l) := by
  have hsub : ∀ x ∈ need y l, ∃ u ∈ ws, u.w = x := fun x hx =>
    (hW x (need_sub l hV x hx)).resolve_left (need_ne_zero hy l hV h0 x hx)
  refine ⟨hnd, fun x => ⟨hsub x, ?_⟩, hs, hf⟩
  rintro ⟨u, hu, rfl⟩
  by_contra hc
  have hc1 := List.all_eq_true.mp hn u hu
  have hc2 : covL (ws.filter fun x => !(Nat.beq x.w u.w)) = L := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [cov_bit]
    cases hi : L.testBit i
    · rw [List.any_eq_false]
      intro q hq
      rw [hs q (List.mem_of_mem_filter hq), sepN_bit, hi]; simp
    · rw [List.any_eq_true]
      by_contra hd
      push Not at hd
      refine hL i hi (need_agree l fun x hx => ?_)
      obtain ⟨q, hq, rfl⟩ := hsub x hx
      have hne : q.w ≠ u.w := fun e => hc (e ▸ hx)
      have hq' : q ∈ ws.filter fun x => !(Nat.beq x.w u.w) := by
        rw [List.mem_filter]
        refine ⟨hq, ?_⟩
        have : Nat.beq q.w u.w = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hne
        rw [this]; rfl
      have := hd q hq'
      rw [hs q hq, sepN_bit, hi] at this
      cases h1 : q.w.testBit i <;> cases h2 : q.w.testBit (143 + i) <;> simp_all
  rw [hc2, Nat.beq_refl] at hc1
  exact Bool.false_ne_true hc1

theorem refute {L y K : ℕ} (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    (hy : y ≠ 0) {ws : List Wr} (hnd : (ws.map Wr.w).Nodup) (hs : ∀ u ∈ ws, u.s = sepN L u.w)
    (hf : ∀ u ∈ ws, u.f = 0) (hn : neededB L ws = true)
    (hsearch : search L y K ws 0 0 0 0 = false) {W : Set ℕ} (h0 : 0 ∈ W)
    (hW : ∀ x ∈ W, x = 0 ∨ ∃ u ∈ ws, u.w = x) : ¬ Der opN K W y := by
  intro h
  obtain ⟨l, hk, hV, hU, hC, _⟩ := exists_sorted h
  have hrep : Rep L 0 (fun _ => 0) ws (need y l) :=
    root_rep hL hy hnd hs (fun u hu h hh => by rw [hf u hu] at hh; simp at hh) hn hV h0 hW
  have := search_complete (H := 0) (mask := fun _ => 0) (fun h hh => by omega) hL K l W ws 0 0 0 0
    hV h0 hU hk hC hrep (fun h hh => by omega)
  rw [hsearch] at this
  exact Bool.false_ne_true this

lemma anyP_append (p : Wr → Wr → List Wr → Bool) (a b : List (Wr × Wr × List Wr)) :
    anyP p (a ++ b) = (anyP p a || anyP p b) := by
  induction a with
  | nil => rfl
  | cons x l ih => rw [List.cons_append, anyP, anyP, ih, Bool.or_assoc]

lemma anyP_chunks (p : Wr → Wr → List Wr → Bool) (m : ℕ) (n : ℕ) :
    ∀ l : List (Wr × Wr × List Wr), l.length ≤ m * n →
      (∀ i < n, anyP p ((l.drop (m * i)).take m) = false) → anyP p l = false := by
  induction n with
  | zero =>
    intro l hl _
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    rw [this]; rfl
  | succ n ih =>
    intro l hl h
    rw [← List.take_append_drop m l, anyP_append]
    have h1 := h 0 (by omega)
    rw [Nat.mul_zero, List.drop_zero] at h1
    rw [h1, Bool.false_or]
    refine ih _ (by rw [List.length_drop, Nat.mul_succ] at *; omega) fun i hi => ?_
    have := h (i + 1) (by omega)
    rw [List.drop_drop, show m + m * i = m * (i + 1) by ring]
    exact this

structure Kid where
  v : List Wr
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  g : ℕ

def eqL : List Wr → List Wr → Bool
  | [], [] => true
  | a :: l, b :: m => Nat.beq a.w b.w && (Nat.beq a.s b.s && (Nat.beq a.f b.f && eqL l m))
  | _, _ => false

lemma eqL_eq (a : List Wr) : ∀ b, eqL a b = true → a = b := by
  induction a with
  | nil => intro b h; cases b with
    | nil => rfl
    | cons => simp [eqL] at h
  | cons x l ih =>
    intro b h
    cases b with
    | nil => simp [eqL] at h
    | cons y m =>
      rw [eqL, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq,
        Nat.beq_eq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      rw [ih m h4]
      cases x; cases y
      simp only at h1 h2 h3
      rw [h1, h2, h3]

def isKid (v : List Wr) (c1 c2 c3 g : ℕ) : List Kid → Bool
  | [] => false
  | q :: l => (Nat.beq q.g g && (Nat.beq q.c1 c1 && (Nat.beq q.c2 c2 && (Nat.beq q.c3 c3 &&
      eqL q.v v)))) || isKid v c1 c2 c3 g l

lemma isKid_mem {v : List Wr} {c1 c2 c3 g : ℕ} (ks : List Kid)
    (h : isKid v c1 c2 c3 g ks = true) : ⟨v, c1, c2, c3, g⟩ ∈ ks := by
  induction ks with
  | nil => simp [isKid] at h
  | cons q l ih =>
    rw [isKid, Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have := eqL_eq _ _ h5
      cases q
      simp only at h1 h2 h3 h4 this
      subst h1 h2 h3 h4 this
      simp
    · exact List.mem_cons_of_mem _ (ih h)

def memN (g : ℕ) : List ℕ → Bool
  | [] => false
  | x :: l => Nat.beq x g || memN g l

def rootNext (al : List ℕ) (ks : List Kid) : Next := fun v c1 c2 c3 g =>
  cond (memN g al) (!(isKid v c1 c2 c3 g ks)) false

def Bdd (N x : ℕ) : Prop := ∀ i, N ≤ i → x.testBit i = false

lemma bdd_op {N : ℕ} (t : Fin 4) {a b : ℕ} (ha : Bdd N a) (hb : Bdd N b) : Bdd N (opN t a b) := by
  intro i hi
  rw [opN_bit, ha i hi, hb i hi]
  fin_cases t <;> rfl

def sIdx (T : ℕ) (i : ℕ) : ℕ :=
  cond (Nat.blt i 143) (Nat.land (Nat.shiftRight T (8 * i)) 255)
    (143 + Nat.land (Nat.shiftRight T (8 * (i - 143))) 255)

def sg (N T : ℕ) (w : ℕ) : ℕ := Nat.ofBits fun i : Fin N => w.testBit (sIdx T i.val)

lemma sg_bit (N T w i : ℕ) (hi : i < N) : (sg N T w).testBit i = w.testBit (sIdx T i) := by
  rw [sg, Nat.testBit_ofBits_lt _ _ hi]

lemma sg_bdd (N T w : ℕ) : Bdd N (sg N T w) := fun i hi => by rw [sg, Nat.testBit_ofBits_ge _ _ hi]

lemma sg_op (N T : ℕ) (t : Fin 4) (a b : ℕ) : sg N T (opN t a b) = opN t (sg N T a) (sg N T b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · rw [sg_bit _ _ _ _ hi, opN_bit, opN_bit, sg_bit _ _ _ _ hi, sg_bit _ _ _ _ hi]
  · rw [sg_bdd _ _ _ i (by omega), bdd_op t (sg_bdd N T a) (sg_bdd N T b) i (by omega)]

lemma sg_sg {N : ℕ} (T : ℕ) (hT : ∀ i < N, sIdx T i < N ∧ sIdx T (sIdx T i) = i) {w : ℕ} (hw : Bdd N w) :
    sg N T (sg N T w) = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · rw [sg_bit _ _ _ _ hi, sg_bit _ _ _ _ (hT i hi).1, (hT i hi).2]
  · rw [sg_bdd _ _ _ i (by omega), hw i (by omega)]

def mapSt (N T : ℕ) (s : St) : St := ⟨s.t, sg N T s.a, sg N T s.b⟩

lemma mapSt_val (N T : ℕ) (s : St) : (mapSt N T s).val = sg N T s.val := (sg_op N T _ _ _).symm

lemma valid_map {N : ℕ} (T : ℕ) (hT : ∀ i < N, sIdx T i < N ∧ sIdx T (sIdx T i) = i) {y : ℕ}
    (l : List St) : ∀ {W : Set ℕ}, (∀ x ∈ W, Bdd N x) → Valid y W l →
      Valid (sg N T y) (sg N T '' W) (l.map (mapSt N T)) := by
  induction l with
  | nil => intro W _ h; exact ⟨y, h, rfl⟩
  | cons s l ih =>
    intro W hb h
    obtain ⟨ha, hb', hc, hv⟩ := h
    have bv : Bdd N s.val := bdd_op s.t (hb _ ha) (hb _ hb')
    refine ⟨⟨s.a, ha, rfl⟩, ⟨s.b, hb', rfl⟩, ?_, ?_⟩
    · rw [mapSt_val]
      rintro ⟨x, hx, e⟩
      have := congrArg (sg N T) e
      rw [sg_sg T hT (hb x hx), sg_sg T hT bv] at this
      exact hc (this ▸ hx)
    · rw [mapSt_val, ← Set.image_insert_eq]
      refine ih ?_ hv
      rintro x (rfl | hx)
      · exact bv
      · exact hb x hx

lemma sg_eq {N T x x' : ℕ} (hx' : Bdd N x') (h : ∀ i < N, x'.testBit i = x.testBit (sIdx T i)) :
    sg N T x = x' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · rw [sg_bit _ _ _ _ hi, h i hi]
  · rw [sg_bdd _ _ _ i (by omega), hx' i (by omega)]

lemma bdd_of_lt {N x : ℕ} (h : x < 2 ^ N) : Bdd N x := fun i hi =>
  Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hi))

def LO : ℕ := 0x7fffffffffffffffffffffffffffffffffff

def ipL : List ℕ := [0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f]

def ip (i : Fin 7) : ℕ := ipL.getD i.val 0

def maskL : List ℕ := [0x78f1e3c78f1e3c58a850404fffffffffffffffffffff01fc00000000000ffffffffffff, 0x39f3e7cf9f3e7cfa75ffffffad9022fffffffffffff80fe0000003ffffff000000ffffff, 0xe1c3870e1c38707fe005fffd26fff802ffffffffc07ffe03f8ffc001fff001fff000fff, 0x1ab56ad5ab56ad58fe2ff2bf87f0ffa5faaf80fe03ffffffffb1fc1fe03f0fe0ff03f00f, 0x3a74e9d3a74e9d3b7f7afbfb18f38f8e78faff01fffff01ffff6fce1e7c031e70f1cf1f0, 0x274e9d3a74e9d3af9fd33d63fb7fdd5a9d59fffe03f80fffffdf3f2678c7f6eb30253233, 0x35ebd7af5ebd7affa7ffadcdffbf71ffd7750001fc07ffffffff4fde1b1bff74c3d80cc0]

def mask (h : ℕ) : ℕ := maskL.getD h 0

private def vertexRows0 : Nat := 0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc
private def vertexRows1 : Nat := 0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0
private def vertexRows2 : Nat := 0x3163398ce62c58800080020000148a900880
private def vertexRows3 : Nat := 0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000
private def vertexRows4 : Nat := 0x3594d654a952a50000400540000100480550
private def vertexRows5 : Nat := 0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000
private def vertexRows6 : Nat := 0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f
private def vertexRows7 : Nat := 0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000
private def vertexRows8 : Nat := 0x63c78ce63c6731800000a000a4c000005000
private def vertexRows9 : Nat := 0x6bd6535942850a0000214080000a2027a22a
private def vertexRows10 : Nat := 0x70e1c38701fc078b150a0809000000000000
private def vertexRows11 : Nat := 0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f

def root : List Wr := [⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

def pm (p : Fin 3) (i : Fin 7) : Fin 7 :=
  match p with
  | 0 => ![3, 6, 2, 0, 5, 4, 1] i
  | 1 => ![4, 6, 2, 5, 0, 3, 1] i
  | 2 => ![5, 1, 2, 4, 3, 0, 6] i

def Tn (p : Fin 3) : ℕ :=
  match p with
  | 0 => 0x5d585a5b595c57726d6f706e716c6b666869676a65645f616260635e87828485838681807b7d7e7c7f7a797476777578738e898b8c8a8d884515123a3736082309212005044746494856171614132e2f2c2d3938533c3b5251240b0a2207063f403d3e110e0f10270c0d354f324d4c02031a1b1c1d00014443554241542b28292a252634334e5031304b4a1e1f1819
  | 1 => 0x6c6d6f706e717257585a5b595c5d7a7b7d7e7c7f805e5f616260636488898b8c8a8d8e65666869676a6b73747677757879818284858386871115103503023223091d1c0100434416172b484941422e2f292a3334240a0b1e1f533b3c5030313f400e0f453d3e12270c0d3a4f081a1b36374d4c2021040546475513142856542c2d252638394e220607181952514b4a
  | 2 => 0x81868584838287888d8c8b8a898e656a696867666b73787776757479575c5b5a59585d7a7f7e7d7c7b805e636261605f646c71706f6e6d722b5528241e1f224f4e1a1b1819161743441146471314403f0f0e0a0b35333403023a38390806072f2e2a29562d2c542726255323501d1c515221204c4d4a4b48491541421045123e3d0d0c3b3c09323031010037360504

def allowed : List ℕ := [0x3ffffc000000000000000000, 0x1fc07000000000ffe000000000, 0xfe00009031e183f000000000000, 0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c, 0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000, 0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000, 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000, 0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00, 0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f, 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f, 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f, 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf, 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff, 0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f, 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000, 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc]

def L0 : ℕ := 0xf1e3c78f003c00000000000ffffffffffff
def Y0 : ℕ := 0x7ffffffff01fc00000000000ffffffffffff
def ws0 : List Wr := [⟨0x60c183060c183058a000000526fdd00000000000007f01fc00000000000ffffff000000, 0xc1830603000c000000000005b2045000000, 0⟩, ⟨0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x3060c603003000000000000a4c000005000, 0⟩, ⟨0x50a142850a1428500800400780f005a05507f01fc000000000000000000f01f00fc0ff0, 0x5141450a002800000000000000100480550, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0xb082c58b002c00000000000000010000005, 0⟩, ⟨0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x1023808e00040000000000000148a900880, 0⟩, ⟨0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0xb1610584001000000000000000a2027a22a, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub0 : search L0 Y0 7 ws0 0 0 0 0 = false := by decide +kernel

def L1 : ℕ := 0x73e7cf980e60000003ffffff000000ffffff
def Y1 : ℕ := 0x7ffffff80fe0000003ffffff000000ffffff
def ws1 : List Wr := [⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe0000003ffffff000000000000, 0x70e1c38000600000010a0809000000000000, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f80000000003ffe000000000fff000, 0x63c78c800c6000000000a000000000005000, 0⟩, ⟨0x2142850a142850a201d00d402800005a05507f01fc000000000003e01fc0000000fc0ff0, 0x3184c6100840000000400540000000480550, 0⟩, ⟨0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x3e00c180e00000002141036000000000005, 0⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc000000000000d98738000000dacdcc, 0x316309880620000000800200000000900880, 0⟩, ⟨0x8102040810204005000523200000200288afffe03f8000000000021e4e400000027f33f, 0x63c64318020000000021408000000027a22a, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub1 : search L1 Y1 6 ws1 0 0 0 0 = false := by decide +kernel

def L2 : ℕ := 0x1c387001c3800e0ffc001fff001fff000fff
def Y2 : ℕ := 0x7ffffc07ffe03f8ffc001fff001fff000fff
def ws2 : List Wr := [⟨0x81020408102040274005bfb000000000000000000000fe03f8ffc001fff000000000000, 0x102040010180060b14000809000000000000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0xc18300101800804e8000000000045000000, 0⟩, ⟨0x40810204081020700000d40500f000005507f01fc000000000e00001fc0001f00000ff0, 0x141050008100040000000540000100000550, 0⟩, ⟨0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x82820008280040000001036000010000005, 0⟩, ⟨0x8102040810204006000429c0000228022a60001fc07f0000000c00007380014cf000dcc, 0x10203000c20008000000020000148a000880, 0⟩, ⟨0xa142850a14285005800523200408e00288afffe000000000000b00004e4000b3c00033f, 0x810500142800a0000000080000a2000022a, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub2 : search L2 Y2 7 ws2 0 0 0 0 = false := by decide +kernel

def L3 : ℕ := 0x6a01ab56ad5ab1fc1fe03f0fe0ff03f00f
def Y3 : ℕ := 0xfe03ffffffffb1fc1fe03f0fe0ff03f00f
def ws3 : List Wr := [⟨0x183060c183060c18742af2bb000000000000000000000fe03fb1fc1fe03f000000000000, 0x60018300ac0281140a0009000000000000, 0⟩, ⟨0x2040810204081008a0000000260dd00000000000007f01fffb1fc0000000fe0ff000000, 0x80023108c58b0e80000000b2045000000, 0⟩, ⟨0x10a142850a142858002fa00005900025d000000003f8001fc030001fe0000fe00003f000, 0x4200a2142510800000a00004c000005000, 0⟩, ⟨0x810204081020408005000487007021820500fe00000fe00001001e003f0e00f003000f, 0x6800081680408000140036000010000005, 0⟩, ⟨0x18b162c58b162c50602cc29c048022a562a600000007f0000020c01980380900cf02c00c, 0x620188462c58800000000000008a000000, 0⟩, ⟨0xa142850a14285005800523200408e00288a80fe03f800000000b001e02400803c03f00f, 0x42010942850a000001400000002003a00a, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub3 : search L3 Y3 7 ws3 0 0 0 0 = false := by decide +kernel

def L4 : ℕ := 0x7401d3a7401d3a76fce1e7c031e70f1cf1f0
def Y4 : ℕ := 0x7f01fffff01ffff6fce1e7c031e70f1cf1f0
def ws4 : List Wr := [⟨0x3870e1c3870e1c3a757afbfb0000000000000000000000003ff6fce1e7c0000000000000, 0x7001c387001c020214000000000000000000, 0⟩, ⟨0x2040810204081010a00000010638d00000000000007f01ffff6fc00000031e70f000000, 0x4001027001c3874e8000000112005000000, 0⟩, ⟨0x3060c183060c1838017aa0000890000e5000000003f8001fc07000e1e00031e0001cf000, 0x600180a6000530000000a00020c000005000, 0⟩, ⟨0x2040810204081023015009401803000a00507f01fc000000004600e007c03007001c01f0, 0x3400d2040010200000400540000100080150, 0⟩, ⟨0x183060c183060c106028c2980080028460a20001fc07f0000020c0c1870001040f18c1c0, 0x30011184400c18000080020000040a100080, 0⟩, ⟨0xa142850a14285005800523200408e00288aff0003f800000000b021e4c000830c04f130, 0x6000530140050a000021408000020004a020, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub4 : search L4 Y4 7 ws4 0 0 0 0 = false := by decide +kernel

def L5 : ℕ := 0x4e9c027009d3a75f3f2678c7f6eb30253233
def Y5 : ℕ := 0x7ffe03f80fffffdf3f2678c7f6eb30253233
def ws5 : List Wr := [⟨0x204081020408102a15523963000000000000000000000fe03fdf3f2678c7000000000000, 0x4080020001d0070b15020801000000000000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0xc1800600190a15428000000522000000000, 0⟩, ⟨0x2142850a142850a801d320002910005a9000000003f8001fc05003266000f6e000253000, 0x428400600843210000002000a4c000001000, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f0000000000004e032018c0f00b00240230, 0x49402500952a50000000040000100000010, 0⟩, ⟨0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0xa8800500882850002041006000010000001, 0⟩, ⟨0x2040810204081001800102200408c000808fffe03f800000000302060c4008b30253233, 0x4a9402500081020000204080000a20252222, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub5 : search L5 Y5 7 ws5 0 0 0 0 = false := by decide +kernel

def L6 : ℕ := 0x1ac06bd7af5ff4fde1b1bff74c3d80cc0
def Y6 : ℕ := 0x1fc07ffffffff4fde1b1bff74c3d80cc0
def ws6 : List Wr := [⟨0x3060c183060c183a257aa9c9000000000000000000000fe03fff4fde1b1b000000000000, 0x180060178058b050a0809000000000000, 0⟩, ⟨0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x20063118f1f4480000005b2041000000, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x18c063c62318000000000a44000000000, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05500001fc000000004e03c01b00f01400d80cc0, 0x8404a952a50000400100000000480440, 0⟩, ⟨0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0x2c00bc02c58002141012000000000000, 0⟩, ⟨0x10a142850a142850202c808c048020a542240001fc07f000002040d803180914c3d80cc0, 0x12804a428508000800200001482900880, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub6 : search L6 Y6 6 ws6 0 0 0 0 = false := by decide +kernel

def kids : List Kid := [
  ⟨[⟨0x3ffffc000000000000000000, 0x3ffffc000000000000000000, 3⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 126, 64, 0x3ffffc000000000000000000⟩,
  ⟨[⟨0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x3060fe0307f0180010a0000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 122, 66, 0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000⟩,
  ⟨[⟨0xfe00009031e183f000000000000, 0xfe00009031e183f000000000000, 17⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 110, 66, 0xfe00009031e183f000000000000⟩,
  ⟨[⟨0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0xbe82c58b162c589010a0809000010000005, 16⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 110, 66, 0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f⟩,
  ⟨[⟨0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x103f80fe02040800008000800148a900880, 32⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 94, 66, 0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc⟩,
  ⟨[⟨0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0x7bf613d84081020010000000000a2027a22a, 64⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩], 127, 126, 2, 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f⟩,
  ⟨[⟨0x1fc07000000000ffe000000000, 0x1fc07000000000ffe000000000, 6⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 123, 64, 0x1fc07000000000ffe000000000⟩,
  ⟨[⟨0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000, 0x6fdfbc810de40804e800a000000045005000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 123, 64, 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000⟩,
  ⟨[⟨0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0xc18306731833984e8000000a4c045000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 123, 64, 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000⟩,
  ⟨[⟨0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000, 0x810204081020400000000004a0050000000, 18⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 111, 64, 0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000⟩,
  ⟨[⟨0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f, 0xfe03c7f0e1c3874ea141036112005000005, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 111, 64, 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f⟩,
  ⟨[⟨0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x3f80c183f80c180021410364a0040000005, 16⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 111, 64, 0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f⟩,
  ⟨[⟨0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0xc183060c19cf9d42800000052348a000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 95, 64, 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000⟩,
  ⟨[⟨0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000, 0x408102040810200a0000000000a24000000, 66⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 127, 0, 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000⟩,
  ⟨[⟨0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f, 0x63c6731e3398f1f4482140805b204127a22a, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 127, 0, 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f⟩,
  ⟨[⟨0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x8102047711dfbf4480000005b2a61000000, 2⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 127, 0, 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000⟩,
  ⟨[⟨0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000, 0x3060c183060c18002140000840000000000, 20⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 107, 66, 0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000⟩,
  ⟨[⟨0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f, 0x6b29aca6b28535800000b03620c010005005, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 107, 66, 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f⟩,
  ⟨[⟨0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x8ee20408ee2040000001036840010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 107, 66, 0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f⟩,
  ⟨[⟨0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x63c78f1e3c67318000214000a4400027a000, 4⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 123, 2, 0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000⟩,
  ⟨[⟨0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00, 0xa142850a142850002001000000000400400, 24⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 103, 66, 0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00⟩,
  ⟨[⟨0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff, 0x3468d25cb692e58000540576000110080155, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 103, 66, 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff⟩,
  ⟨[⟨0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc, 0x4f613d84f7efd800000004000018a000010, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 87, 66, 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc⟩,
  ⟨[⟨0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c, 0x10204081020408000100030001080800804, 48⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 79, 66, 0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c⟩,
  ⟨[⟨0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf, 0x3b8911dc488edd800284120600041a100081, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 79, 66, 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf⟩,
  ⟨[⟨0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0xaea2850aea2850002041006001090800801, 16⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩], 127, 79, 66, 0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203⟩,
  ⟨[⟨0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f, 0x60c07f01fc07cf800235509200020004a020, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 111, 2, 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f⟩,
  ⟨[⟨0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0xb162c58be82c5800214101200082023020a, 16⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩], 127, 111, 2, 0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootSearch : anyP (tryP LO (rootNext allowed kids) 9 (lenL root) 127 127 66 0) (pairsA [] root) = false := by decide +kernel

def kv0 : List Wr := [⟨0x3ffffc000000000000000000, 0x3ffffc000000000000000000, 3⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid0 : search LO LO 9 kv0 127 126 64 0x3ffffc000000000000000000 = false := by decide +kernel

def kv1 : List Wr := [⟨0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x3060fe0307f0180010a0000a4c000005000, 4⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid1 : search LO LO 9 kv1 127 122 66 0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000 = false := by decide +kernel

def kv2 : List Wr := [⟨0xfe00009031e183f000000000000, 0xfe00009031e183f000000000000, 17⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid2 : search LO LO 9 kv2 127 110 66 0xfe00009031e183f000000000000 = false := by decide +kernel

def kv3 : List Wr := [⟨0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0xbe82c58b162c589010a0809000010000005, 16⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid3 : search LO LO 9 kv3 127 110 66 0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f = false := by decide +kernel

def kv4 : List Wr := [⟨0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x103f80fe02040800008000800148a900880, 32⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid4 : search LO LO 9 kv4 127 94 66 0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc = false := by decide +kernel

def kv5 : List Wr := [⟨0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0x7bf613d84081020010000000000a2027a22a, 64⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows11, vertexRows9, 64⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid5_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 residualMask2) (((pairsA [] kv5).drop (6 * 0)).take 6) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid5_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 residualMask2) (((pairsA [] kv5).drop (6 * 1)).take 6) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid5_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 residualMask2) (((pairsA [] kv5).drop (6 * 2)).take 6) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid5_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 residualMask2) (((pairsA [] kv5).drop (6 * 3)).take 6) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid5_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 residualMask2) (((pairsA [] kv5).drop (6 * 4)).take 6) = false := by decide +kernel

theorem kid5 : search LO LO 9 kv5 127 126 2 residualMask2 = false := by
  have h1 : isT LO kv5 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f) (pairsA [] kv5) = false := by
    refine anyP_chunks _ 6 5 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid5_0
    · exact kid5_1
    · exact kid5_2
    · exact kid5_3
    · exact kid5_4
  rw [search, h1, h2]; rfl

def kv6 : List Wr := [⟨0x1fc07000000000ffe000000000, 0x1fc07000000000ffe000000000, 6⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid6 : search LO LO 9 kv6 127 123 64 0x1fc07000000000ffe000000000 = false := by decide +kernel

def kv7 : List Wr := [⟨0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000, 0x6fdfbc810de40804e800a000000045005000, 0⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 residualMask5) (((pairsA [] kv7).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid7 : search LO LO 9 kv7 127 123 64 residualMask5 = false := by
  have h1 : isT LO kv7 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (pairsA [] kv7) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid7_0
    · exact kid7_1
    · exact kid7_2
    · exact kid7_3
    · exact kid7_4
    · exact kid7_5
    · exact kid7_6
    · exact kid7_7
    · exact kid7_8
    · exact kid7_9
    · exact kid7_10
    · exact kid7_11
    · exact kid7_12
    · exact kid7_13
    · exact kid7_14
    · exact kid7_15
    · exact kid7_16
    · exact kid7_17
    · exact kid7_18
    · exact kid7_19
    · exact kid7_20
    · exact kid7_21
    · exact kid7_22
    · exact kid7_23
    · exact kid7_24
    · exact kid7_25
    · exact kid7_26
    · exact kid7_27
  rw [search, h1, h2]; rfl

def kv8 : List Wr := [⟨0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0xc18306731833984e8000000a4c045000000, 2⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 residualMask9) (((pairsA [] kv8).drop (5 * 0)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 residualMask9) (((pairsA [] kv8).drop (5 * 1)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 residualMask9) (((pairsA [] kv8).drop (5 * 2)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 residualMask9) (((pairsA [] kv8).drop (5 * 3)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 residualMask9) (((pairsA [] kv8).drop (5 * 4)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 residualMask9) (((pairsA [] kv8).drop (5 * 5)).take 5) = false := by decide +kernel

theorem kid8 : search LO LO 9 kv8 127 123 64 residualMask9 = false := by
  have h1 : isT LO kv8 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000) (pairsA [] kv8) = false := by
    refine anyP_chunks _ 5 6 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid8_0
    · exact kid8_1
    · exact kid8_2
    · exact kid8_3
    · exact kid8_4
    · exact kid8_5
  rw [search, h1, h2]; rfl

def kv9 : List Wr := [⟨0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000, 0x810204081020400000000004a0050000000, 18⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid9 : search LO LO 9 kv9 127 111 64 0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000 = false := by decide +kernel

def kv10 : List Wr := [⟨0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f, 0xfe03c7f0e1c3874ea141036112005000005, 0⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 residualMask10) (((pairsA [] kv10).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid10 : search LO LO 9 kv10 127 111 64 residualMask10 = false := by
  have h1 : isT LO kv10 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (pairsA [] kv10) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid10_0
    · exact kid10_1
    · exact kid10_2
    · exact kid10_3
    · exact kid10_4
    · exact kid10_5
    · exact kid10_6
    · exact kid10_7
    · exact kid10_8
    · exact kid10_9
    · exact kid10_10
    · exact kid10_11
    · exact kid10_12
    · exact kid10_13
    · exact kid10_14
    · exact kid10_15
    · exact kid10_16
    · exact kid10_17
    · exact kid10_18
    · exact kid10_19
    · exact kid10_20
    · exact kid10_21
    · exact kid10_22
    · exact kid10_23
    · exact kid10_24
    · exact kid10_25
    · exact kid10_26
    · exact kid10_27
  rw [search, h1, h2]; rfl

def kv11 : List Wr := [⟨0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x3f80c183f80c180021410364a0040000005, 16⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid11 : search LO LO 9 kv11 127 111 64 0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f = false := by decide +kernel

def kv12 : List Wr := [⟨0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0xc183060c19cf9d42800000052348a000000, 2⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 residualMask8) (((pairsA [] kv12).drop (5 * 0)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 residualMask8) (((pairsA [] kv12).drop (5 * 1)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 residualMask8) (((pairsA [] kv12).drop (5 * 2)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 residualMask8) (((pairsA [] kv12).drop (5 * 3)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 residualMask8) (((pairsA [] kv12).drop (5 * 4)).take 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 residualMask8) (((pairsA [] kv12).drop (5 * 5)).take 5) = false := by decide +kernel

theorem kid12 : search LO LO 9 kv12 127 95 64 residualMask8 = false := by
  have h1 : isT LO kv12 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000) (pairsA [] kv12) = false := by
    refine anyP_chunks _ 5 6 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid12_0
    · exact kid12_1
    · exact kid12_2
    · exact kid12_3
    · exact kid12_4
    · exact kid12_5
  rw [search, h1, h2]; rfl

def kv13 : List Wr := [⟨0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000, 0x408102040810200a0000000000a24000000, 66⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows11, vertexRows9, 64⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows5, vertexRows10, 1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 residualMask1) (((pairsA [] kv13).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid13 : search LO LO 9 kv13 127 127 0 residualMask1 = false := by
  have h1 : isT LO kv13 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (pairsA [] kv13) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid13_0
    · exact kid13_1
    · exact kid13_2
    · exact kid13_3
    · exact kid13_4
    · exact kid13_5
    · exact kid13_6
    · exact kid13_7
    · exact kid13_8
    · exact kid13_9
    · exact kid13_10
    · exact kid13_11
    · exact kid13_12
    · exact kid13_13
    · exact kid13_14
    · exact kid13_15
    · exact kid13_16
    · exact kid13_17
    · exact kid13_18
    · exact kid13_19
    · exact kid13_20
    · exact kid13_21
    · exact kid13_22
    · exact kid13_23
    · exact kid13_24
    · exact kid13_25
    · exact kid13_26
    · exact kid13_27
  rw [search, h1, h2]; rfl

def kv14 : List Wr := [⟨0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f, 0x63c6731e3398f1f4482140805b204127a22a, 0⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows11, vertexRows9, 64⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows5, vertexRows10, 1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 residualMask11) (((pairsA [] kv14).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid14 : search LO LO 9 kv14 127 127 0 residualMask11 = false := by
  have h1 : isT LO kv14 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (pairsA [] kv14) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid14_0
    · exact kid14_1
    · exact kid14_2
    · exact kid14_3
    · exact kid14_4
    · exact kid14_5
    · exact kid14_6
    · exact kid14_7
    · exact kid14_8
    · exact kid14_9
    · exact kid14_10
    · exact kid14_11
    · exact kid14_12
    · exact kid14_13
    · exact kid14_14
    · exact kid14_15
    · exact kid14_16
    · exact kid14_17
    · exact kid14_18
    · exact kid14_19
    · exact kid14_20
    · exact kid14_21
    · exact kid14_22
    · exact kid14_23
    · exact kid14_24
    · exact kid14_25
    · exact kid14_26
    · exact kid14_27
  rw [search, h1, h2]; rfl

def kv15 : List Wr := [⟨0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x8102047711dfbf4480000005b2a61000000, 2⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows11, vertexRows9, 64⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows5, vertexRows10, 1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 residualMask7) (((pairsA [] kv15).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid15 : search LO LO 9 kv15 127 127 0 residualMask7 = false := by
  have h1 : isT LO kv15 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (pairsA [] kv15) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid15_0
    · exact kid15_1
    · exact kid15_2
    · exact kid15_3
    · exact kid15_4
    · exact kid15_5
    · exact kid15_6
    · exact kid15_7
    · exact kid15_8
    · exact kid15_9
    · exact kid15_10
    · exact kid15_11
    · exact kid15_12
    · exact kid15_13
    · exact kid15_14
    · exact kid15_15
    · exact kid15_16
    · exact kid15_17
    · exact kid15_18
    · exact kid15_19
    · exact kid15_20
    · exact kid15_21
    · exact kid15_22
    · exact kid15_23
    · exact kid15_24
    · exact kid15_25
    · exact kid15_26
    · exact kid15_27
  rw [search, h1, h2]; rfl

def kv16 : List Wr := [⟨0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000, 0x3060c183060c18002140000840000000000, 20⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid16 : search LO LO 9 kv16 127 107 66 0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000 = false := by decide +kernel

def kv17 : List Wr := [⟨0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f, 0x6b29aca6b28535800000b03620c010005005, 0⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 residualMask4) (((pairsA [] kv17).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid17 : search LO LO 9 kv17 127 107 66 residualMask4 = false := by
  have h1 : isT LO kv17 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (pairsA [] kv17) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid17_0
    · exact kid17_1
    · exact kid17_2
    · exact kid17_3
    · exact kid17_4
    · exact kid17_5
    · exact kid17_6
    · exact kid17_7
    · exact kid17_8
    · exact kid17_9
    · exact kid17_10
    · exact kid17_11
    · exact kid17_12
    · exact kid17_13
    · exact kid17_14
    · exact kid17_15
    · exact kid17_16
    · exact kid17_17
    · exact kid17_18
    · exact kid17_19
    · exact kid17_20
    · exact kid17_21
    · exact kid17_22
    · exact kid17_23
    · exact kid17_24
    · exact kid17_25
    · exact kid17_26
    · exact kid17_27
  rw [search, h1, h2]; rfl

def kv18 : List Wr := [⟨0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x8ee20408ee2040000001036840010000005, 16⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid18 : search LO LO 9 kv18 127 107 66 0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f = false := by decide +kernel

def kv19 : List Wr := [⟨0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x63c78f1e3c67318000214000a4400027a000, 4⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows11, vertexRows9, 64⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows5, vertexRows10, 1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid19 : search LO LO 9 kv19 127 123 2 0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000 = false := by decide +kernel

def kv20 : List Wr := [⟨0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00, 0xa142850a142850002001000000000400400, 24⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid20 : search LO LO 9 kv20 127 103 66 0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00 = false := by decide +kernel

def kv21 : List Wr := [⟨0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff, 0x3468d25cb692e58000540576000110080155, 0⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 residualMask3) (((pairsA [] kv21).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid21 : search LO LO 9 kv21 127 103 66 residualMask3 = false := by
  have h1 : isT LO kv21 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (pairsA [] kv21) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid21_0
    · exact kid21_1
    · exact kid21_2
    · exact kid21_3
    · exact kid21_4
    · exact kid21_5
    · exact kid21_6
    · exact kid21_7
    · exact kid21_8
    · exact kid21_9
    · exact kid21_10
    · exact kid21_11
    · exact kid21_12
    · exact kid21_13
    · exact kid21_14
    · exact kid21_15
    · exact kid21_16
    · exact kid21_17
    · exact kid21_18
    · exact kid21_19
    · exact kid21_20
    · exact kid21_21
    · exact kid21_22
    · exact kid21_23
    · exact kid21_24
    · exact kid21_25
    · exact kid21_26
    · exact kid21_27
  rw [search, h1, h2]; rfl

def kv22 : List Wr := [⟨0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc, 0x4f613d84f7efd800000004000018a000010, 0⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 residualMask6) (((pairsA [] kv22).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid22 : search LO LO 9 kv22 127 87 66 residualMask6 = false := by
  have h1 : isT LO kv22 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (pairsA [] kv22) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid22_0
    · exact kid22_1
    · exact kid22_2
    · exact kid22_3
    · exact kid22_4
    · exact kid22_5
    · exact kid22_6
    · exact kid22_7
    · exact kid22_8
    · exact kid22_9
    · exact kid22_10
    · exact kid22_11
    · exact kid22_12
    · exact kid22_13
    · exact kid22_14
    · exact kid22_15
    · exact kid22_16
    · exact kid22_17
    · exact kid22_18
    · exact kid22_19
    · exact kid22_20
    · exact kid22_21
    · exact kid22_22
    · exact kid22_23
    · exact kid22_24
    · exact kid22_25
    · exact kid22_26
    · exact kid22_27
  rw [search, h1, h2]; rfl

def kv23 : List Wr := [⟨0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c, 0x10204081020408000100030001080800804, 48⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid23 : search LO LO 9 kv23 127 79 66 0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c = false := by decide +kernel

def kv24 : List Wr := [⟨0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf, 0x3b8911dc488edd800284120600041a100081, 0⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 residualMask0) (((pairsA [] kv24).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid24 : search LO LO 9 kv24 127 79 66 residualMask0 = false := by
  have h1 : isT LO kv24 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (pairsA [] kv24) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid24_0
    · exact kid24_1
    · exact kid24_2
    · exact kid24_3
    · exact kid24_4
    · exact kid24_5
    · exact kid24_6
    · exact kid24_7
    · exact kid24_8
    · exact kid24_9
    · exact kid24_10
    · exact kid24_11
    · exact kid24_12
    · exact kid24_13
    · exact kid24_14
    · exact kid24_15
    · exact kid24_16
    · exact kid24_17
    · exact kid24_18
    · exact kid24_19
    · exact kid24_20
    · exact kid24_21
    · exact kid24_22
    · exact kid24_23
    · exact kid24_24
    · exact kid24_25
    · exact kid24_26
    · exact kid24_27
  rw [search, h1, h2]; rfl

def kv25 : List Wr := [⟨0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0xaea2850aea2850002041006001090800801, 16⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows5, vertexRows10, 1⟩, ⟨vertexRows11, vertexRows9, 64⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid25 : search LO LO 9 kv25 127 79 66 0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203 = false := by decide +kernel

def kv26 : List Wr := [⟨0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f, 0x60c07f01fc07cf800235509200020004a020, 0⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows11, vertexRows9, 64⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows5, vertexRows10, 1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_0 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 0)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_1 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 1)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 2)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_3 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 3)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_4 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 4)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_5 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 5)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_6 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 6)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_7 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 7)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_8 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 8)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_9 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 9)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_10 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 10)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_11 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 11)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_12 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 12)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_13 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 13)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_14 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 14)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_15 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 15)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_16 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 16)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_17 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 17)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_18 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 18)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_19 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 19)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_20 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 20)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_21 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 21)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_22 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 22)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_23 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 23)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_24 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 24)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_25 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 25)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_26 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 26)).take 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26_27 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 residualMask12) (((pairsA [] kv26).drop (1 * 27)).take 1) = false := by decide +kernel

theorem kid26 : search LO LO 9 kv26 127 111 2 residualMask12 = false := by
  have h1 : isT LO kv26 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (pairsA [] kv26) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid26_0
    · exact kid26_1
    · exact kid26_2
    · exact kid26_3
    · exact kid26_4
    · exact kid26_5
    · exact kid26_6
    · exact kid26_7
    · exact kid26_8
    · exact kid26_9
    · exact kid26_10
    · exact kid26_11
    · exact kid26_12
    · exact kid26_13
    · exact kid26_14
    · exact kid26_15
    · exact kid26_16
    · exact kid26_17
    · exact kid26_18
    · exact kid26_19
    · exact kid26_20
    · exact kid26_21
    · exact kid26_22
    · exact kid26_23
    · exact kid26_24
    · exact kid26_25
    · exact kid26_26
    · exact kid26_27
  rw [search, h1, h2]; rfl

def kv27 : List Wr := [⟨0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0xb162c58be82c5800214101200082023020a, 16⟩, ⟨vertexRows6, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨vertexRows11, vertexRows9, 64⟩, ⟨vertexRows0, vertexRows2, 32⟩, ⟨vertexRows1, vertexRows4, 8⟩, ⟨vertexRows3, vertexRows8, 4⟩, ⟨vertexRows7, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨vertexRows5, vertexRows10, 1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid27 : search LO LO 9 kv27 127 111 2 0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00 = false := by decide +kernel

theorem kids_false : ∀ q ∈ kids, search LO LO 9 q.v q.c1 q.c2 q.c3 q.g = false := by
  intro q hq
  simp only [kids, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kid0
  · exact kid1
  · exact kid2
  · exact kid3
  · exact kid4
  · exact kid5
  · exact kid6
  · exact kid7
  · exact kid8
  · exact kid9
  · exact kid10
  · exact kid11
  · exact kid12
  · exact kid13
  · exact kid14
  · exact kid15
  · exact kid16
  · exact kid17
  · exact kid18
  · exact kid19
  · exact kid20
  · exact kid21
  · exact kid22
  · exact kid23
  · exact kid24
  · exact kid25
  · exact kid26
  · exact kid27

def okL (L y : ℕ) : Bool :=
  Nat.blt L (2 ^ 143) && (List.range 143).all fun i => !(L.testBit i) || (y.testBit i != y.testBit (143 + i))

lemma okL_spec {L y : ℕ} (h : okL L y = true) (i : ℕ) (hi : L.testBit i = true) :
    y.testBit i ≠ y.testBit (143 + i) := by
  rw [okL, Bool.and_eq_true] at h
  have hlt : i < 143 := by
    by_contra hc
    have h1 : L < 2 ^ 143 := by simpa [Nat.blt_eq] using h.1
    have := Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (not_lt.mp hc)))
    rw [this] at hi
    exact Bool.false_ne_true hi
  have h2 := List.all_eq_true.mp h.2 i (List.mem_range.mpr hlt)
  rw [hi] at h2
  simpa using h2

def W0 : Set ℕ := {x | x = 0 ∨ ∃ i : Fin 7, x = ip i}

def LB (h : ℕ) : ℕ := [8, 7, 8, 8, 8, 8, 7].getD h 0

lemma subW (h : ℕ) (ws : List Wr)
    (hc : ∀ i : Fin 7, Nat.land (ip i) (mask h) = 0 ∨ ∃ u ∈ ws, u.w = Nat.land (ip i) (mask h))
    {W : Set ℕ} (hW : ∀ x ∈ W, x = 0 ∨ ∃ i : Fin 7, x = Nat.land (ip i) (mask h)) :
    ∀ x ∈ W, x = 0 ∨ ∃ u ∈ ws, u.w = x := by
  intro x hx
  rcases hW x hx with e | ⟨i, e⟩
  · exact Or.inl e
  · rw [e]; exact hc i

theorem subBound (h : ℕ) (hh : h < 7) {W : Set ℕ} (h0 : 0 ∈ W)
    (hW : ∀ x ∈ W, x = 0 ∨ ∃ i : Fin 7, x = Nat.land (ip i) (mask h)) :
    ¬ Der opN (LB h - 1) W (Nat.land LO (mask h)) := by
  interval_cases h
  · exact refute (L := L0) (y := Y0) (ws := ws0) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub0 h0
      (subW 0 ws0 (by decide +kernel) hW)
  · exact refute (L := L1) (y := Y1) (ws := ws1) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub1 h0
      (subW 1 ws1 (by decide +kernel) hW)
  · exact refute (L := L2) (y := Y2) (ws := ws2) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub2 h0
      (subW 2 ws2 (by decide +kernel) hW)
  · exact refute (L := L3) (y := Y3) (ws := ws3) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub3 h0
      (subW 3 ws3 (by decide +kernel) hW)
  · exact refute (L := L4) (y := Y4) (ws := ws4) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub4 h0
      (subW 4 ws4 (by decide +kernel) hW)
  · exact refute (L := L5) (y := Y5) (ws := ws5) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub5 h0
      (subW 5 ws5 (by decide +kernel) hW)
  · exact refute (L := L6) (y := Y6) (ws := ws6) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub6 h0
      (subW 6 ws6 (by decide +kernel) hW)

lemma root_ip : ∀ i : Fin 7, ∃ u ∈ root, u.w = ip i := by decide +kernel

lemma ip_lt : ∀ i : Fin 7, ip i < 2 ^ 286 := by decide +kernel

lemma LO_lt : LO < 2 ^ 286 := by decide +kernel

lemma Tn_inv : ∀ p : Fin 3, ∀ i : Fin 286,
    sIdx (Tn p) i.val < 286 ∧ sIdx (Tn p) (sIdx (Tn p) i.val) = i.val := by decide +kernel

lemma Tn_ip : ∀ p : Fin 3, ∀ i : Fin 7, ∀ r : Fin 286,
    (ip (pm p i)).testBit r.val = (ip i).testBit (sIdx (Tn p) r.val) := by decide +kernel

lemma Tn_LO : ∀ p : Fin 3, ∀ r : Fin 286,
    LO.testBit r.val = LO.testBit (sIdx (Tn p) r.val) := by decide +kernel

lemma pm_inv : ∀ p : Fin 3, ∀ i : Fin 7, pm p (pm p i) = i := by decide

lemma allowed_spec : ∀ t : Fin 4, ∀ i j : Fin 7, i ≠ j →
    (∀ p : Fin 3, opN t (ip i) (ip j) ≤ opN t (ip (pm p i)) (ip (pm p j))) →
    memN (opN t (ip i) (ip j)) allowed = true := by decide +kernel

lemma sg_ip (p : Fin 3) (i : Fin 7) : sg 286 (Tn p) (ip i) = ip (pm p i) :=
  sg_eq (bdd_of_lt (ip_lt _)) fun r hr => Tn_ip p i ⟨r, hr⟩

lemma sg_LO (p : Fin 3) : sg 286 (Tn p) LO = LO :=
  sg_eq (bdd_of_lt LO_lt) fun r hr => Tn_LO p ⟨r, hr⟩

lemma sg_zero (N T : ℕ) : sg N T 0 = 0 :=
  sg_eq (fun i _ => Nat.zero_testBit i) fun r _ => by rw [Nat.zero_testBit, Nat.zero_testBit]

lemma sg_W0 (p : Fin 3) : sg 286 (Tn p) '' W0 = W0 := by
  ext x
  constructor
  · rintro ⟨w, rfl | ⟨i, rfl⟩, rfl⟩
    · exact Or.inl (sg_zero _ _)
    · exact Or.inr ⟨pm p i, sg_ip p i⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, Or.inl rfl, sg_zero _ _⟩
    · exact ⟨ip (pm p i), Or.inr ⟨pm p i, rfl⟩, by rw [sg_ip, pm_inv]⟩

lemma bdd_W0 : ∀ x ∈ W0, Bdd 286 x := by
  rintro x (rfl | ⟨i, rfl⟩)
  · exact fun i _ => Nat.zero_testBit i
  · exact bdd_of_lt (ip_lt i)

theorem theta : ¬ Der opN 10 W0 LO := by
  intro h
  obtain ⟨l, hk, hV, hU, hC, hmin⟩ := exists_sorted h
  have h0 : (0 : ℕ) ∈ W0 := Or.inl rfl
  have hLO : LO ≠ 0 := by decide +kernel
  have hL : ∀ i, LO.testBit i = true → LO.testBit i ≠ LO.testBit (143 + i) :=
    fun i hi => okL_spec (L := LO) (y := LO) (by decide +kernel) i hi
  have caps : ∀ h < 7, kills (mask h) l + LB h ≤ 10 := by
    intro h hh
    obtain ⟨n, hn, hd⟩ := der_masked (m := mask h) l hV h0
    by_contra hc
    have hLB : 1 ≤ LB h := by interval_cases h <;> decide
    refine subBound h hh (W := (fun w => Nat.land w (mask h)) '' W0) ⟨0, h0, by simp [Nat.land]⟩ ?_
      (hd.le (by omega))
    rintro _ ⟨w, rfl | ⟨i, rfl⟩, rfl⟩
    · left; show Nat.land 0 (mask h) = 0; simp [Nat.land]
    · exact Or.inr ⟨i, rfl⟩
  have hy : ∀ h < 7, Nat.land LO (mask h) ≠ 0 := by
    intro h hh
    have key : ∀ h : Fin 7, Nat.land LO (mask h.val) ≠ 0 := by decide +kernel
    exact key ⟨h, hh⟩
  have hfl : ∀ u ∈ root, ∀ h, u.f.testBit h = true → h < 7 ∧ Nat.land u.w (mask h) = 0 := by
    have k1 : ∀ u ∈ root, u.f < 2 ^ 7 := by decide +kernel
    have k2 : ∀ u ∈ root, ∀ h : Fin 7, u.f.testBit h.val = true → Nat.land u.w (mask h.val) = 0 := by
      decide +kernel
    intro u hu h hb
    have hlt : h < 7 := by
      by_contra hc
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le (k1 u hu)
        (Nat.pow_le_pow_right (by omega) (not_lt.mp hc)))
      rw [this] at hb
      exact Bool.false_ne_true hb
    exact ⟨hlt, k2 u hu ⟨h, hlt⟩ hb⟩
  have hrep : Rep LO 7 mask root (need LO l) := by
    refine root_rep hL hLO (by decide +kernel) (by decide +kernel) hfl (by decide +kernel) hV h0 ?_
    rintro x (rfl | ⟨i, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (root_ip i)
  have hbud : Bud 7 mask 127 127 66 l := by
    intro h hh
    have c := caps h hh
    interval_cases h <;> simp only [LB, List.getD_cons_zero, List.getD_cons_succ] at c <;>
      refine ⟨by omega, fun _ => by decide, fun _ => by decide, fun h3 => ?_⟩ <;>
      first | (exfalso; omega) | decide
  cases l with
  | nil =>
    have e : ∀ i : Fin 7, LO ≠ ip i := by decide +kernel
    rcases hV with h | ⟨i, h⟩
    · exact hLO h
    · exact e i h
  | cons s l =>
    have al : memN s.val allowed = true := by
      obtain ⟨fa, fb, fab, _⟩ := step_facts hV h0
      rcases hV.1 with e | ⟨i, ei⟩
      · exact absurd e fa
      rcases hV.2.1 with e | ⟨j, ej⟩
      · exact absurd e fb
      have hs : s.val = opN s.t (ip i) (ip j) := by rw [St.val, ei, ej]
      rw [hs]
      refine allowed_spec s.t i j (fun e => fab (by rw [ei, ej, e])) fun p => ?_
      have vm := valid_map (Tn p) (fun i hi => Tn_inv p ⟨i, hi⟩) (s :: l) bdd_W0 hV
      rw [sg_LO, sg_W0] at vm
      have := hmin _ vm (by simp)
      change s.val ≤ (mapSt 286 (Tn p) s).val at this
      rw [mapSt_val, hs, sg_op, sg_ip, sg_ip] at this
      exact this
    have := level (k := 9) (r := rootNext allowed kids) hy hL hV h0 hU (by simpa using hk) hC hrep hbud ?_
    · rw [rootSearch] at this
      exact Bool.false_ne_true this
    · intro v' d1 d2 d3 hv' hb'
      show cond (memN s.val allowed) (!(isKid v' d1 d2 d3 s.val kids)) false = true
      rw [al, cond_true]
      cases hkid : isKid v' d1 d2 d3 s.val kids
      · rfl
      · have hm := kids_false _ (isKid_mem kids hkid)
        have hs := search_complete hy hL 9 l _ v' s.val d1 d2 d3 hV.2.2.2 (Or.inr h0) hU.2
          (by simp only [List.length_cons] at hk; omega) hC.2 hv' hb'
        simp only at hm
        rw [hm] at hs
        exact absurd hs Bool.false_ne_true

end CoTheta3174Public

namespace CoThetaPacked4358

open CoTheta3174Public CoThetaNine CoThetaFreeCore

private def position (j : Fin 7) : Fin 7 := ![1,6,2,0,4,5,3] j

private def packedRows : Nat := 0x262c55441d4693162aa20ea3498b15510751a4c58aa883a8d262c55441d4693162aa20ea3498b15510751a4c58aa883a8d262c194644122a940a06200cca93164c58d061458a860a9141548512052a50c05082146a4188d0894480c084a3460c10645811060d1014151a54889223428911040541850450104004c1110050a142850a14224489122448960c183060c1803060c183060c850a142850a13060c183060c050a142850a144891224489133568db32649956a458b1226e5cd9b273c7870e2e5c38758b1ab4689529d387068c18ab562c56a54aa50e142f1a7861c362c4993468d0a1e9d2b64c919b164c98306e1c2962c18214264c8912

private def sample (r : Fin 286) : SmallInput :=
  ⟨(packedRows >>> (7*r.val)) % 128, Nat.mod_lt _ (by decide)⟩

private def code (f : SmallInput → Bool) : Nat :=
  Nat.ofBits fun r : Fin 286 => f (sample r)

private def tag : Kind → Fin 4
  | .conj => 0
  | .disj => 1
  | .leftOnly => 2
  | .rightOnly => 3

private theorem onBits (t : Kind) (a b : Bool) :
    applyKind t a b = opB (tag t) a b := by
  cases t <;> cases a <;> cases b <;> rfl

private theorem bounded (f : SmallInput → Bool) : Bdd 286 (code f) :=
  fun i hi => Nat.testBit_ofBits_ge _ _ hi

private theorem code_bit (f : SmallInput → Bool) (i : Nat) (hi : i < 286) :
    (code f).testBit i = f (sample ⟨i,hi⟩) := by
  rw [code, Nat.testBit_ofBits_lt _ _ hi]

private theorem code_op (t : Kind) (f g : SmallInput → Bool) :
    code (fun x => applyKind t (f x) (g x)) = opN (tag t) (code f) (code g) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 286
  · rw [opN_bit]
    rw [code_bit _ _ hi, code_bit _ _ hi, code_bit _ _ hi]
    exact onBits t _ _
  · rw [bounded _ i (by omega), bdd_op (tag t) (bounded f) (bounded g) i (by omega)]

set_option maxRecDepth 8192 in
private theorem zero_code : code (absentBit : SmallInput → Bool)=0 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem raw_codes : ∀ j : Fin 7, code (raw7 j)=ip (position j) := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem answer_code : code ans7=LO := by decide +kernel

private def pool (ws : List (SmallInput → Bool)) : Set Nat :=
  {v | ∃ f∈ws, code f=v}

private theorem start_pool : pool vertices7 ⊆ W0 := by
  rintro v ⟨f,hf,rfl⟩
  rcases List.mem_cons.mp hf with rfl | hh
  · exact Or.inl zero_code
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
    exact Or.inr ⟨position i,raw_codes i⟩

private theorem run_der {n ws} (run : Free vertices7 n ws) {y : Nat} :
    ∀ {k : Nat}, Der opN k (pool ws) y → Der opN (k+n) (pool vertices7) y := by
  induction run with
  | start => intro k d; simpa using d
  | @binary n ws a b pre t ha hb ih =>
    intro k d
    have subset : pool ((fun i => applyKind t (a i) (b i)) :: ws) ⊆
        insert (opN (tag t) (code a) (code b)) (pool ws) := by
      rintro v ⟨f, hf, rfl⟩
      rcases List.mem_cons.mp hf with rfl | hw
      · exact Or.inl (code_op t a b)
      · exact Or.inr ⟨f,hw,rfl⟩
    have da : code a ∈ pool ws := ⟨a,ha,rfl⟩
    have db : code b ∈ pool ws := ⟨b,hb,rfl⟩
    have step := Der.step (tag t) (code a) (code b) da db (d.mono subset)
    have eq : k+(n+1)=(k+1)+n := by omega
    rw [eq]
    exact ih step

theorem lower : CoThetaNine.SignedLower := by
  intro n ws run output
  by_contra small
  have last : Der opN 0 (pool ws) (code ans7) := Der.here ⟨ans7,output,rfl⟩
  have program := (run_der run last).mono start_pool
  rw [answer_code] at program
  exact CoTheta3174Public.theta (program.le (by omega))

end CoThetaPacked4358
namespace CoThetaSeven

theorem checked_lower : CoThetaNine.SignedLower := CoThetaPacked4358.lower

end CoThetaSeven

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
def allAt (p : Nat→Bool) (beginning : Nat) : Nat → Bool
  | 0 => true
  | size+1 => allAt p beginning size && p (beginning+size)

theorem allAt_get {p : Nat → Bool} {b n : Nat} (h : allAt p b n = true) (i : Nat)
    (lo : b ≤ i) (hi : i < b + n) : p i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have checks := Bool.and_eq_true_iff.mp h
    by_cases l : i<b+n
    · exact ih checks.1 l
    · have e : i=b+n := by omega
      simpa [e] using checks.2

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

def options : List Bool := [false,true]

theorem all_options (b : Bool) : b∈options := by cases b <;> simp [options]

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

def emit (w : W) : Nat := (w.1.toNat<<<4) ||| (w.2.2.original.toNat<<<3) |||
  (w.2.1.original.toNat<<<2) ||| (w.2.2.separates.toNat<<<1) ||| w.2.1.separates.toNat

def read (n : Nat) : W :=
  (BitVec.ofNat 15 (n>>>4),(⟨n.testBit 2,n.testBit 0⟩,⟨n.testBit 3,n.testBit 1⟩))

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

namespace CoNum4358.Tiny.Reflection
open CoAO3143

set_option maxRecDepth 65536 in
def order : Fin 15 → Fin 15 := ![7,4,5,6,1,2,3,0,8,14,11,10,12,13,9]
set_option maxRecDepth 65536 in
def reverseK (w : K) : K :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 15 => w.getLsbD (order i).val))).cast List.length_ofFn

set_option maxRecDepth 65536 in
theorem reverse_bit (w : K) (i : Fin 15) : (reverseK w).getLsbD i.val=w.getLsbD (order i).val := by
  rw [reverseK,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  have bd : i.val<(List.ofFn (fun j : Fin 15 => w.getLsbD (order j).val)).length := by simpa using i.isLt
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bd]
  exact List.getElem_ofFn bd

set_option maxRecDepth 65536 in
theorem invol (w : K) : reverseK (reverseK w)=w := by
  have inv : ∀i : Fin 15,order (order i)=i := by decide +kernel
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 15 := ⟨j,hj⟩
  change (reverseK (reverseK w)).getLsbD i.val=w.getLsbD i.val
  rw [reverse_bit,reverse_bit,inv]

set_option maxRecDepth 65536 in
theorem injK : Function.Injective reverseK := Function.LeftInverse.injective invol

set_option maxRecDepth 65536 in
theorem op (d : Bool) (a b : K) : reverseK (makeKW d a b)=makeKW d (reverseK a) (reverseK b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 15 := ⟨j,hj⟩
  change (reverseK (makeKW d a b)).getLsbD i.val=(makeKW d (reverseK a) (reverseK b)).getLsbD i.val
  cases d <;> simp only [reverse_bit,makeKW,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,BitVec.getLsbD_or]

set_option maxRecDepth 65536 in
theorem constants : reverseK 0=0 ∧ reverseK 32767=32767 ∧ reverseK 255=255 ∧ reverseK 7442=7442 := by
  decide +kernel

set_option maxRecDepth 65536 in
theorem raw_fixed : (bare.map reverseK).toFinset=bare.toFinset := by decide +kernel

set_option maxRecDepth 65536 in
def wire (w : W) : W := (reverseK w.1,(w.2.2,w.2.1))
set_option maxRecDepth 65536 in
theorem wire_invol (w : W) : wire (wire w)=w := by
  rcases w with ⟨s,a,b⟩
  change (reverseK (reverseK s),(a,b))=(s,(a,b))
  rw [invol]
set_option maxRecDepth 65536 in
theorem wire_inj : Function.Injective wire := Function.LeftInverse.injective wire_invol

set_option maxRecDepth 65536 in
theorem combine (d : Bool) (a b : W) : wire (make d a b)=make d (wire a) (wire b) :=
  Prod.ext (op d a.1 b.1) rfl

set_option maxRecDepth 65536 in
private theorem read_fee (w : K) : (reverseK w==7442)=(w==7442) := by
  by_cases eq : w=7442
  · subst w
    exact (beq_iff_eq.mpr constants.2.2.2).trans (beq_iff_eq.mpr rfl).symm
  · have m : reverseK w≠7442 := fun z => eq (injK (z.trans constants.2.2.2.symm))
    have a : (reverseK w==7442)=false := Bool.eq_false_iff.mpr (fun h => m (beq_iff_eq.mp h))
    have b : (w==7442)=false := Bool.eq_false_iff.mpr (fun h => eq (beq_iff_eq.mp h))
    exact a.trans b.symm
set_option maxRecDepth 65536 in
theorem price (d : Bool) (u v : W) : pay d (wire u) (wire v)=pay d u v := by
  simp only [pay,wire,read_fee]

set_option maxRecDepth 65536 in
def Represented (a : Sig) := ∃t : K,wide t=a
set_option maxRecDepth 65536 in
noncomputable def renameSig (a : Sig) := wide (reverseK (Function.invFun wide a))

set_option maxRecDepth 65536 in
theorem rename_wide (a : K) : renameSig (wide a)=wide (reverseK a) := by
  rw [renameSig,Function.leftInverse_invFun wide_inj a]

set_option maxRecDepth 65536 in
private theorem faithful {a b : Sig} (ma : Represented a) (mb : Represented b)
    (eq : renameSig a=renameSig b) : a=b := by
  obtain ⟨x,rfl⟩ := ma
  obtain ⟨y,rfl⟩ := mb
  rw [rename_wide,rename_wide] at eq
  exact congrArg wide (injK (wide_inj eq))

set_option maxRecDepth 65536 in
private theorem preserves_proper {a : Sig} (ma : Represented a) (h : proper a) : proper (renameSig a) := by
  have ez : renameSig zero=zero := by rw [←zero_value,rename_wide,constants.1]
  have eo : renameSig one=one := by rw [←one_value,rename_wide,constants.2.1]
  exact ⟨fun eq => h.1 (faithful ma ⟨0,zero_value⟩ (eq.trans ez.symm)),
    fun eq => h.2 (faithful ma ⟨32767,one_value⟩ (eq.trans eo.symm))⟩

set_option maxRecDepth 65536 in
private theorem preserves_bin (d : Bool) {a b : Sig} (ma : Represented a) (mb : Represented b) :
    Represented (bin d a b) ∧ renameSig (bin d a b)=bin d (renameSig a) (renameSig b) := by
  obtain ⟨x,rfl⟩ := ma
  obtain ⟨y,rfl⟩ := mb
  exact ⟨⟨makeKW d x y,wide_bin d x y⟩,by rw [←wide_bin,rename_wide,rename_wide,rename_wide,op,wide_bin]⟩

set_option maxRecDepth 65536 in
theorem mirror_live {k t S} (h : Live k t S) (hz : t=0) (all : ∀v∈S,Represented v) :
    Live k 0 (S.image renameSig) := by
  induction h with
  | stop =>
    have fixed : renameSig target=target := by rw [←target_value,rename_wide,constants.2.2.1]
    simpa [fixed] using (Live.stop : Live 0 0 {target})
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb ne fresh tail ih =>
    have ma : Represented a := all _ (by simp)
    have mb : Represented b := all _ (by simp)
    have bz := preserves_bin d ma mb
    have mu (u : Sig) (hu : u∈U) : Represented u := all u (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    have child := ih hz (fun u hu => by
      obtain eq|old := Finset.mem_insert.mp hu
      · rw [eq]; exact bz.1
      · exact mu u old)
    simp only [Finset.image_insert,bz.2] at child ⊢
    apply Live.binary (preserves_proper ma ha) (preserves_proper mb hb)
      (fun e => ne (faithful ma mb e)) _ child
    intro bad
    rw [←bz.2,←Finset.image_insert,←Finset.image_insert] at bad
    obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp bad
    exact fresh (by simpa only [faithful (all _ hv) bz.1 eq] using hv)

set_option maxRecDepth 65536 in
theorem good {k : Nat} {S : Finset W} (h : Good k S) : Good k (S.image wire) := by
  constructor
  · have live := mirror_live h.live rfl (fun v hv => by
      obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨w.1,rfl⟩)
    have sets : (S.image (fun w => wide w.1)).image renameSig=(S.image wire).image (fun w=>wide w.1) := by
      simp only [Finset.image_image,Function.comp_def,wire,rename_wide]
    rwa [←sets]
  · intro s
    obtain ⟨w,hw,hits⟩ := h.caps (!s)
    exact ⟨wire w,Finset.mem_image_of_mem _ hw,by cases s <;> exact hits⟩

set_option maxRecDepth 65536 in
theorem trace {k q S} (h : Trace k q S) : Trace k q (S.image wire) := by
  induction h with
  | done q w a b c =>
    simp only [Finset.image_singleton]
    exact Trace.done q (wire w) (by change reverseK w.1=255; rw [a,constants.2.2.1]) c b
  | @step k q U d a b ne budget clean unused raw facts child ih =>
    have ori : ∀t : K,reverseK t∈bare → t∈bare := by
      intro t ht
      have m : reverseK (reverseK t)∈(bare.map reverseK).toFinset := by
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨reverseK t,ht,rfl⟩)
      simpa only [invol,raw_fixed,List.mem_toFinset] using m
    have eq : (make d (wire a) (wire b)).1=reverseK (make d a b).1 :=
      congrArg Prod.fst (combine d a b).symm
    have source := good facts
    simp only [Finset.image_insert] at source ⊢
    simp only [Finset.image_insert,combine] at ih
    apply Trace.step d (wire a) (wire b) (fun h => ne (wire_inj h)) (by rwa [price]) _ _ _
      source (by simpa only [price] using ih)
    · rw [eq]
      exact ⟨fun e=>clean.1 (injK (e.trans constants.1.symm)),
        fun e=>clean.2 (injK (e.trans constants.2.1.symm))⟩
    · intro bad
      rw [eq,←Finset.image_insert,←Finset.image_insert] at bad
      obtain ⟨w,hw,ev⟩ := Finset.mem_image.mp bad
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact unused (Finset.mem_image.mpr ⟨v,hv,injK ev⟩)
    · rw [eq]
      exact fun e=>raw (ori _ e)

end CoNum4358.Tiny.Reflection

namespace CoNum4358.Direct

structure Pack where
  bits : Nat
  words : Array Nat
def Pack.val (x : Pack) (i : Nat) := (x.words[i/32]?.getD 0 >>> (x.bits*(i % 32))) % 2^x.bits
def blank : Pack := ⟨0,#[]⟩

structure Tier where
  count : Nat
  groups : Nat
  index : Pack
  base : Array Nat
  keys : Array Pack
structure Data where
  dict : Pack
  starts : Pack
  layers : Array Tier

def roots : List Nat := [31234,91208,119072,139448,299089,361092,396548]
def getTier (d : Data) (k : Nat) : Tier := d.layers[k]?.getD ⟨0,0,blank,#[],#[]⟩

def lower (ok : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0,lo,_ => lo
  | fuel+1,lo,hi => if lo≥hi then lo else
    let m := (lo+hi)/2
    if ok m then lower ok fuel lo m else lower ok fuel (m+1) hi

def column (t : Tier) (n index : Nat) :=
  (t.keys[n]?.getD blank).val (index-(t.base[n]?.getD 0))

def rawNumber (v : Nat) : Nat :=
  if v==31234 then 0 else if v==91208 then 1 else if v==119072 then 2 else
  if v==139448 then 3 else if v==299089 then 4 else if v==361092 then 5 else
  if v==396548 then 6 else 7

def decodeExtras (dict : Pack) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,key => dict.val (key % 2048)::decodeExtras dict n (key>>>11)

def rawPart (raw : Nat) := (List.range 7).filterMap fun j =>
  if raw.testBit j then roots[j]? else none

def row (d : Data) (k i : Nat) : Nat × List Nat :=
  let t := getTier d k
  let g := lower (fun j => decide (t.index.val j>>>11>i)) 16 0 t.groups - 1
  let tagWord := t.index.val g % 2048
  let n := tagWord>>>8
  (tagWord % 2,rawPart ((tagWord>>>1) % 128) ++ decodeExtras d.dict n (column t n i))

def dictID (d : Data) (v : Nat) : Nat :=
  let b := v>>>10
  let lo := d.starts.val b
  let hi := d.starts.val (b+1)
  lower (fun j => decide (d.dict.val j≥v)) 12 lo hi

def insertID (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y::ys => if x≤y then x::y::ys else y::insertID x ys

def encodeExtras (xs : List Nat) :=
  (xs.foldr insertID []).foldr (fun x n => (n<<<11) ||| x) 0

def place (d : Data) (k q : Nat) (words : List Nat) : Nat :=
  let t := getTier d k
  let split := words.foldl (fun (v : Nat×List Nat) w =>
    let j := rawNumber w
    if j<7 then (v.1 ||| (1<<<j),v.2) else (v.1,dictID d w::v.2)) (0,[])
  let n := split.2.length
  let tag := q+2*split.1+256*n
  let g := lower (fun i => decide (t.index.val i % 2048≥tag)) 16 0 t.groups
  let found := t.index.val g
  if g≥t.groups || found % 2048 != tag then t.count else
    let hi := if g+1<t.groups then t.index.val (g+1)>>>11 else t.count
    let key := encodeExtras split.2
    let i := lower (fun j => decide (column t n j≥key)) 16 (found>>>11) hi
    if i<hi && column t n i==key then i else t.count

end CoNum4358.Direct

namespace CoNum4358.WordRows
open Direct (Pack rawPart)

structure Tier where
  total : Nat
  cuts : Array Nat
  header : Pack
  extras : Array Pack
  edgeStart : Pack
  edgeList : Pack

def blank : Tier := ⟨0,#[0,0,0,0,0,0,0],⟨0,#[]⟩,#[],⟨0,#[]⟩,⟨0,#[]⟩⟩
def bound (t : Tier) (n : Nat) := t.cuts[n]?.getD t.total

def width (t : Tier) (i : Nat) :=
  if i<bound t 2 then (if i<bound t 1 then 0 else 1)
  else if i<bound t 4 then (if i<bound t 3 then 2 else 3)
  else if i<bound t 5 then 4 else 5

def unroll : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,c => (c % 524288)::unroll n (c>>>19)

def row (t : Tier) (i : Nat) : Nat × List Nat :=
  let h := t.header.val i
  let n := width t i
  let items := (t.extras[n]?.getD ⟨0,#[]⟩).val (i-bound t n)
  (h % 2,rawPart (h>>>1) ++ unroll n items)

def seek (es : Pack) (code : Nat) : Nat → Nat → Nat
  | 0,_ => 1048576
  | fuel+1,i =>
    let e := es.val i
    if e>>>10==code then e % 1024 else seek es code fuel (i+1)

def locate (t : Tier) (i code : Nat) :=
  let start := t.edgeStart.val i
  let stop := t.edgeStart.val (i+1)
  seek t.edgeList code (stop-start) start
end CoNum4358.WordRows

namespace CoNum4358.WordRows.Orbits
def p3 : Direct.Pack := ⟨5,#[0xa4ea00016c7340000062204a000000]⟩
def p4 : Direct.Pack := ⟨7,#[0x3674e000000487100000000000000000000000000000001820200000,0x74e1cb76ad8000000000000000000000811243478e2c4ca152e2858c,0x24479b38000952400000017b360c5934]⟩
def p5 : Direct.Pack := ⟨8,#[0x100,0x6050a0b0809000000000021201e1f1a191b1c1d0e161715100f131211141800,0x5800000000000000000000000000000000383a39434204030d0c3637000007,0x696a6b68675e5d5c747300005452534f5150570000000000000000000000,0x929300009b000000000000000000000056665b7f55656163626460595a818000,0x9799989a9695aaaba9a2a3a100000094a6009d9e000000]⟩
def p6 : Direct.Pack := ⟨9,#[0xe11058080200078341c00030000000000000805018000000000000000,0x481c0e8a80000000000000000000000,0x2090880441d8f07e3e1e89c4c2f00000000000000003a1c8e00000000000000000000000,0x351a4d86b279380063321889248251148e46108806000000000000338000000000000043,0xa85329140a27a3299850291108c36371a8d86833190c44a1f0f208006d,0x0,0x17cbf5daf578a45329544a350a6da200000000000000000000000000000000000000,0x620000000000000000000000000000000000000000000000000000000000000000000000,0x7e3f5fcff7dbddf4f1783bde6f6793d5e8f87cbb1dced,0x4559acc65b1d8cca64b218aae55ab558e573391c0df71b89c2c0000000000000000000,0x8b3419ece5d2e56ab15b2cd70b7592d160af75ba9d2e873a9e43228fc763d20000000140,0x1178c46e35195027d389e4eb0d84c1552a5512892c8e4927935128742,0xc56270581cd6640000c6e3b0f85c35f2f77ac46000000000000000000000000000000000,0x5ff198bc260efb7e]⟩
def p7 : Direct.Pack := ⟨10,#[0x2c07018180641705800000000000400c02004000000000005000000000000000000000000000000,0x400f0440e0240a0200c,0x4200040,0x14c5200000000000000000000000000000000000000000000000000000000000000000,0x5e1705d1805f1605a16c5715859150550e42d11c4600000000000000000000,0x1843a0bc2e1244800000000000000000000000000000000000000aa000001f400000000000000000,0x2c4af2b8ad2b07f1f800000000000000000000000009f2789c2746b1a46a1b0671a0651906319862,0xec350d0360cc320c4300a829144501384f1344b1304a0e0370b02b000000000039400000b32c0b2,0x358d534cd2360d729ca3298a2284a0294a41e8791d8781dc751d0731c8711c06f1b46e0f83f0f43c,0x3a8e939ce82e4b72e8b82d0b62d488214872188420c82204804940048c00364d4,0x0,0x1645a9685a5660000000165000000000000000,0x0,0x5fd8260584555544f970000000000000000000000000000000000005f97c5f400000000000000000,0x778000000000000000000000000000001d20018d6218f639906319262d8962993645836158061d86,0x6719b6519666199559425053f501710000000000000000000000000000000000000000001e2001df,0x7b5e57b1e47bdea79dab000000000084c00755d475dd668da2699a067da56859e675a7691976559a,0x5214750d454f13b5e97b5cd725dd795e1765d17554d3d8b22b000007cdf27c5f47c1e67ade97a1ee,0x855dd769db765d877161581635895f579585755c56d5a55d59539525455053d4d531465114b52949,0x2789d2730000000000000000000000000000006ddb86d9b56d1b36c9b16c1af6b9ac6b61785a18,0x2719ea799da75a0e82a040000000]⟩
def p8 : Direct.Pack := ⟨10,#[0x0,0x20050300901c0602c03010020040000000000000000000000000000000000000000000000000000,0x801505c160501303c0e044120400d14c00144000004711442128460004410c0000000000000000a,0x7e000310b42f0b0350c8340c02e0cc2b0a8290a02408c2609c250881b0601f0681d064210781c,0x264962540025c000000024c0023c8e0000000088218872088000000000840008100000,0xaa0000000000000000000000000,0x0,0xfd00000000000000000000000000000000000000b72d0b82d4b92d8b300000000000000000000,0x400fe3f0fb,0xc02ecbe2f4bc2fcba000000000000000000000000000000000000000000000000000000000000,0x15c0015b000000011142d13429094350c43d0e4491041d08415060000000000000000000000000,0x1605795a,0x330cb320ca304c229ca8298a52a4a4278a32809f288a1274b22b4ae2b0b02bcb1000000000000000,0x3e0f23c4f03d4f63dcd0358d333cda36cd8364d7338df378dd370d4348d1354cd318c9310c7314c3,0x1d975dd8758000000000000001d2741d1000000014a5254250d485054051146515473e8f93ccf4,0x48518459154791d4711b46917465143a0e4388e3398e539ce1381e879de600000001db769e078400,0x5b56c5ad695a16a59129491264a1324cd344c52d49d2c4e1374d9354c12f4b9254ad2a48d1f48122,0x5e5765d5736058260d805f5745f184619855fd7e5c9785dd7b5e9705bd6e5c56759965,0x9725495a550000000253000000000000000944000024c0024b000000000091c008fe4090c008f63e,0x9424e99666000009865796000,0x27a0000000000000000000000000000000000000000,0x9ba6d9b26b9e67800000000000000000000000000000000000a5a94a54009ec00000000000000000,0xb7add00000aa692a3286a2e85a0289a128ea2a87a2283a06829fe8d9f67c9fa759d2739ca719c26f,0xadab5acab0abab4aceb1abea5a8ea2a86a7a82a6a7ea4a7699a6e97a7a9ca6a98a428f002e100000,0xaeab8adeb9]⟩
def p9 : Direct.Pack := ⟨9,#[0x3000321b0d0000000008100602028000000000000000000000000000000000000000000,0x1d8000000000006a361a000000000000002e17800000f070482210098340e090402c140c,0x9e502c800000025928923f1f0dc663200000004c00000000021914880000000783d,0x1b0da0000000ca643380000000017c0060,0x49244000000000007c3e9ec0000000000000000000000,0x2b15a000000000005380000984b25c0000,0x4ab78008f66b310a8843a191489422010481419fcfc00001e8e6723b1d4e8783b9e4e270,0x2dd64b55a2cd6cb1583d1ea00003c800aa55aa5c4e150a81449a4e26d3c9d4fa640000,0x8cc6800008b80223105faf57c0000301790c0041a0ab95d2e000005dc060000,0x0,0x93800015aad8000154ab5540000004924d2591c7a43208fc8a3a00000000000000000000,0xa451e8b46a24fe7d42a0d02873c9dcea733895cde6d339acd2652c974b6612f98caa5328,0xcf800018ac5e270a00c760f09880063f0d87000000000000000000000000000000027b49,0xdf6f40000000000000d56b356000000000000000000000000001a700003218dcce33299e,0xdaf1801bbda6cb63b3e280375b0d6ebf5dcc000038800e170c00000000001bc]⟩
def p10 : Direct.Pack := ⟨6,#[0x5c04d14000005800004800000001ca2480000000c1080000,0xa1b025680022000]⟩
def p11 : Direct.Pack := ⟨0,#[0x0]⟩
def tier : Nat → Direct.Pack
  | 3 => p3
  | 4 => p4
  | 5 => p5
  | 6 => p6
  | 7 => p7
  | 8 => p8
  | 9 => p9
  | 10 => p10
  | 11 => p11
  | _ => Direct.blank
end CoNum4358.WordRows.Orbits

namespace CoNum4358.WordRows.BicolorBase
set_option maxRecDepth 65536 in
def tier3 : Tier := ⟨24,#[0,0,10,18,24,24,24],⟨8,#[0x402008080402a088848250301812a5a48c8a877158535238]⟩,#[⟨0,#[]⟩,⟨12,#[0xbb2bb2af36f13f1f62f53d71d71fc2]⟩,⟨38,#[0x2ca9002ac8bf24002f33f64400bc4fab4002f1ba2e203d0ae9d200f42b25a803d0ec15200d51]⟩,⟨57,#[0x2e8b8a21b801c8574e9110dc00e42c1e0c5f9200078d92d4441f203c0b06921fb22005a383490fab4002d1]⟩,⟨0,#[]⟩,⟨0,#[]⟩],⟨0,#[0x0]⟩,⟨0,#[]⟩⟩
set_option maxRecDepth 65536 in
def tier4 : Tier := ⟨82,#[0,0,6,46,70,82,82],⟨8,#[0x87878771717169686858585858585353535252523838380f0e0e8f8e8e797878,0x848484828282505050303030181818181812a5a5a5a4a4a48c8c8c8c8c8a8a8a,0x402008080808080808080402a08888888888]⟩,#[⟨0,#[]⟩,⟨12,#[0x2f12f32f1f42f43f42]⟩,⟨38,#[0x14a6002800521800b001404003c4036000031008e200a000220002b1007400014401688012000500005c407210012001644011000501005604437003909115c00d42441f203c0807810005101aa200808068000253014a60140005010055101a400014406288012001800005c406a88002001a400014406800007101a8400a0005c1004400120401b030692002d1c1e0c003c706a2002b1,0x16440024005490012001404006c00581000b001564004000501001b00156400104055100051]⟩,⟨57,#[0x2ca9002808005817e480056400104bf24002a2000a25f9200129800a02fc900090c005817e4800404003c4fd91002d1000407ec880150000513f64400a0000389f568005a200080fab4002a0000a27d5a0014000071ba2e20390800805d1710160401102e8b880a0200a8174e90072100100ba74802c0802205d3a40140401502c96a00f020008364b5006a080202b25a8034000121d92d40148601402c96a00a0200a8360a90068000051]⟩,⟨76,#[0xba2e2886e0050100440ba748886e0050100440f1f0964b51107c87f02c1e0d74fd1107c97e48c1e0d64b51107c9ff68c1e0d243c5b27c17e48c1e0c5f920005800041c1e0c5f920005000051b25a8883e4068000202b25a8883e4050100500c1a487ec88014000051c1a487d5a0014000051]⟩,⟨0,#[]⟩],⟨0,#[0x0,0x0,0x0]⟩,⟨0,#[]⟩⟩
set_option maxRecDepth 65536 in
def tier5 : Tier := ⟨183,#[0,0,2,78,144,183,183],⟨8,#[0x797979787878787878787878787878787878787574737372725b5a5a3c3cac5a,0xacaca7a7a6a69c9c9c9a9a8f8f8f8f8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e79,0x524a3838383432322c261c1a0f0e0e0e0e0ed8d8d8d3d2cacac7c6b8b8b5b4ad,0x98928c8c8c8c8c8a8a8a87867170696868686868625858585858545352525252,0x2828242422221818181818180c0a0a09c8c4c2b0a8a5a4a4a4a4a4a2a2989898,0x8888888888888484848282825050504844444242303030]⟩,#[⟨0,#[]⟩,⟨12,#[0xab2d51]⟩,⟨38,#[0x404003c716de00e4201c84004000581004400140401503c7e207f42d3eac5bd2307a31ff686c9f003c093d5c00d4201e040010406a10020201a820080806a00020201a000090c05810044201604011000521805000140401504050100540012040190b4eaa00b22c5f7877c8bc7c2005606c9f00348316fe1dd606c9f00348316de00c51f1f0801546c96a00d41d3aa802e0ac96a00f02,0xba7e802c0b16de00a926c9f002a88bf24002b2f1f08006c1b27c003a0f1f08006c317de1d3b0ba7e80290ee9d200a533f64400b46e8b8806c03ead000b4716de002d1005a20008001500005100500001c7c7c2000f1d3aa800ac6e9fa222f9b05e89ebe64978b66f800582000c40159000410056200104015800041005440014401500005100502001c4014000071004a6002800121800b0,0xba2e203908ffb4002533ead00294cbf24001713fed0001c53d5c004712fc90003c53d5c00171c5bf8747c6e9d200e423f64401b02c96a00b22]⟩,⟨57,#[0x441f2034000101220f9014040140316fe220f93ba41e3e103f8100051c1e8d745c4bf2460f063fed000144068000202000a202808028000051d3aa9745c4058100c000024000147c7c25d17100a818b6f0ee9000051c1a487fda00028c90716c9f0034000680000510004164b51107c80d00c1e8d74e90bf2460f06b25a85bd2004810044000501a7552e9d200b02f1f0974e9002a0582a46c9f003403078317e48001618bef307831d1b0c1e0d243c4bf2478f84b25a801507069200280000a383c1ae9fa220f9c1e0d243c5b27c60f0600160001070783000a0000a383510014000031,0x4f5707d5a00038dd3f42ca9002809b27c17e480054402808009000090f1f081ec08005862dbc3a3600280ae9fa221b801404d93e0fd91002a00140400400005878f842ca90002c1b27c1f5680054174fd0bf2400243ba7485f9200129d92d43fed00090ec96a1f5680148760a90ffb400051ba7e8883e40501592d4445f27ec8a4878b64f8014040280800580004101404002800028d92d4445f27d5a2c17a220f92fc900110001400003100500004800028f8f84441f2747c40501004400024183c19b27c1df224437002808022078f84441f21fc0b0783220f93fed088ae0048100440,0x2c96a220f90fe049eae0fd9100071]⟩,⟨76,#[0x920e2d93e0fd91002803f64400a00002880020b05489eae0fab400051920e2d93e0fab4002803ead000a00002880020f1f09745c43d8100440d3aa9745c4b2a400a02ba2e202808022000100c1e0d745c5107c97e48d3aa9745c510dc00a02c1a489eae0fd9100051f1f09745c510dc00440c1a489eae0fab400051f1f0974e903d8100440d3aa974e90b2a400a02ba74802808022000100c1e0d74e91107c97e48c1e0cd93e0bf24000a0d3aa974e9110dc00a02c1a48d93e0fd9100280f1f0974e9110dc00440c1a48d93e0fab400280f1f0964b503f8100041c1e0d74fd0bf2400041c1e0d74e90bf2400051c1e0d64b50ffb400041b25a803400010100041b25a802808028000041c1e0d64b51107c9fb22f1f0964b51107c80500c1e0d64b51107c9f568c1e0d64b51107c97e48,0xba7e8883e4bf2400202b25a8883e4ffb400202b25a8883e4fab400a02921e2d93e0bf24002022fc90008080058000412fc9000808005000051b05489eae0fd9100051]⟩,⟨0,#[]⟩],⟨0,#[0x0,0x0,0x0,0x0,0x0,0x0]⟩,⟨0,#[]⟩⟩
set_option maxRecDepth 65536 in
def tier6 : Tier := ⟨425,#[0,0,26,154,377,423,425],⟨8,#[0x3c36362e2e1ef9f5f3e7e6dddbdadad7cebdbcbcbbb7aeaeae9f7c7a7a7a7776,0x7b7a7a7a7a7a7978787776767676767674726c6a6a66665e5e5a5a564e3e3e3c,0xafafafafaeaeaeaeaeacaca69f9f9e9e9e9d9c8f8e8e7d7d7d7c7c7c7b7b7b7b,0xdadadadad9d8d6d2d2d2cfcfcfcecececacac6bdbcbcbcbcbabab6b6b4b4b4af,0x1f1f1e1e1e0ff9f9f8f8f8f4f2f2ececeaeae8e7e6e6e6e6e6e6e4e2e2dcdcdb,0x524f4f4e4e4e3d3d3c3c3c3c3c3c3c3c3c3c3b3a3a3a363636342f2f2f2e2e2e,0x72726d6d6c6c6c6b6b6b6a6a6a6966665d5c5c5b5b5b5a5a5a5a5a5a59565656,0x8d79797979797878787878787878787878787878787574747474737372727272,0x9a9a9a9a99969696969694928f8f8f8f8f8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e,0xb2b0adadadacacacacacacabaaaaaaa7a7a6a6a6a6a6a6a49d9c9c9c9c9c9b9b,0xd0cdcccccbcbcacacacacacacacacacac7c6c6c6c6c2b9b9b8b8b8b8b5b4b4b2,0x261c1a1a190f0ff0f0f0f0f0e9e9e8e8e8e4e4e4e2e2e2d9d8d8d8d8d8d3d2d2,0xa4a4a2a2989898988c8c8a8a8a89696964625858545452524638383834343232,0x4523c8c4c4c2c2a8a8]⟩,#[⟨0,#[]⟩,⟨12,#[0xe42b225601b01b0a53c515514711710f1a92b82aa26c03a02b22b12b02d1f02d42d41d40d20d20]⟩,⟨38,#[0xc1e8c5f923078316f48c1a881fd0b16de00d20c5b7877c8316de1dd60c5b787748b16de1dd20c5b780348116dc1dd20c1e0c77c8b06a21dd60c1b681eacb06da164f8441f20340306da1d1b045b707748307a35d17193aa28b6e24ea896d4801a0000146483880d0093aa28b6e307a35d3a4b1f088b6e2c7c307f02b1f081fc0b07831d1b0b0548034030783000b0b1f088b6e30783490f1,0x6cdf000a81b27c002a26c9f000a82c15a07ab201404002c1115c1d3b0f1f08003474eaa00291ba7e80090ee9d200253ba2e200b06c96a00a43921e20280ac96a222f9b05e8883e64978a22b8d3aa802c0b17de00e02c5b780380b4fab00b02d3aa802c0b07a31fb22f1f080150316fe00c40c5b780310b16de00c41c5b7803103c7e200540f1f0801507c7c200540c1e8c7d5a1107c80d00,0x3f644001c6e8b8805403ead0001c4ee9000051c5bf80034716de000d14f570001c6e8b8a22f94f5f2001c53d5c00071921e2593e64878964f8441f2747c6c96a00b02ba7480290ec96a00b023f64400b04bf24002a2ba74801908fab4002c1c1e0c746c0fab4002a0ba74802c08fd91002a03a3600280b17de00290c5b7800a4b16de00291c5b7800a41b27c002a0c1e0c002c2e9d2222f9,0x6c9f0038093d5c00c423fed00090cfd91006423ead00290ee8b880b02ba74801501107c9dd20c1b681eac9117c9fb22c1b68593e1117c9f568441f21fc0b16de001b0c5b7874ec316de1d1f0c5b78746c716de1d1b0c5b78006c306da1d1b00f604002c1107c9dd202ca90002c2e8b880a433f6440094cbf2400071ba2e20190ac96a005413ead00094cbf24000712fc900094c3f8100051]⟩,⟨57,#[0xc5b7963a183f0162dbcb1d081f80bc7c2592d40fe05a7550048100280c1e0d74fd0bf2460f06b25a87fda30783592d40160583c18bf24000a0c1a8974e90050160d443f64400a02c96a00d000040564b50050100500c5b7962a18022060f06ba7480110b07835d3a40088183510fab400280c5b7963a10ee9062dbcb150c7548306921f5680050183490fd9100280c5f7983c18004862dbcb1d088b2e30692364f80050183c1ae9d2220f9c1e0cd93e0005060d44ba74888ae316de58e84938a38b6f2c54349451c1e0d74fd00020e0f06ba7480014706a25d1710050183c1ac96a220f9,0xc1a8888ae0fd9178f84443700110316fe220f9018018b6f306ca164d8f1f08883e4028060f06441f27d5a306a2222b83ead183c19107c97e48c5b7983650e8d862dbc459707748316de494510140583c18fd9100051c1a89745c4050162dbc938a25b12316de00c00000a383490bf2400051f1f08014000028e0f06ba2e20110b07835d1710088183c18fab400051c1a885f9200018d92d401a0000107078317e48000a38b6f24e289dd20c5b7925144ec9160d243f6440014706921f568000a38b6f24e28a2cb8c1a489eae00028e0f06ba2e2883e706a25d17144571835113d5c00031,0xf1f08d93e03f8178f840fe04001074eaa16d480040583c19b27c1ff68c1e0c7fda00020e0f063f6440110b07831fb220088183510ffb400202c1a887d5a00501364f801a0000809b27c00a0200a009eae004810044001a0000808002080a0200a000010404810044000405a7550050100120c5b78774883f0162dbc3ba401f80b16de1dd20004058b6f0ea9000a02f1f08011000090364f8018000048316de364f83ba418b6f0ee9016c48c5b78774800020e2dbc3b244011030692364f83fed0d93e0068000020d3aa8886e0050162dbcc1b281ea4b4eaa222b80120583c19107c9fb22,0xf1f08746800028e9d543a26200a02c1521fb22000a3241c4fab400280920e27ec880140582a43ead000147c7c2220f9001a38b6f0014000051b05489eae00028c90716c9f000a0001400005100041e3e12e9fa220f9f1f09243c5b27c78f840016000107c7c2000a0000a3a7550014000031ba7e888ae00020dd3f4441f20080ae9d2222b8000a3745c5107c80281ba2e2883e40140582b44f570001064878b64f80040400a0000208003100404002c00020802020014000146c96a220f901405e3e103d8100440d3aa859520050162dbc01404011030783364f801c0402808022000100,0xb25a888ae00481364f80140400281107c9fb2200502883e4fd91002802fc9000808005862dbc2c8b200a02e9d2222b800880883e4fab400281441f27d5a0014078f840024000241b27c0028000241e3e1316de1d1b0f1f0974fd110dc78f8400200002c316de582943a3618b6f0e8d800202c5b78744c401405d3a4443700280bc7c207a82000a374fd0050100041ba748028080028d92d43f6440090e487897e48004047ec88014000051d3aa8591640140582a42fc9000146e8b8804400050164b50fab400243b05685f92000209f5680050000146c96a17e4800487e3e10e8d800041,0xba7e8883e4bf245d1714457001102c96a220f93fed164b51107c80500921e2d93e0bf2427ab800880000c5115c1f568000a2883e4bf24000712fc90002c0002097e4800140001453d5c00120000a38b6f248689d1b1c5b7924344e8d862dbc3a3600010716de1d1a0000a3745c510dc00440b25a859520050158a864f57001102e9d217e480048774e90050100440b25a85b52001011fb220088000a02c96a00a0200241e3e12e9fa07b02ba7e802808008078f84ba7e859522c152364f83fed174e90b2a400a02c5b7960a503d4962dbc0140400242c96a221b80140574e91107c80a02,0x5d3a40f60401102e8b89654801404d93e0ee90002026c9f075480050127ab83b2440110316de164d80f5258b6f0b22c87a82445707ec880220220f93fed000809107c9f568014058b6f0e8d807a92c5b78744c43d415d171443700280b16de1d1b02c9b18b6f0e8d016459ba748886e00220494516c9f00280ae8b897e4800487745c4050100440b25a81fc0800209ff680040400144fab400a02000a25f920009000051920e2d93e0ffb41ff68000a200082e8b887b02008818b6f03d4100051ba2e2883e40501222b83f6440014716de490d12c9b38b6f24868964d8]⟩,⟨76,#[0xb25a87d5a0050100041b25a888ae0fd9100041b25a8883e4fd9100202f1f0964b51107c9f568b25a888ae0fab400041b25a8883e4fab400202b25a8883e4bf2400202c5f7983c19b27c17e48c5b7983c19b27c17e48c1a48d93e13d5c1fb22c1a48d93e13d5c1f568c1e0d745c4bf2400041c1a89745c4bf2400202f1f09a7552e8b887b02d3aa9745c4050100100f1f09a7552e8b896548f1f09745c4022000100f1f09a7552e8b8a21b8c1e0d74e91b27c17e48c1e0d74e90bf2400041c1a8974e90bf2400202f1f09a7552e9d207b02d3aa974e90050100100f1f09a7552e9d216548f1f0974e90022000100f1f09a7552e9d2221b8c1e0d64b50fd9100041f1f0964b50028000041c1e0d64b50fab400041c1e0d64b50bf2400041f1f098b7f2c96a220f9f1f098b6f2c96a220f9,0xba2e2883e4bf2400202920e2d93e13d5c1fb224f5707ec88002880020920e2d93e13d5c1f5684f5707d5a0002880020ba748883e4bf24002026c9f05f9200101000a0b0548d93e13d5c1fb226c9f07ec88014000020b0548d93e13d5c1f5686c9f07d5a0014000020ba7e85f920010100041ba7485f920010100051b25a87fda0010100041]⟩,⟨95,#[0x34eaa62dbc9f4a69eae0009078f84c5b7979b31b27c00120]⟩],⟨0,#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩,⟨0,#[]⟩⟩
set_option maxRecDepth 65536 in
def tier7 : Tier := ⟨651,#[0,0,40,314,624,651,651],⟨8,#[0xfbfafaf6f6f6f6f6f6f6f6efefeeeedfdfdfdedbbfbfbfbfbfbebebd7f7f7e7e,0x6e5f5f5e5e5e5d5b56563f3f3f3e3e3e3e3d3d3b36361f1ffdfdfdfcfbfbfbfb,0x7b7b7b7b7b7a7a7a7a7a7a7a7a79797776767676767676757473726f6f6f6f6e,0x9e9d9d9b8f8f7f7f7f7f7f7f7f7f7f7e7e7e7e7e7d7d7d7d7c7c7c7c7c7c7c7c,0xb6b5b5b4b4b3b3afafafafafaeaeaeaeaeaeaeaeadaba7a69f9f9f9f9f9f9e9e,0xcecdcbcbc7c6bfbfbfbfbebebebdbdbdbdbdbcbcbcbbbbbbb9b7b6b6b6b6b6b6,0xdbdbdadadad9d9d7d6d6d6d6d6d6d6d5d5d3d3d2d2cfcfcfcfcecececececece,0xecebebebeaeaeaeae9e9e7e6e6e6e6e6e6e6e4e4e2e2dfdfdededddddddbdbdb,0xf4f4f4f4f4f4f3f2f2f2f2f2f2f2efefefefefefefefefeeeeeeeeeeededecec,0x3c3c3b361f1ffdfdfcfcfbfbfbfbfafafaf9f9f9f9f9f9f8f8f8f6f6f6f6f5f4,0x5f5f5f5e5e5e5e5e5e5e5d5b5a563f3f3f3f3f3f3f3e3e3e3e3e3e3e3e3e3d3d,0x7a7a7979797777767676767676767674726f6f6f6f6f6f6f6f6f6f6f6f5f5f5f,0x7d7d7d7d7c7c7c7c7c7c7c7c7c7b7b7b7b7b7b7b7b7b7b7b7b7a7a7a7a7a7a7a,0xaeaeaeaeadacaba69f9f9f9f9f9f9f9e9e9e9e9e9e9d8f8f8f7d7d7d7d7d7d7d,0xbababab7b6b6b6b6b6b4b4b4b4b2b2afafafafafafafafafafafafaeaeaeaeae,0xcececececececdcbcbcacac6bdbdbdbdbdbcbcbcbcbcbcbcbcbcbcbcbcbbbbba,0xdadadadadadadad9d6d6d6d6d4d4d2d2d2d2cfcfcfcfcfcfcfcfcfcfcfcecece,0xeaeaeaeae9e9e7e7e6e6e6e6e6e6e6e6e4e2dcdcdcdcdbdbdbdbdbdadadadada,0xf4f3f2f2f2f2f2ededededededecececececececebebebebebebebeaeaeaeaea,0x996d6b6b676757564f4d37362f2f2b1ff9f9f9f9f9f9f9f8f8f8f8f8f8f4f4f4,0xe9e5e4e3e2d8b8b89c9a9a]⟩,#[⟨0,#[]⟩,⟨19,#[0xa800150402a01df203bac077488ee901d3b03a3e0746c4e8d8222f900160002c4005800253001a2001c40038804510058200a800149002910052000a88015000a82c1e8c03400068100d00,0x1c0402c08052180b020188403104062000642]⟩,⟨38,#[0xc1e0c76c8b069216568c1a88755830783220f9c1a8888ae3069200090443700300306da000b045b7003403078300051c1a480014706a20003193aa2034024a2880902c1aa81e94f06aa16459c1aa8745c706a21d131c1e0c0024306a200280c1a4800a0307835d3f4c1e0c00282c7c200d00b150c0140307c307a82c1f081ea0b07c2166c8c1f0874e8307831d1a0c1f0924b470783490d1,0xf1f081fc0b07831ff68c1e0c02c083f8100d020fe04034003f0100d0201a0000808050100500c1e0c0110b078300440c1b285936306a200c402ca90034034eaa16d48c1a887fda306a2005406c9f003400b6a400d002d890034000680000410120401103078316e48c1a881f908060000120c5b787748306ca1d1b0c1a487fda0ee9000d003b24403400ea9000d0201a0000083069207b22,0xb25a80090ec74249c51b150d25146c15200051920e200a00014000051f1f09243c6c15a00041921e20080ac16a07a53921a20280a4968966c8b05a8883e64968a22b8f1f898b7f34fab62fbcc5b790301316de40c01c5b784380316de01c40c5b780300b16de00c00443700300316de1dd20c5b785700316de00d00b25a80340116dc00d00c1e0c0380b06ca07a92c1a88028083d8100d00,0xb0d881f908014000120f1f08746c2c7421dd20b150c75482c1521ff68b0528746c0e8d8002023a26200a02c1d207b22b05481ec08ec91002803a3400280ac1d216568b054859522c74222cb8b0548002c1115c00290441f200a05107c80280f1f08002c2e9fa222b8b05689eae2c15a000b0b0528002c1115c002a000500000c40101000b0b150c8aae2c362224f8b0748886e1115c1d3a0,0x441f200346e9fa220f9921e2d93e24878800b1921e2002c24868800b1441f2001c400580004100140001464d29a2ab8928a2893e64a28a24f8922e2886e1107c9d171f1f084034316de58e84c1e0c00242c74222cb8c1e0d74fd2e9d200243b05685f923c7c207a92b1d0c1f80ac74207e02b05281ea48050100090ba7e8028080501000a00120400a02c543004402c8b200a00022000280,0xba2e20090e487897e48928a2028083d410005101404001464e28b64f8938a25b1224868964d9921a2593600600000513fed00014402800005100880000c64d2996e480fc0400144009000051938a2774824a289d922921a2746c648689d1b0920e27fda0e8d8000413a3400014648b887b22920e21ec0a48b896568920e259520ea90000513a262011024e28a2cb8920e2002c1115c00051,0xc5b786424316de000b0c1b68002c0bf24000b04437002809107c80a0244570024083d59000b00f504000c5115c004404437001101107c80c00441f27fda1107c805002c9f0002c0b22c800a0449f01f909107c87e02002400024316de1d1b0ba7e8886e1165c1dd203a360002c0e8d0000b13a262002c00080000b04557076c89115c1d922449f075581107c9d520c5b79271464e28a2cb8,0x2da90008083f8100041c5b787748316de1d1b0c1b28746c1165c1dd200140400482e9fa07b023ba441f808ee9007e023ba4000808ea9000a023a3601ea48e89887a820088000482e9fa165486c9f077480ee9016c483ba4000104ec91004403a36059360e8d016459c5f78d9be316fe27af9c5b784034316de02098c5b780824b16de01290c5b780024716de00090c1a480024316de1d1b0,0xc5b781ea4b06ca07a92b25a81fc08fd9100243c5b785936306ca164d86c9f043801107c80c00b25a85b521107c9ff683ead00090cbf24002432ca9002808b26c07a922c8b21ea083d81004400140401101b27c07f02]⟩,⟨57,#[0xd3aa983c1ae8b8e0f06ba2e20010706a25d1714f57183512e8b880202d3aa98b6f03d09e9d54c5b785916706a25d1712fc91a755316de1d131f1f098b6f2b26678f84c5b78593234eaa62dbcb150da755316de00280c5f7983c1ac96a62dbcb1d080300316de58a8600801e3f1306a25d3a4f1f0983512e9d278f84b25a8014034fab60f06ba749a755307835d3a4c1e0d74e91b27c60f06ba748001070783592d43ead183512e9d200202f1f098b6f03d4160f06b25a85f92307835d3a42fc9183c1ac96a1fb22f1f098b6f0b26478f84c5b7874683c7c262dbc921a383c1ac96a00041,0xc5b7803000009078f84c5b78754834eaa62dbc3b2458b6f0ee9017e48c5b7877480060062dbc3b2440100316de1d5200100583491b27c1fb22c1a489eae0fab460d244f5707ec8b0692364f83ead1e3e134eaa221b8f1f098b7f1107cf8f84c5b78883e74eaa62fbc44571a755316de222b8c5f7983c19b27c62dfcc1a889eae316de60f066c9f18b6f306ca00090c5b79835113d5c62dbc45970030030692364f84f571e3e1316de49451f1f098b6f00028e9d54c5b791e84f4eaa62dbc0f4278b6f24e2880c00c5b7925144040178fc4c1a89745c7c7c260d44ba2e3a7d5b07835d171,0xd3aa89eae0048169d54012040080b07835d1712fc9183c19b27c1fb22c1e0c7ec880020e0d444f5707ec8b06a21fb2200405e3e134eaa16548f1f098b6f0022078f8400880004034eaa62dbc2d8918b7f306a217e48c5b7983510bf2462dbc6c9f00300316de16c48018018b6f00c0100440c5b78030000020e2dbc01004011030692364f82fc91e3f1306a21f568f1f0983510fab478f846c9f001403c7c2005000008383c19b27c1f568c1e0c7d5a00020e0d44ba7485f92306a227ab83ead183510fab400202c1e0cd93e0bf2460f062fc900010706a217e4800405e3e134eaa00120,0xc5b7961a11b27c78f84ba748886e3c7c2592d4441f3e3e124868b64f8f1f08402000028f8f840012000107c7c200080000a3a7550080880280d3aa800a000008f8f84ba7e800107c7c25d3a4000a3a7552e8b880280ba7e8008080020dd3a40040400146e8b8802800008364b50050100041f1f0964b51107cd92d44457000106c96a220f900405e3e134eaa07b02f1f098b6f03f0169d54c5b780280b4eaa00a02002018bef3078317e48c5b7983c18bf2462dbc208000280b16de07e02018058b6f03f0100c00c5b7803000010162dbc01404010034fab60f063f645a755307831fb22,0xb0548d93e0fd91582a44f5707d5a0fab40028000041e3e12e9d207b02ba748028080080582a44f5707ec88fd910028000041e3e12e9d216548b0548d93e0fab478f84c5b7800243c7c2592d4443718bef2c96a222b8c5b7964b51115c62dbcb05289eae316de58294001218b6f1b27c00280c5b7804044014062dbc005000004716de002020012160a91b27c27ab86c9f000a00001078f84ba748883e7c7c2364f800141a7552e9d2222b8ba748d9be1115c5d3a46c9f088ae2e9d2222b80008374e91107c80202b25a888ae0fab4364f8004040028316de58a864f57164b51115c1fb22,0xc5b792614d3d5c62dbc928a2d93e2c96a220f92fc91745c5107c97e48b25a8883e4fab469d54ba2e2886e3c7c2592d40f605e3e11b27c07a82d3aa962a193d5c62dbcb25a80280ac96a00a0200201a7552e9d200a02d3aa87ec88014060f06b25a87ec8ae9fa17e480040574e91b27c00a02ba748028080020d92d43fed00080ac96a1f5680140564b500481002026c9f07ec8801401fb220050000104bf240020200141e3e12c96a16548b0548d93e0bf2478f84ba74801102e9d20044000404d93e0fab4002803ead000a000020f8f84b25a800483c7c25d3f400201e3e11b27c1d1a0,0x2fc9000104001897e4800404001474eaa27ab83a263241c5b27c1fb22920e29eae0fab41fb22000a2000834eaa5d1710f605241c53d5c1fb22d3aa9745c4b2a45d17100880004024838b64f83ead07d5a0002880020c5bf964b51107ce2dbcb25a8883e716de490d16c9f18b6f2486880091c5b7924344004862dbc4f5700014716de10080000a38b6f0004800041c5b78002000028c90716c9f09eae13d5c0005100041e3e12e8b8a20f9d3aa9745c5115c69d544f570000c6e8b8a7af9441f3745c53d5c220f9ba2e288ae00020dd171441f20080ac96a220f93f6449eae0002080031,0xc5b78004800048364f84f57000483c7c25d17144371a7552e9d2221b8c5b7964b50e8d862dbc6c9f07468316de27ab83a2638b6f0e8d800090c5b78746800008e2dbc3a2620020316de27ab83b2458b6f1b27c1d520d3aa9745c405015d17101404001053d5c1fb22000a27ec88010100051f1f0925145b27c69d544f5705916716de17e48000a3241c5b27c17e482fc9000144001078f84ba2e201103c7c21f568000a374fd0bf2400041ba7485f9200028dd1714f57001102e8b8a20f92fc91745c4022000202b25a87fda00020d92d400a00001053d5c1f568000a27d5a0010100051,0x6c9f07fda0001062dbc970a69eae316de498534f5718b6f1b27c07a82c5b78d93e0050162dbc0f5240024316de07a8200023a7551115c1fb226cdf088ae0fd91364f8445707ec893d7ca20f93f6449eae1107c9fb22445707ec880020a20f93f6440080b16fe220f92fc918b6f2d346364f8c5b7961a11b27c62dbc4f5705916716de27ab8008818b6f0b26c00090c5b7859164004078f84441f27d5a2e9d2220f92fc90d9be1115c1f5686c9f088ae0fab4364f82fc90002813d7ca20f93ead09eae1107c9f568445707d5a00020a20f93ead00080b16de364f80fc04883e4bf2400202,0x3c7c2364f80fc0583c19b27c17e486c9f0410000501364f80180000809b27c00a02008009eae00c01004404f570020080220364f83fed000809b27c1f568014049eae0fd91004403fed00080800209fb220088000808fab400a0200083e3e12e8b887b02d3aa974e903d8169d544f5707648ae8b880a0200200d93e0bf2400120f1f09745c4b2a478f846c9f0754834eaa5d3a42ca9174e90022000100]⟩,⟨76,#[0xc5b78d93e0bf2400202c5b793e94d3d5c001206c9f09eae0fd9100020c5b7979b31b27c001206c9f09eae0fab400020ba2e25f920010100041ba748d93e0bf2400202ba7485f920010100041b25a87ec88010100041f1f0964b50fab400041b25a87d5a0010100041b25a85f920010100041f1f098b6f1b27c00a02f1f098b6f1b27c17e48d3aa98b6f13d5c00440f1f098b6f1b27c00120d3aa98b6f13d5c00120d3aa98b6f27d2980120f1f09a7552e8b880100f1f098b6f1b27c00051d3aa98b6f27d29a7ab8f1f098b6f2f36600120f1f09a7552e9d200100f1f098b6f2c96a364f8d3aa98b6f13d5c00280f1f098b6f2f366364f8f1f098b6f2c96a00041]⟩,⟨0,#[]⟩],⟨0,#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩,⟨0,#[]⟩⟩
set_option maxRecDepth 65536 in
def tier8 : Tier := ⟨772,#[0,0,156,618,772,772,772],⟨8,#[0xbfbfbfbfbfbfbfbfbfbfbfbfbfbfbebebebebebe7f7f7f7f7f7f7f7f7e7e7e7e,0xefefefefefefefeeeeeeeedfdfdfdfdfdfdfdfdfdfdfdfdfdfdedededededebf,0xfbfbfbfbfbfbfafafafafafaf7f7f7f7f7f6f6f6f6f6f6f6f6f6f6f6f6f6f6ef,0xfefefefdfdfdfdfdfdfdfdfdfdfdfdfdfdfcfcfcfcfcfcfbfbfbfbfbfbfbfbfb,0x3f3f3f3efffffffffffffffffffffffffffffffefefefefefefefefefefefefe,0x7d7d7d7d7d7d7c7b7b7b7b7b7b7a777676767676766f6f5f5f5f5f5f5e3f3f3f,0x9f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7e7e7e7e7e7e7e7e7e7e7e7e,0xbbbbbbbbbbbbb7b7b6b6b6b6b6b6b6b6b6afafafafafafae9f9f9f9f9f9f9f9f,0xbfbfbebebebebebebebebebebebdbdbdbdbdbdbdbdbdbdbdbdbdbcbcbbbbbbbb,0xd6cfcfcfcfcfcfcebfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbf,0xdddddddddddddddbdbdbdbdbdbdbdbdbdbdbdbdbdadad7d7d6d6d6d6d6d6d6d6,0xdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdededededededededededddddd,0xeeeeeeeeeeeeedededededecebebebebebebeae7e6e6e6e6e6e6dfdfdfdfdfdf,0xf2f2f2f2f2f2f2efefefefefefefefefefefefefefefefefefefeeeeeeeeeeee,0xf6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f5f5f4f4f4f4f4f4f4f4f4f3f3f2f2,0xfbfafafafafafafafafafafaf9f9f9f9f9f9f9f9f9f7f7f7f7f7f7f6f6f6f6f6,0xfcfcfcfcfcfcfcfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfb,0xfefefefefdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfdfcfcfc,0xfffffffffffffffffffffffffffffffffffffffffffffefefefefefefefefefe,0x7f7f7e7e7e7d7b77776f6f5f5f5f5f5e3f3f3f3f3f3effffffffffffffffffff,0xbfbfbebebebebebebebebdbcbcbbb6af9f9f7f7f7f7f7f7f7f7f7f7f7f7f7f7f,0xebebebeae7e7dfdfdfdfdfdfdedededededededddbdadad6cfbfbfbfbfbfbfbf,0xf6f6f6f6f4f2efefefefefefefefefefefefefefefefeeeeeeededededecebeb,0xfdfdfcfcfcfcfcfcfcfbfbfbfbfbfbfbfbfbfafafafafafafafaf9f9f7f7f7f7,0xfdfdfdfd]⟩,#[⟨0,#[]⟩,⟨19,#[0xb150d61b12c342583a4b070960b52c162582a4b052920a060142102800050400a02c5c358784b070960ad2c15218280c1f0983c1b06ca60d84c1aa983513069260d14c1b49834d3069200d00,0x455708a2e1127c224b844570886e1107ca29b844b70886e0005849c51934a72614e4a28c92d1924a7245c648a8c90d1920e320146002881051000a32654e4aa8c9151921e3241c44828d8e84,0x2c8b2411003221024480088201100b6a4165482c9d0591e4b2341444030240504804890051200024077480ed911d9223aac075480e9d01d3223a640746c0e8d01d1713a2c274580e898a2cb8,0xfe0403400005807e420fc041ec883d8107a920f5041e94c3d2187a220f4261a808150101a02014041fc083d8107aa20f4661e8882d0116e482d89059b20b324165682ca9059360b26416468,0xb25e903012060097f4821c0040340104c020920388004a40060100c00004860024400485d3f4ba769747c6c15a490f13fed07fc88feb41dd203a36064240b6a415c00]⟩,⟨38,#[0xc1a481e88b068a07a13c1e0c7ec8b078316648c1b085932306a217e48c1a8801103069216468c1a285916706a21f568c1a480048307831d322c1b087468306a21d161c1a487ec8b06921f568c1a28744c70783222b8c1a88883e7078349253c1b092434706aa00051c1a8800047069249071c1a89745c707c200280c1e0d64b53078300080c1a8960b130692582a4c1a2960a5307835d3a4,0xd3aa983c1b17de60f06c5bf98351316de60f06c5b798351316de00c00c1e0cd93e3078300041c1b280024306a227ab8c1a880080b0692592d4c1a48d93e3069227ab8c1a485f920060000100f1f08014034eaa00902c1e0d745c707831f568c1a8974e9306a21fb223fed003400fd9100d003ead003400bf2400d000120401000040100500c1e0c5f923078300a02c1b081ea0b06a207a43,0xb052859164b36400280b074800482c15200100f1f0874682c5431d922b0d0875482c1621d161b05487ec8ac1521f568b0528744c4e9d0002803a3400080ac96a222b8b150c8a2e2c342224b8b0708886e2c162220f94457000a02e9d2222b8f1f0924346c54349853b0d0925146c1c249151b05a800146c15249071b052800106496880280921a20080bc7e260d44f1f09835134fab60f06,0xc1e0d74e92e9fa00202ba76960a52e9d258294ba74888ae2e8b880280b150c7d5a0fab4002800040400283c7c207a82b25a80280ac54327ab8b150c0280ac34207e02b07081ec0ac16207a43b05481e88ac14a07a130f50400a083d41002800140400200040100280ba74802808fd9100280f1f0859322c96a16648b150c5b122c36200440b0d08d93e2c1c216548b05885f922c15216468,0x924a688ae248a8a21b8441f200146e8b8a20f9f1f0859323c7c200090d3aa962a1b4eaa00280c5b7962a1b16de58684c5b7960a5316de00280c1e0d64b52c97a582a4b25a960a92c96a222b8b1d085f922c74200c00b150c01002c152364f8b05489eae2c15217e48b05289eae2c14a000906c9f000a0008088028000500001040140000200050000044010100090f1f0974fd3c7c2000a0,0x921a21ea0a483887a220f4a6001474eaa16459930a65b1224a28b64f8928a2011064a2880440924a65992248a896548921a2593224838964682fc9000144b22c800510088000044020000051ba2e201100fab400051922e200482483880100d3aa8744c64c299d922928a27548249299d322921a27468248389fb22920e27d5a0e8b8800513a26200106c96a220f9930a68a2e24a28a24b8,0x938a25f9224e2880c00928a20200a4868b64f8921a200246486880090920e2d93e24838a7ab8920e25f9213d5c0005120100001440101000510012000104004000051000a2000834eaa00031c1a89745c6e9fa00041ba74800146e8f8c90d1ba2e324346e8b8a20f9928a27ec88fd910005100082000c74eaa07a13b25a81e90e4d2980a02930a69eae24a2887e02924a65f92248a887b02,0x140000440040000314557002809125c07e02445700200910dc07b02441f21e90d115c1fb22451705b121127c00440445705992110dc16548441f25f921107c80400441f27d5a110dc00120ba748886e2e8b8a21b84517076489125c1d5204457074c89107c9d161f1f0925147c7c200051d3aa81e84f16de49853c5b792514716de490d1c5b7800146c97a49071b25a9241c6c96a220f9,0x3a64459920e8d0164c83a26259167c7c2221b8f1f08883e74eaa222b8d3aa8886e317de222b8c5bf8883e716de222b8c5b78883e716de00090b25a8886e1b37c222b86c9f088ae13d7ca20f94f570883e5165c00c00445700010510dc17e48441f200808004800020ba7e8002c2e9d2220f9ba748002c2e8b8a22b8ba2e2002c2c96a000b06c9f0002813d5c00031445707d5a1107c9fb22,0xb25a8746c1b27c1d1a04f570744c4ffb4000203fe4475480feb41d9223ba405f920ee9000c003b24401000ea90008023a36000240e8d0000113a262002003d91001200f60400082e9d207b02ba2e21ec093d5c1d9223b64402808ec91002023aa401f808e8d007a823a2c21e90ce89887a132cad000480b2a400020ba74859522e8b8965486c9f075480ec9116c483aac001100ea9000041,0x6c9f07fda1b27c00500441f27d5a0ffb4000413fad05b120fd91004403ead05b1200280000416c9f01f808b72400a022d89000808b2a407b022c9901ea08b23407a222c8b21e84c3f21004400fc0400107c7c200120d3aa800482c96a001206c9f0004813d5c001202fc9000483c7c21d520d3aa87648b16de1d922c5b787548316de1d1a0c5b78744c6e9fa00100ba768744c6e8f89d1a0,0x3f6441f808fab400a02012040080bc7c216548f1f08011034eaa16c48d3aa85952316de16c48c5b785932316de16459c5b780110306a217e48b25a859522c96a164d8b0d08d93e1b27c00c004f570591653d5c00440441f25f920bfa4165482fc9059520b62400c002c9b000240b22c8008003004011000600000410100401100022000202008800040306a21f568ba74859166e9d200440,0xf1f081f80bc7c207b02d3aa81ec0b4eaa00a02c5b781f80b16de07a82c5b781e84f16de00a02c1e0c5f922c96a07b02b25a81ea4a4c29a7ab86c9f01ea09b27c00a022fe901ec08bf2407b0220800028083f0100c020fc04030003d49000900f504000440600002020140401000050100100014040010707831fb22ba2e21ea0ae8b880a024f57002409115c1fb223fed000808ff9107e02,0xc5b791e84f16de42813c5b790923316de40094c5b785b12316de164c8c5b781f82316de07e02c5b781e84f16de02c08c5b780300316de00090c1e0cd93e306ca00090c1a889eae30692592d4459700300110dc17e48c5b797edcf16de5f7ecc5b7974fd316de1ff68c1e0d745c706a25d3a4ba7e85f922c96a1ff68b25a80240ac96a00500445707d5a1107c9fb222fc9000280bf2400031,0xf1f08883e74eaa222b8c5b797fb3316de5fe59c5b797eb5b16de5f6dcc5b7969a3316de58684c5b7960a5316de564ccc5b792e14f16de49853c5b792435316de490d1]⟩,⟨57,#[0xf1f098b6f0820078f84c5b7809023c7c262dbc00801e3e1316de00041d3aa98b6f13d5c69d54c5b785f9234eaa62dbc05005a755316de01802d3aa98b6f0040169d54c5b780080b16de17e48018018b6f0040100400fba498b6f0bf2478f84c5b787d5a34eaa62dbc3f645e3e1316de00a02d3aa98b6f0022078f84c5b78004834eaa62dbc00241e3e1316de364f8d3aa98b6f13d5c69d54c5b797d1674eaa62dbc9f4a7a755316de40011d3aa98b6f00008e9d54c5b79745c7c7c262dbcbf50de3e1316de5e6ccf1f098b6f2c96a78f84c5b7900213c7c262dbc00101e3e1316de5d3a4,0xb25a87d5a00020e9d54ba2e20040316de364f8000a3e3e1316de5e6ccf1f098b6f2c96a78f84b25a8d93e3c7c2592d400201e3e11b27c10080f1f08d93e0004069d544f57000a0316de5e6ccb25a98b6f2c96a00202f1f09a7552e9d278f84ba748d93e3c7c25d3a400083e3e12c96a1f568d3aa974e9001015d3a46c9f00080ae9d2002020008364b50fab400202b25a85f92001015d3a42fc900080ac96a1fb2200405e3e12f366364f8f1f0974e90008062dbc4f57000a03c7c2592d40008364b50010100041f1f09a755316de78f84d3aa800403c7c262dbc6c9f1e3e1316de17e48,0xc5b7974e91b27c62dbcba2e29eae316de592d47e3718b6f2fd4327ab8c5b793e94d3d5c62dbc4f5700a00b16de27ab8010058b6f13d5c1fb22c5b797d165b27c62dbcbcd98d93e316de364f82fc918b6f1b27c02408c5b78d93e0020062dbc6c9f07d5a316de364f8002418b6f13d5c00120f1f08d93e00028e9d54c5b793e94f4eaa27ab802023a75513d5c00011c5b7964b527d29e2dbcb25a800107c7c269d54ba2e3e3e12e8b880041d3aa9745c53d5c69d54ba2e20080ae8b8a7ab800083745c4010100041b25a87ec880020e9d549f4a69eae2c96a17e4800083745c4bf2400041,0x6c9f09eae0fab4364f83ead0008093d5c1f568000827d5a00101000416c9f05f920010117e48004040010716de5e6cc002418b6f2c96a00120c5b793e94c009062dbc2fc9000483c7c25d17100201a7552e9d2001006c9f07ec88001027ab83ead0000813d5c1fb2200040d93e0fab400020f1f098b6f1b27c69d54c5b789eae316de592d46c9f18b6f2c96a27ab8c5b7964b50004862dbc80108d93e316de400114f5718b6f1b27c27ab8c5b78d93e0804062dbc6c9f00080b16de364f8001018b6f13d5c01011c5b789eae00020e2dbc4f5700004716de0008000022d93e13d5c00020,0x3c7c2364f801405a75513d5c01802d3aa89eae0040162dbc9f4a69eae316de4fa532fc918b6f0bf2400202d3aa89eae0fd9169d543f6440080ae8b897e4800404d93e13d5c1fb226c9f07ec88010127ab83f64400104fd910020200083e3e11b27c17e48f1f08d93e0820078f846c9f0010034eaa27ab8008818b6f2f366364f8c5b7979b30bf2462dbc6c9f05f92316de17e4800082d93e0bf2400020f1f08d93e0fab478f843ead000106e9d2364f82fc9174e90bf2400041]⟩,⟨0,#[]⟩,⟨0,#[]⟩],⟨0,#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩,⟨0,#[]⟩⟩
set_option maxRecDepth 65536 in
def tier9 : Tier := ⟨476,#[0,0,284,476,476,476,476],⟨8,#[0xfbf7f6f6f6f6f6f6efefefefefdfdfdfdfdfdfdfbfbfbfbfbfbfbf7f7f7f7f7f,0xfefefefefefefefefefefefefefefefefefefefdfdfdfdfdfdfdfbfbfbfbfbfb,0xfefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefe,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefefe,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x7f7f7f7effffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xdfdfdfdfdfdededebfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbebebe7f7f7f7f7f7f,0xfaf7f7f6f6f6f6f6f6f6f6f6f6efefefefefefefefefeedfdfdfdfdfdfdfdfdf,0xfdfdfdfdfdfdfdfdfdfdfdfdfcfcfcfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfafa,0xfefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefdfd,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffefefefefefe,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff]⟩,#[⟨0,#[]⟩,⟨19,#[0x88000480ec911d5203a64474680e8b09d13145170892e1115c221b8441f32614e4a28c9253922a324346483880051b150d61a12c1c2582c4b054960a50014060f06c1b0983513069260d14,0x3000058020b001144002808250000482089011120061c0082c01052020a006080a010110090200a0000280001887e020f6041ea083d2187a220f42602808b624166482ca9059320b23416459,0xfe779fc7e7efd27dd74bf74d7edcefbf65f579ba7e974492e890d8004b0003240060082401017f770fd7e1e89020100400407fda0f8941f1223b24475480e9911d1a03a2c2744c4c10118080,0xc086180203001051020a04010008180182802048100880810440208204092080641009820080400406008090101041020220400c060000a020088000a00009000090000a3ffc9bfede7fd6c,0x2e8905b120b324165482c990591a0b22c960022a00050400a010120082080040800804010040200003e80c68018910012042200043f0107b020f5041e90c3d1107a130e0061a008320106202,0x74170dfbe1b224360b864170ac2e53d01270b84c1708c2e5145c224b844570886e1107ca20084400482001020020080400207e808fa249e4483a00474004e000190003020060080bd0117449,0xa00093e80e7829cd053960b32c14e4c29c9451924a7245464868c9071920072080e4040c804190023200124000c7a068f4070400e04034080380809010060103400848008300046000240001,0xc41738741b078360d84c1a8983493068a60004c00037fb32ff2cdfad6bedb979126f1435d286ba0a370a12d1465a286b250d64a12c828d8a86b0d0960e12c162582a4b052960006b22656449,0xfff0dff573fd5e7f4f9fdf99f9bf3d97e7afbcf3fa9e3413c14277f4cedbf9d341386826ff56df5f3af7f3505ce9d04d20a3a34133fde66d06cba0d8b4331683620bc]⟩,⟨38,#[0x8200047587cdd171d3aa9745c6e8b880041f457964b53c7c25fa86f1f0979b33c7c2592d4f1f0800202f366592d4b25a80080ac54300802b0d0801002c1c200100b058800106c15200020b0528000453d5c002800040400203d15e5d3a4f1f0974e92e9d200202f1f099fc1bc7c262dbceda99a75534eaa62dbcc1e0c0080b06c200080c1a8800107069200020c1a2800047ee9262dbc,0xba2e200400fd91000203ead000080ec91008023aa4001000e991002023a34000200e8b0800413a26200047d15e27ab8d61f2d93e316de364f8c5b789eae1145c008024497001001115c002024437000401107c80041c5b78fc6e3587cd92d4d3aa97d1674eaa4fa53d3aa800046c96a4fa53b25a8001064c2980802928a201002492980202922a200402486880080920e200081b27c00051,0x2fc90008083f01004000f604004003d41000800f486001043d11000200f42600044040100202cfe0c7ec893d5c1fb223f6440080bb6a617e48d3aa801102fa2cb64f8bcd98d93e2f36617e486c9f05f921b27c004002fc9000104b624008022cc9000808b2a4001002c99000200b234000202c8b200044020000041eda987d5a1b27c1f5683ead00010716de001200020000082e9d200100,0xba7e9745c6e9fa592d4ba74964b52e9d2364f8ba7485f922e9d200041ba74800046e8b8d92d4ba2e29eae2e8b897e48ba2e20080ae8b880080b25a8fc6e2c96a1fb22b25a87d5a1b27c1fb224f5707d5a0ffb41fb223fed07d5a0ffb417e483f6445f920fd91004003f64400104fab417e483ead002008fab400202f1f080280b3f8317e48bf50c9eae27d29a7ab89f4a65f9213d5c00802,0xc5b7800046c96a364f8b25a89eae2c96a17e48b25a800402c96a00090b25a800081b27c27ab86c9f040201b27c002026c9f000201b27c000204f570040453d5c000414f570000813d5c000112fc9003000bf24001002fc90000800401004000040400104004000011fba485f923c7c25d171f1f087d5a34eaa5d3a4d3aa87ec8b16de5d3a4c5b79745c716de1fb22c5b787d5a2e9fa5d3a4,0xf1f09a7553c7c262dbcf1f08d93e3c7c217e48f1f0841003c7c200400f1f0800403c7c200041d3aa98b6f34eaa27ab8d3aa85f9234eaa01802d3aa80200b4eaa00202d3aa80040316de5fa86c5b797d16716de5e6ccc5b7964b5316de4fa53c5b790021316de40011c5b78d93e316de27ab8c5b785f92316de02802c5b780902316de00802c5b780100316de00202c5b780020316de00041]⟩,⟨0,#[]⟩,⟨0,#[]⟩,⟨0,#[]⟩],⟨0,#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]⟩,⟨0,#[]⟩⟩
set_option maxRecDepth 65536 in
def tier10 : Tier := ⟨42,#[0,0,42,42,42,42,42],⟨8,#[0xfffffffffffffffffffffffffffffffffffffffffffffffffffffefefefefefe,0xffffffffffffffffffff]⟩,#[⟨0,#[]⟩,⟨19,#[0xb25a93e94e4000c000480002d93e13d5c20000300005f920a000100001200218008280102008040040400c04010040000404004000040000410004000047ee925d3a4ba2e2fc6e0fd911f568,0x3d15e78f84eda99ac3e74eaa67f06c5b797ea1afa2cde6cc]⟩,⟨0,#[]⟩,⟨0,#[]⟩,⟨0,#[]⟩,⟨0,#[]⟩],⟨0,#[0x0,0x0]⟩,⟨0,#[]⟩⟩
set_option maxRecDepth 65536 in
def tier11 : Tier := ⟨1,#[0,1,1,1,1,1,1],⟨8,#[0xff]⟩,#[⟨0,#[0x0]⟩,⟨0,#[]⟩,⟨0,#[]⟩,⟨0,#[]⟩,⟨0,#[]⟩,⟨0,#[]⟩],⟨0,#[0x0]⟩,⟨0,#[]⟩⟩
set_option maxRecDepth 65536 in
def tier : Nat → Tier
  | 3 => tier3
  | 4 => tier4
  | 5 => tier5
  | 6 => tier6
  | 7 => tier7
  | 8 => tier8
  | 9 => tier9
  | 10 => tier10
  | 11 => tier11
  | _ => blank
end CoNum4358.WordRows.BicolorBase

namespace CoNum4358.WordRows.FastJump
structure Jump where
  control : Direct.Pack
  desc : Direct.Pack
  values : Direct.Pack
def layer3 : Jump := ⟨⟨10,#[0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]⟩,⟨0,#[]⟩,⟨0,#[]⟩⟩
def layer4 : Jump := ⟨⟨11,#[0xa01402804008012023ff02800c0180300600c0100200500c008010000000040202affe008107ff00005bff,0x81403c07c0901c03a0400d01b01c0600c80c02c0580b016028048090120220280800e01c0380700e01803006,0xb8160280540a01502a0540a014026048088100200400840b]⟩,⟨20,#[0xb0002a200292002828027280261802528024000232002228021280200002]⟩,⟨5,#[0xac1f374aed65974446f6506537b9ac]⟩⟩
def layer5 : Jump := ⟨⟨11,#[0x815026040000000000b00b80f01a02800808000004038040000001b7fe06808bff01a040090320140ce00c00,0x4c1101581f050ffc1202507e0881e01e82704a0882304000c018030070420780381c00c0180381b0320581c,0x834125ffbff8320d41a02e096ffc2602f83105e0b4158280181c81402603c06021080075ff8360120b41502c,0x600b811bff04709e133ff7ff096123ff846ffe114218400620fc1e7fe059ff81683b0701c41b06e0340680c,0x9d0c4280470a011a1842f0950ba16c2c09b0ac26c2a09e0f41d0450870a4150280500fa1404507610421031,0x10ea1c8488710de1b03e07b0d41d83a8680e01bc3309c1442385108c0d41a432]⟩,⟨23,#[0x5010049c20092c001a40503451806800014f46819d00033800046c8008d04011908022e620856000ca0301930802245004442008800010f00021b10062f0410501018881030e0c061840082880104000206000408400808c01000002,0x142600a7c0014e80029960092a60124688246d10488080b062c16044013f80027d0004f60009dc882399804710004de4009b0201b41804650406c40c0d7c401ae0003590806ac000d50001290002]⟩,⟨10,#[0x10410100710036008190e4020d438008340dc1700433060000043200431004300042f0a4270540e,0x2c0a02447020461380701c4c01c4b01c4a0f03f020050f83b0143a0143d01044018030104301042,0x841d07c1e0681c06c501441913c171341705c4905c480581505013058120440f043ff0b80c0380d,0xcc4e12c4d0cc490c8310cc300bc331204f1204e1342c0b42b0a42a0a04509c2408c2508c2608022,0x12440130411004b110421004a10c3f0f43e11c3b1183c0e839ffc37144380d434ffc361404c1284f,0x4e1004d]⟩⟩
def layer6 : Jump := ⟨⟨11,#[0x7fe1582c40d7ff03205c0a0140f41dc0900c0142440880e1000183f80c0f202c0405100e0140180005004807,0x7ff0520980e034ffe09411038ffdffbff7feffdffbff820021ffbff81effdff8697feffe070607fe175ffbff,0x7feffdffc207fe0ba0fc1e04cffe0e83a7feffe0e41b0570683dc198300b20b80b7ff0580881a82a021ffbff,0x7fe150263ff84e1aa1306384a18822bff8480ba118247feffe11041072ffdff88b7feffdff8838422184403a,0x7feffe1742d09d0b1ffbff856036154290b2ffdff87c7fe1e2143ff7feffdffbff7feffc4486b1080e426049,0x876ffe1d4397fe139ffbff8710de1b4350b90d1ffbff8670c9ffbff7feffdffbff1342702b3ff8630c217bff,0x89111e233ff0dd115ffc440d6ffe21c427ff105ffbff7fe1a1ffbff8801861fbff7fe1a1ffc3e87affdffc3c,0x8b916e2d4590e51622bc560291562a01202314c074528a314227c4e89b131ffbff7feffe25c4a892ffdffbff,0x8e31c1ffc6f8dcffdffbff8da2b057c6c0e91ae354698d119e334658c918e3146104c094120288c117e2f45d,0x903201ffc7f10e1f5ffc7e7feffe3ebff7feffdffc7c8f71ea3cc787feffdffc777ff1da3ac748e71c9ff87e,0x154ffc3ebff7feffe483ff91f23a46c8c7fe1de45c8a912ffdffbff7fe290463ff91121dffc8690b21241c82,0x9432824fc9e93affdff8a2938ffdffbff7feffc3749b934ffdffc997feffc4dbff93125e4b49592924e49491,0x9772ea5ccb896f2da5acb40f92ce590789632c1ffbff95f2ba568699592ae554a995129e5305d94b29251ca2,0x3ff7ff30a60cc097f2fa5ecbc]⟩,⟨24,#[0x2588022490022302032187032080021f90021e00031d08021b80031a88021903031800021700021586031498021380021280021100031000020f00020d31040c18020b10020a200208800307800206800205800203a104020103010002000802,0x4a8d034901034810024728024648024481034388024280024188024088023f80023e80023d98023c98023b02033a00023882033701033600023428043280033180023080022f90022e90022da8022cc8022b04032a0802290002281802268103,0x7b010578a305760e057510027380037209037108026da3076c80026b00036a00026828046700026630026520026408026196055f03055d48045c00025b10025a00025900025800025641045487035380025202035081034f80024dd8044c0103,0xa38603a20003a082039f80029e88029d88029c90029a98049998029800039708029600029530029400029300029200029100029010028f28028e48028d00028b80038a01038754068610028500028400028300028200028100027f28047d8303,0xc7f104c68802c50103c40002c28003c18002c08002bf8002be8002bd8802bc0003bb0002ba1002b90002b76804b60002b50802b40802b30802b20002b13002b01802af0002ae1802ad0002ac0002ab1002aa1002a82004a71002a60002a51802,0xf60802f45004f30802f12904f00802ee3104ed0802eb3904e94904e78403e5a804e40003e28003e18002e00503de8303dd8802dc8802db0a03da2002d84004d71802d55104d42002d30002d18003d08802cea804cd8802cba904ca8802c98802,0xfa0002f90802f75904]⟩,⟨10,#[0x1445507c44134201080c0e04b128460c0470843610c3e0a82f0a4350cc370d017008190601601015,0x1fc2e1f0781dc2d078651681206c631641d0381c1500f068691745c06c0b1c85e1b46717c0014057,0x23c811308e12449234312348e0942d114741684120c32218260b08b09c850047a088820b82320439,0x2589e1540225402250532689c27c522784f144981405213c97240522449320013068101fc6510470,0x244a71bc9f24064188060146a198042545e25c6829461184a328c532945229c022645b00c5726002,0x406c1b816034111cc0c028731900918807184071606017c071c49d2986f24c7126ca41c0921b06f,0x1c4a0ffca807c191a81726470064680686f05c960501a19c191981916c180549504c171b4172500f,0x84b62cc211442913bff0902b088500a8212c84f084272c4232d07d078a22a81d284a9080730781d,0x1f8b02b47e0d0752b4322c0ac2bc312ac320c43314cae0c07d0c07b0c07a0c0790bc760b8280b852,0x228750f03b2203b21c852243b2109d21c7a1f4390e0791f080154b30dcae0d8761e0800d4ab20880,0x118752085d2804416c431088a2244121441230872108c1f8582848c22840220791ec3f2c8570f83d,0x2084d2a08f264671a04c1984b12864124601847e1245f2d8472d45e23c9211cb31207611cb211cb1,0x2849d168a11649b288a01649d26c9325892250542649125898240962a48c1bc6d2d4b41b0a621c69,0x2d8b52409c2949a28c9829c692a865298a9194a818ca92a0a418caa290a62789727c981745a288a0,0x218af2b89c20cad2acac26883208982c8b625cb1204b520095258b41fc9424c7c2d4b4248b524478,0x2d8a72bc8e2c0a5238ae2b08d2b48d2aca32d89f278b32c48b218b0]⟩⟩
def layer7 : Jump := ⟨⟨11,#[0x8170281e0350680cc1908b114224444097feffdffc0880f01a02bff80900c2fc020bb0042bbff800ffdffbff,0x83906e0d419830ffdffbff7feffe0bc1682b05209c127feffdffbff7feffdffbff82304207c0e81a1001fc0c,0x85b0b06b42b7ff0aa14c2884e099ffc2684affdffc24846346114217feffe103ff7feffdffc1f83cffdffc1d,0x86effdffbff7feffdffbff7feffc1a8340660c9ffbff7feffe1b43586837219bff8650c61802003effe17c2e,0x88effdffbff7feffdff8a47ff11a22c4488710a208567ff1021fc3e7feffdffbff87a27c4f43c8770ea1cc38,0x8a8ffdffbff7feffdffbff0ca2902dc5323affc5c8b827b14a28c5089f13a26c4c7ff12e250a915112495c48,0x2b518a30c608beffdffc5e184304a714d8bb1722dbff7feffdffbff7fe2f9ffc5a8b31622b86f0dcffe2b455,0x7ff1ca38c708df1ba36bff7feffe3646b8d434234bff7ff1a1ffbff7feffdff8be8cf19a32c648c6ffc6615b,0x1d23a23fc7e2dc5b63ec7c8f638a3d4792d65a9ffbff114ffdff88b112221ffbff7feffe3c4778ed1d63a473,0x92123dffbff7ff239ff8dc91b231ff8d67fe248a283a91722a449732e522243c8690b211ffbff90720a40c80,0x7ff27a4e8cd19a32063c9c937269ffbff932ffdffbff15affc52c9892e2c458c961582ae4ac94927249ffc91,0x1552ba56cac9572a81b0e61c0ffe54ca894f29a52ca4947288bd1797feffcc8bff321285ffca093e33dffbff,0x99131e634c598930e614c19812fe5f0b097b2f25dcba07e1081fcb99703825bcb696b2d259cb29632c257984,0x9c137cca4de7ff375ffcdc9b614c8ccda9b24626c4d79ad3566a4d39a5346684cf99d33423ccc99732a648e6,0x9f53e67c4f79ec4667acf49e73ca78cf09df3ba76cec9d61802e85d9d53a494ce89cf39a72ce49c64ce714e1,0xa2b45289d12a23441ffbffa1f43a86d0ca1649ca450aa134228386aa0d41682503a05406804ff9fd3f67e4fb,0xf94c297d2ea5b4b295d2a2314a694527a4d49692523a454869051f0e947a8ed1c29746e8d519a3145cac516,0x2644c6a2d447ff50c46542a83501ff94b2534fe9f53d7feffe9e53ba754e4b4121a714de9b535a694ce99531,0xaab552a9975aa5546a83ff7fe579ffd4fa9d534ae15c26e4daa654b1aeffdff9347ff52aa4d48a8e54ca9d46,0xac8ffdffbff34e6a0d45637fe6a0d3d627feffcd3979133584bad60abe5d2af55dab956ead559ab155eab174,0x640d456c34f5aeb5569ad159eb3565]⟩,⟨26,#[0xbba4182c03050ac00082a00020a08010264804094800823830308a000821020307e300c1e0403072000c1b10030682008183804058201015180205000081283030441c0c1010020371c140ba00402ac00808c80401e8008060903012040c03900200a0008001205,0x18c000c608205178bc145c380416a0c0c58190515c4008562002152000c53800214a0008510c0313e3c0c4db80412e00104a000311e0814459804110080c42810310640084080020fe00083e80020f4100c3a96050e4440c3800020d640143488020ce000831e004,0x23c20088d800323220088bb00222ac008890a0321e080c85800420ec41082050320164107e18041f080107a83031e4240c7781031da00087580021d240087306031c800087082031be20086e11031b440086c00021aa0c0c69010319e0c0c6690021960008648002,0x2ea2008b988022e20008b780022d8080cb482032ce0008b280022c62008afb1042b66010ac98022ac000ca985032a0000ca70002296000ca4060328a080ca1900227c00149e000227500089b2104264401098080225c2008963002252100c930003246000c900203,0x3b00c14ea11043a48008e700043982008e4880338e4008e191043820008df0a03376200cdb0e053680008d8810335c080cd5010434e140cd112053402008ce5804330a010c9860531f2410c6030330e0814c280023066008c002032fc2008be10022f20c0cbb8002,0x48020091e21044721c0d1ae9044662009160107452000d13800244a000911020344000090f000243800090c89034281c1509080241d801105860340d0815000e063f98010fd10023ea1814f990023e20008f700033d80008f500023ce0c0cf1e9043c0180cee8103,0x54a001150080553c20094d810353220094b8002528000d48820351c240d46100251400094213064fe04153d89044eee011391c054dce4113384074c704113088024b684192c80024ae00092aa0024a6000928800249c140d26000249400092408024898011210002,0x608000d8029045fc20097e00025f400097b82035ea00097904035e0000975be055d0080d7300025c210156f02035b210156b80025a7241168020359a000d6502035902009631002588000960810357e00095de00456a6019598002560140d5700025580009548803,0x6be2009ae80026b60009ac80026ae0009aa03036a14011a4bd0768e2009a280026860009a0880267c000d9c940566e000999010565e240d9602036500011931002648200991000263d24118e100263420098b830362a000988d80461c280d8600026121c0d838002,0x7787015dd20027702009db10027654011d800027560415d4980274e0009d102057400009cf0002736000dcc800272e2009ca0703722040dc681047160009c3d004708180dbf81056f8100dbd00026ea4415b990026e20009b790026d76011b409036c60015b08802,0x84a0c0e11000383e000e0e9802837000a0a8a06822e012060605812000e03800280464160000027fa140dfd80027ef2011f928057da0415f588027d22009f309037c40011ef01047b86009ec81037ae2009ea02037a20c0de680047901c15e30802786100de08002,0x22d0a058aa981628240589a1c0e243c05886401620010387668161b1c058621c16160705854000a140002]⟩,⟨10,#[0x2405a1308e1c8811ec7d140531d0801e4771cc701f04f198691706418852178581a0440a0390883b,0x28c1c274b5068b22841f0841b11c991246c18c941ac822544e1a84526041258671fc4324c781f83d,0x348da350bb364a0ffcd30b02d08c1b270ce30cc6328c02fcbd2e8c509c23098a5078aa2c09b298a7,0x3c83e0dcde3c0253b42b3103a00cee010eb004e40c4e138ce70000037c290c024074de000a2268bc,0x2c4053e0b73e4052d0f63d4b3118382bced017ff3c0ae3b0053bcf4320ac2acf331c2e108023dc02,0x1311e46d244811145d1445510458064490f4891c4344d475040690348caf3102109cfb1202f334f1,0x4fc1e4a86546129150604dd064c9364c5054b10c1550901d0401c59128084090a404094d45b07051,0x42d5003d0016851089474f00e18541155264e00c1340d2d8ad521214d11f5100b4bc0a4b91a1841d,0x455453c10588245854c4694b4655c41d5344c6d1d50e5650803c0f40d55435521c44b5440f4050c,0x554c0552d2182a20c854b0150a0511c9675552333d6849d5e05163494131d8cb581640947a32412,0x3756f3fd3a5753936c2d244565c5584ccd85a54a35c840ad575c0d5235560b06e23c164c12a21d2e,0x344880c8d0061433a8855097639d75398e505c83500e35d87624884384e05d08f245355456c4ed28,0x25d24240444783b238970e54746c9759d494f9773f4fe57d78518193f1663e8f91e9453dd653e08d,0x5f4ae2849c618a227422617ff5f0b428022610b45ecb5619852c8b55f8b42cc9a5f97c5ec9d594b7,0x290be3418e63fff2f4a33309f308be278c1274bc6342826cba630bb0a0c5630b827ca42a49e2a0b7,0xe58c610f23a8e52a4d0388e8308c10cc332a18f300df29d8e2998f2fd8e37cd861d7f374dc358d1,0xf8f10f0f13bcf93257d3b0d50f4f83d8c6350f55f03b34cf20ecc33d9863ed910e4d2634f55ed85,0x3d4445f8da364f2111813f443624fc3958010fff3e8fe3618838ce432ccc38840384e02b441328df,0x3e8dd3f5826284864447640b93a4b83a04739ce611ccf118f43cc452d8ee3ac4536cf7634b53d8ce,0x2709b4090513d26138ff661133fd0e5e995651971310964d0826992ffc4c6598b3f84960cfc3a849,0x65d394a12d5fc535e51a14d1949c53485181490c439264950b47d0a66c514249d4210141c504019a,0x17d1167c5c674a3679106705c43d0e4e90d42d381650715d0728109168a216908685002850368058,0x60d4250463609284f86267c622999e4553e501814519d4fd2e4c13c4b53b4f52b4bd124d1291792a,0x501494813f601464cc672ad9c470aa1993150d304b142501414b51767d3f1919dffc646711629c63,0x1b141609462d9442d53566d38494b14e9261acaf2d1992b9981a9395159e488692c1362c86868123,0x42472ffcbc421a61c99655d022e904ffc705659255d52699596555764d5661d4a5086c50d3c5253b,0x5e54e56d4d5694f4494c1d14b1d15e441a31cda5689112f4736910fffd5d4395442871419051c0bb,0x1ec7969561459a330117690795818b57d15695891e1881e15f5287768d612fd60689141dc755e874,0x325635655166d506691f5507f560c755d99311655597d1f9a2471533187d590c54747c590c3ffd9a,0x3452b5356b2256a2256d62966209263355d6912259081ffd5c338cb588805848032920583ff59988,0x359735c96a5bcd56555968555681506508e34cd4239935c17034992685a653d2f4b56c61d695fd6e,0x625775009360493601785a4de37d604fd614f4dc5cd6effd725b57136cd92419736890659705ad5a,0x3c1633bd443b8ed5c1993d4f225d713cceb258ec255983c56f5089462d7860d77629412516c588e4,0x5f193665944797b6491b6659b629896218762d7f6018160d8226590265765a0995d574520983d964,0x1a46959e67d8f671a36898e6759b6358c59da66199a681476158466da15f9964919965d7d66195]⟩⟩
def layer8 : Jump := ⟨⟨11,#[0x7feffdffbff7feffdffbff7feffdffbff7feffdffbff7ff005ffbff7feffdffbff7feffdffbff7feffdffc00,0x7feffdffbff7feffdffbff7feffe024037feffdffbff7feffdffbff7feffdffbff7feffdffbff804ffdff8b8,0x7feffdffbff7feffe03bff7feffdffbff7feffdffbff7ff019ffbff7feffdffbff7ff015ffbff7feffdffbff,0x21b8833ff7feffdffc097feffdffbff7feffdffbff7ff021ffbff7feffdffbff7feffdffbff7fe4d5ffbff,0x7feffdffc150261dc3b00282904c8710d8250460840f81d03606011022048088120000040040b81441c0006f,0x847089ffbff7feffe10bff7ff0820fbff7ff07a0ebff7feffe0e41b7feffdffbff7ff0681b3ff8330620bc16,0x510f61e43b8750e61c43786d0d61a4338650c61804285f0ba16c2c8570aa14c2884f099ffbff7feffe12c24,0x372ffdffbff7ff12a24c4888effdffbff88d115ffc4405510dffbff7feffe21441880ffdffbff87effdffc3e,0x8b916e2d4598b115c47bff8ad15417c548a714a28c50116ffdffbff7feffc1702d89f13a26c4c27affdffc4b,0x6d1c9ffbff7feffe38c702a11be3746d8d86e635c6a8d225dffc687ff19e334658c918e314618c117e2f45d,0x3f2ffdffbff7feffe4047f7ff1f85e8bc7feffdffbff8fa0e23e47b8f51e63c4778ecffdffbff7ff1d63a473,0x92e325ffc967ff2564a4939252464848f91d2364648b915226444872b721a428c27ff2101d483904555ffc81,0x9552a6544a794d296523ff1d8ffdffca37ff289ffbff9432824fc9e93b271ffbff7feffe4dc9a2be7e64cc98,0x980ffe5f8ea7feffdffcbe97b2f25dcba9732e25bcb696b2d259cb29632c25784195d2b5ffcac7ff2adffbff,0x9ab350778f046b34e694d109412cbb4d099f33a66ccc99732a64cc898f31a628ec7feffdffbff98930e614c1,0x9d93ac7c4ea9d33a273ce60ab395ffce49c7389ffbff7feffdffce11ed3826fcde9bb3726dcda9b33626bcd6,0xa08942818627ff40a80d009ff3fa7ecfc27b3ee7d4f99f0ffd24cf79ed3d67a05b7ff3ce794f19e13be774ed,0x4834768e51ba354668c517a2d454aad14a27449ffa57a23440343ffa1f43a86d0ca1742a84d08a0f4187fd05,0x4b095c8510b2c0ffdff90a0e4540390732be1ca93d26a4b490b2909a461c5ffbff20c1ba91149a434828fd1e,0x2ed4d037bff7ff4ce99531a614be973ffa5a582963ff7ff4ae95151a52ffe9416a0ee1d88690e49492485151,0x7ff532a5d4aa93522a3d46a8b512a1d42a829c6a053fa7d4f69e53b2c34ea9cbffa714dca707431f4da9a96a,0xacc92ab2bffac958eb13ffac3581ffd5fabd576ae55bab5566ac276aaf55aaad54aa6ffea9551aa153ea754d,0xaf15debb575ae95cd2aa47ae44311abff3995c6b856fadd5b4b2d6cad75a9ffbff20effeb4a58ad0ffdffd67,0x7ff64ec9591b2163ec758db1962ec5589b10ffdffd87b0d616c2583b05606c057fafd5f6be57baf48e6bc979,0xb2d656ca3ff]⟩,⟨26,#[0x116000843110510880084082030fc040c3d81030ec34143958040d29c243380020c2b4182f0c030b6040c2c80020ae00082a80020a60008254f090904008230002088200821000208000081d900506e8010180107052681c0ce01002e2008090a0501c401000540e,0x23660088c0203227141487c904214701483700420440107f82031fa00087da0021dae03873c8061bc40246d21041aa4c14671207192081462a904186000860020317610145b01051642410577004156200c54000314c40085200021369c244c9002127101846a306,0x326040cc6240730a1c1cc001052f6cc14bb06052e6040cb898022d4641cb430022ca000cb100032ba0014ad00032a91018a8800329c1c0ca6280228c1c18a0850527ea0089e8002274140c9c200226a080c99020325e000c96880224ea4189280022401c148e8003,0x4140c0d038403400481cff10023f6080cfb0b053e02c18f683033d68008f402033ca000cf104033c00008eb88093aa0008e78c063943014e381033840014df820337a2008dc880436c040cda300235cd418d5800334c0814d129043400008cf1802336000ccb0305,0x50c9019420002502040d3f04034f6000d3b12054e6080d3800034d670153402034c2141d2f01034b6000d2c00034aa040d282505498a41125000248a9415210403477241d1b0305462141514440944c200910820543a04110d020342c001108cb0541e8009069802,0x63440098a8f0561d141d849e0560ae4118101035fc44117e18025f4400974cc115ce00097112055bc80116c92055a800156808045912c215fd709578000d5c300456a100d581e05558e01154810354ac41151880254200094f040353214154a900451c1c1d461002,0x6fe4009bea0026f4040dbc00026ec2009b986036e0100db680036d4040db384036c8240daf9a056b8340dac81036a83415a6c907694000da38003680941d9e8003674140d9b8a0366a800999010365e000d960103654000993840364a800991000363e540d8e0303,0x7e44415f808027d8e411f500027ce040df189047c26009ef80027b4c015eb81037a42c15e78503798080de340067860c0de009037762815db04057607019d4970774e4009d2100373e1015ce08037352009ca22067220c0dc60805712080dc3a802708040dc08303,0x8e2000a3700038d8a00a3487038ce200a3200038be0c162d01058aa901629090389e040e25610588e040e2280028840c0e1e9a05874100e1b8303868080e170506856340e13800484414160db5078274822080403819241205000280a941600a8047f8fc15fba105,0x9c4000a6d22089a3742667000398a7026618002982200a5ea804976800a5c800296a601258020595c000a560802954800a540002944f01a4f1904938200a4c390492c400a4a100291e1416469002914340e43800390a000a4033058f600163c80028ec000e398003,0xac2000eaf0003ab40412ab8303aa8100ea86904a904022a28203a8360129dbe06a6c7816989305a5e600a960303a54600a928005a46000a8f8004a3a000a8db002a30000e8a8303a22e412870003a16080e8312059fd80227d50049ea08167812059d4b81a721106,0xbbce012ed8003ba8ac1ee61108b849c2ae00802b7c000adc5406b660416d69a06b506016d18b05b3b441acd9802b301c0ecb0002b28000ac80004b1c400ac51004b0a0816bf0007af8000abc1104aec200aba3002ade7416b68802ad6200ab49802ace400ab20403,0x3158002c52000b130503c46000f100303c3900130c8c03c2c100f092804c1e100f045007c0c000b020802c00a012ff0002bf6080efc8002be85c16f88503bd81816f48a03bcba012f10503]⟩,⟨10,#[0x3e440417ff230c3ffce93887f398c531081244902cc800ec54ffc3f12430ffc6c1845618c6dffc57,0x4dd2619d28191274c45a15917475251311513fff283ff490f4294d23c7ff2410024d04ffcc03bbff,0x713305d0f2e41b1d10c06073068191c92effd2f0513600cb439c8742c16428151c000045082c939,0x5c44d0dc390e15c55d5654c3c0a42b0b02dffc354fbff0c9434e940534280a9470c9454fd440c475,0x65da2199405f0471493e6559b658651985c6018e54d7b16445144581657f5f986120465c84d5c16f,0x60c606114819c53ffc5a665985615a65c3219982605435298050994165930e8010bc015f46b4ffff,0x65581139661a85d5fc3455d68650035ed56508435f9935c83d61d6f58d710cd7058c4d61c4100871,0x5a1a159d8d59564ffc506259d13d7562d5e1c18c531796797d609690f9965153a00d58513ff1117c,0x4edb61f47e1ec7c1e829618791a54a571855255b1a4785699b51c5f5199a5645e5a54d6887863879,0x29c2c1f0892789a2749926d3c768a2765d4760a27442b221ba25892739a86f4881e9c1239c26fc92,0xc5e36f1f2011412b9e72b5aa7bdf06ec047c4041f49b270047a9ee2b1d57a4ad7b5e42ade574c8a,0x281c70d4b70249376db02b7ff70c812b0b5518926b48c0c9eb2d7ff015c06b88d6addd779d70187f,0x1dcc2bca172c82779ca795c56c9c927c0b0d3ff251dd6ade4715d320c0affc3375c9f6c408720a9,0x6edcb731ca2994e720b52ddec01dcd2d8a4260b02194c52ca3215d9785d171884751c6029d8289e1,0x835f731cc67d5a77efff6a4ba1ecc131a027f1ff7d9b42b8a5740b22a94f7c5ed6c5ae538a852d4f,0x30cb364cc0322087a2436e103762386cdc83a1a340bb338cd33d5232e17858d384a1583cd32e837,0x6bcbf6b1fe0361f850dd8ae2a7e80d8643c200be3687e0e40c55228032297e225860dd37a21ffe27,0x869ac8603e8a9b403e0634bff344e403db3816250f60303bff83bff2121436e00889ad319b030221,0x5748503db682cd5828e0824df3520483e2603a168548384a0434e2620a0886e038adb581cd132010,0x8ddf439629589616cdaf88ce3575f85893b82a0b58627820d88140f6de0c387ff218d73a15e328d6,0x2f8ed945ba4064d948f73ac8a2f1f690e4b3f23a7dcfb3d8ea3e9f53ee3f9123c224bb8d9b83ccf3,0x7f10904c426fa43710c6804927f5c32fe40315bc7ea00234918f5bd90a4c7ecfb93c123e0123fc8b,0x940c84423f7fe4f255fe8f894ffe4e3c8ca59098051a8ffe3d10dfd6fe4d8f24c0523a69dbeffc44,0x5b64b7356a5b20c82566ffd088e7ff8ca54819cbffdd0919c73d4f4ffcf373e4294511704c8905c0,0x4622e970cc114eb40db85ba3773da9912025b7ff711025acfe806527096e3f5f48d96b739114420d,0x5a314481646a301209e3409d33dd6482614826284c9c8be603b447118ce268cd2651896dd297611,0x46234768d18ce1727ca2134d3126595d4f235d1e48916290d65d01a5cca3068a148d1b1391335232,0x464f5770d897a3829a38978505e25c47177981148bd745de2e5e1738c6344f23054a333ccee76d20,0x9a128610dc4c23e3ee65151308745999a6414cfa60d2607a1c3663b9bcda148513dca77717a4857a,0x4c9893f11508a692a988450239905e080fe77e1e07fff6425a840fd4a81d615df969e0ffcdd96457,0x78a6c63117378e22a628922209a4a891e6687d304c98b385164b246174df44d349152b449149a98a,0x4059849de6649d24b5e2975e0641296462463c218465b6481f63d8b91554921914658891c2163518,0x990368e5f7be2c408696a8257a663ffd9a7b0242b62c8b65f664ab9a0617a066996671826379c24,0x9ae677aa6d471a067cb147d9e2c11e46e544b0af1a93846a534ac276751d9b26b394274719c4b5d5,0x699a684d2affe618b5297b9a468e3b67da594e56505f067255485a4684279b9207cdf2958e4954e3,0x2d922590e81c8b5565047ae228746d7a13179a1c4dd484c24e78ce6902192cda59bc277cdd609a62,0x9ca7c9e6765515f549559c6759c2734f5504ed414f16c6dcb83a5254d5394926e59d6648d344e10a,0x671a55e2705b18a5dd776214f63d5d5d14b5cc739f9a062a7c9ee759ea799ee779f6739c67e9ea76,0x6d1aa6c1b79c3ff6b48769e7fa013affe826a1a45e9915b9909d3ff9e1a364bff69a7d1d5a05e162,0x509446f5e8a0143ffd407a1eb9fe84a0d3f7ade37993e6ea827a1ec755d29d1d676db89c9c96a681,0x76a726c9c773674781ee6bdc37a9496c1e9711e7a054877dc251a846b1c06f1456fa83ffcb46fdad,0x8668554df6889f5a021c8768184213846787d27781ddc7c1d09ccb976de27cdef73db5769b67c9b3,0x9e224809b056e2c882006ba01879596adfe55dfa39e85ffdfc561fd6b556875fba0a1d7de229fe1f,0x71a86a26768be576edf99c6879f68a925b97e22e8ee7ba1e899ea776d5b285e286c617832069c22d,0x839d19667343dca8223881e34a296782e56816348cdc9921cc8cdc88c64542e3094e0480d6371688,0xa267976e62976788de5f96a5b8da7498616965d985172a2215a19d85c5d7751d384a885c2865be0f,0x906687757f8fa3d6057e8f2654be809ba6cffe18a2a68a117da0d7c5efffffe7f8ea654ba859d687,0x9f26a632279798d625e18962661e596122399e8160d859126390221a118088a43a0e8686dde60a1a,0x9499866a6465deba15e58ae889a22a941966524e791366564c64e4d996829f5339726d9be5c8a66b,0x27e9b6609a9f198269a29a167666665ed]⟩⟩
def layer9 : Jump := ⟨⟨11,#[0x82b05209c127ff045ffc107feffe07c0e81b0320595d7ff02a04c0880f019ff8fd80b01201c027ff006003ff,0x7feffdffbff7feffdffbff7feffdffbff7fe15611c228430820fc1e83b070b0bff83706a0c90283105dffc16,0x7feffc348547fe925243ff84cffdffbff7feffc07c25018085ff836003091ffbff10a219ff88a7fe22dffbff,0xeaffdff8790e8ffdffc350790d030c3307217e193ff7ff0c61842f85cffe16c2c8570aa14c2884effdffbff,0x7ff0fdffc3e87affc13bff7fe18c303ff8790ee1d4397feffdff82d056ffe1c437026ffdffc367fe19c3d865,0x7ff10dffbff7feffdffbff7feffdffbff885106203ff7fe0f81e008008ffdffbff7feffdffbff036061ffbff,0x7feffdffbff7feffe2505b7feffe24c487fe0bc1601902effdffbff7feffc0fc4703b1180500888b111ffbff,0x7feffe2a3ff8a7149ffbff7ff1462844f89cffdffbff7feffdffbff7feffdff86f89affdffc4c896ffdffbff,0x8bb1722dc5a7feffdffbff0e40a9ffc598b0ffdffbff8aeffdff85d02d159ffbff7feffe2abff7feffdffbff,0x8f11de3b4758e808a39c7202f1c63846f8dd1b63646b8d51a6344678cd1963200d8c71880546100d1822fc5e,0x92b25249c9292324247c8e91b23245c8a9120ec1cc8890f21a42c8490720a4082c9011fe3f47d8f91ee3d479,0x9652c6584af95d2b6564ab9552a6544a70db29a5286794928e514a194127e4f49d93926e4d49993125c2c496,0x98f31a629a3342680464c498730a6088c9812fe5f4bd9792ee5d4b9970310618c210f2de5b08796b2d25987b,0x9cf39a72ce49c738a70ce09bf37a6ecdc9b736a6ccd89af35a6acd49a734a68cd099f33a66ccc99732a64cc8,0xa0740a80d009ff3fa7ecfc9f73ea7ccf89ef3da7acf49e73ca78cf09df3ba76cec9d73aa74ce8]⟩,⟨26,#[0x27c94449c1b06261a020956606250000883912120454147d59081f00008790d061b4a860658f0f18aa4185f8a06173881859820614700404e67071164444448002104281c3e39060eb801c2cbe1c0a6cc18288802092e820220f05052446c0d5c0f0101448004208,0x43980110d500243000090b080242820090900024202009058b05412800903800240a800901a8024020008ff98023fa2008fd90023f20008fb80023ad5c84e80906392101ce1cd0637ad018cc95243264418c4af0a30e0008bddd0c2f2a008b58f0e2b95c3ca7ee0d,0x514801143710450440113e85054f2e4113b80024eb00093990024e2800937c8024db000931700b4b208252b88024aa00092988024a2400927900249a600925a80248c141522080248100111f200247800091d1002470a0091b18024684009159c094532009100509,0x6f00411b828086dc0009af8e0f6b74411abb1046a70411a703056940011a33004686000d9f0205668442993230e64820098f85056269831851c0961000097ce40f5eaa01178b9045d800157410045c60c156f98045b8080d6c280459c84295f950f5494c6d473016,0x89a602e1f010f87400121b18048650012170004854c01213390484444120b4d0c815443200af097f69819faa0067de8c19f4be067c6fc19ef00057b5a011eb60047a42411e720047920415d6b41c72b2461c8800471a4011c498047080015c050046fc0009be0802,0x9f10012789e079daa4127580029ce40127082069b860166c01049a92012669e079900016608e0797c280e5e180296e08165a900295a6c2250280d93840124c400492844124850049198012441804908a4123d0d0a8dc08323585038d2200a32c0048c6000a2c140b,0xb722016da8104b5ef81ad4ba06b480816cce80bb245c1ec4290ab08e012bda309ae8501eb69707ad2e412b11307aba7016ab0b07a8edc3ea00307a7c600a9ca305a66981a970005a52241692a904a4344128e8004a32641289a206a1c1416831208a0204167e1c05,0xd980013633f06d7ce02359ce0bd5a0c1b4ac318d26800b479104d12401b400309cee2027399104cdec01331190dc8e646f1c160fc690413179305c51281f114306c111c6b018905bfe0012fa660bbd7b826f29b06bb5342ee98407b8e0032e20203b84600adf2104,0xdef181b780607da69877680303]⟩,⟨10,#[0x370a12ffff368d4378b2294d2ffffffffff28fff2d4d1367ff2dbff31cc6340b1338cdffcad33cac,0x423ff4c106451233c3ff4d3ffffd1f480a2ffd16ffce93ebfffffff410c8324be270d5ffca02e7ff,0xfffffffd69ffd4a38d334a5104550f4d5323fd264a12e3cfff49cf23e1244c52538519484e0fffff,0x5dce75a0df5f97550974505735214efffff29972ffd6d567ff5317f53d644e7ff5c3ff5016effd84,0x6a18b6d58affd8effd3e691b7ffd396359c6cfff69d8f4e3ff6b15f6095659585ffd79605555e180,0x784f7741da780ef771cf775474fdd977da96b994689b6ffce9ffce8ffceeffd976d19dffdaf631b8,0x2d55482a117f3ff7a9e83e7ff2c7ff79dce7a7ff70de6631e5525c878dd6789ca74dd26f1bf75de4,0x70a0f823ff7021584d0353a0b81212561fd80100807ff7ffff537ffffd4bffd927b1f6ffdbd85fff,0x2fa348ba23fffffffffffffffffe25fffff417ff44560ffd0fffdc9ffe1a41df181a167de14861c1,0xfffff7ce378edeb8aa1c72e398b5cc737ff8ea3289d098da2f885128d5627c999893ffffe38883ff,0xfffffffc3767d1cffc6c15c0366e3dffc2303513223ff8f3ffffc0e6686b58d6c1588900822ffd9e,0x7e24631642ffc6a1561987ccaffe41167ff204261b411307ff0e05830240040cbffc6e1fc257d1fa,0x6c228fffffffc836983917c071d81a1107d469deffd6a90da50d6474742403e1d1f8007edd8fffff,0x147a0bbff0b009fffff4d91e814d3fffffffe501e0175bc46493ff74576ffc62ffe4effffffffff,0x358670d12a1efff94440fffff1a0330fc0a07c4d0f44b1f031ffc06078661243b1dc0b0c0640e81c,0x1cc4c0c8480bc7510c7310606ffd7affe0c75226083ffffe4bffc4e80a29fffffffcccffc846abff,0x215f595c90262074de561281d194471844510819ffc9186e5421a2c2618394c3e19c3b194611dc5f,0x5f49b07c320c41d01819010170a0146b7ff879b28fc1245d2c9a24a13e3e8256609db15f1ab7e669,0x843ff7f96b934dd16a4c13c9a99c9999894996642560d9892d26c8d9848bffd1897a309708a23967,0x2909effcb32e8ab274019f47114c70178291485117015143ff93e458cd1b36c6f363ff4be2235e44,0x9de80a1272fffff9cc049c2719e674ffe85ffe75a0e822e0a82a8b02bca72f4b727cae2a4bc2d0bb,0x46bffa226effe89fffffffe6f9aa78ffe6ca2fff9ae6d022869f28affe76ffe7affffffffffffe7b,0x42a9048aa004cef37ca0a47ff4169ba729d03d1c9a91dffd13ffce8a5e99a53ffa63ffffd1b27117,0xa4e8effca14691e4bced3d901398ec438f5394fe390eb437ff27cf43a90cffcfc2790b3889d3c4fb,0x75119b7fffffffa8ea44daa5a3e9a474e7ffe6b41d124dea140cf70669fffd2ca5696a7902ffcee,0x4fc275b14b09270ac2a8ac6b3fffffab96bac938ffd6328fff5aaaffffff59aaa07e6f9bbffa4aa6,0xad0e64f55751945578e54f1532a1444ed523915c4ebff29d5b545432915a540e2ae571a9ca5387ff,0xb1c369d031ab273ae032ffd5853583ada7151d62ad42fffead5bd7cffe8f4faabaa561ffe8effd6a,0xfbfffffffffec4b62c2ffe75b0d93624ed4f4ec621984f0aa6453b61fff640eb4e9963a8a961995,0xfffffaffffb0676fffffb27ffaf3ffb42d1af6c0ffed90f2cdaebffb4ec5b1bffb3ac8b5a90fffff,0x6f8f63d588515c72c1446ed872bd43719ba714ae618f4710abffcf16e7ffafad4ffebbb5fffffea7,0x13cf8523ff709deb7a9162dc1732dfaa1c0629de72cad762db3cedd50ada76141b70f22b146627ff,0xbb7ffba7ff7ebff7eedaba14affee7636e67f9f8bb0b27e6a9ffdf49e2bab8e77b82e2aeee1ffdcd,0x8258f64dbe405572e19154dbb3f9907c1527bcb7545ba2d1ee540fc2cded6e4fb16deb6f18eaf055,0xbc2ee53ee5fffffbdabf836bd3fd567cd4cfffff6ffffbd2e4aabffaacfdfffff2daea842ef809f8,0xffec21a904ffe1f2e594876f7bf3ffbe69388a1987bff9e6f380c5fb06c0a4861bc865bc6eb831fb,0x439c76615e435967c15c7bd5b718bd714bc431952ed5a42dee2e9c47b50a721971bdf1b6ef8bf6fa,0x9ea2bb1877c02acffec51ceff1d630fff0157d06b0d1072ae4ffefb576feb96948cfff2fe9587626,0xbeaddbe564b72e9452e73048686d6531af88faf7672ad7e115301f5217ff676e8876968fee632303,0xb22af45ab1aaa3c90efbbeeae915a2468c9ac08a59d9a886c720aad90642a4ea990bff9029aa59fb,0x9ee49b0a46af2489f2c9bae9ca619f5a6ea90e94bae3d31fff69297a6eea5aa444608b7f59bffd9e,0x2027dacab3b7d1d882ecbb4cb86a9a9f1fca7699b7bffbf1f69eccabf6c99aa4792249b22479c246,0x335d8499d3245299fbff7497923eaea39a9344d4ffe97b92e6bdffffffff69c8e81227ffdd0b2dcf,0xb3521be2e7abd275d2dbb292033adc496ccad9d982fff47dd55ee7f4afff8b0cc81da892898bb973,0xffee8356e55c2f96b5785b9daffecf8bea1ffeca4a2daffccfbb975b756db39d948ab76acd2937ff,0x90aab83ea36be32779db83a31b54d026da69312d5f6cab4afa48d72ba7ffb46a25c5daffe4fb4298,0x9afff8da13603ffa1bffb36b46c6ef35e3577eccffecb94d3198612ffe71ffea4b5c9624ad690e95,0x98fff9fa57ffec34ce5ea0614609e2952bd98a876067e785328de80b42fe361b2a7acf959e0b2e5c,0xffffffffff947ffa2a6635a7fffe46bc6efa127d94af0afefeffeff797ff85257a0e5fb1255a22be,0x9cf00b86c599bffffeffb525d9b2604c65bb4e72986f0bcad25fecfa2de74c285c02d2b31e6b8267,0xb1fffa7a64fffff91ed7b59b0ffe50ad1e8997fffffff9b6b5b5658a7ee2a9665ffe49ad6b8ffe5a,0xffedeaa2158e68c7fdb5ffe679966fb1a66b06649d2c0bca48bc6e399e6e993ffffe59a9a9ffffff,0xb6302bf7ffc0534a16b7fffffffe8424e82c09e380de38053585a81c06fca64db9a2b0803ff6da80,0xb7db888e866de69bb3ffa3eb2a6fff3768db6211a06b87a675ac6f3ab3fffffffffea0ffe0affeb6,0xa4bffa868bae7ffffef6a73ffbd6a4b668abd8978ae89792f5792878eef4616258623aa46a3a3224,0x28c85e38a76b3a3687a36a5a99eab6634a8bff613ffbb703bd3fffffff8bbfffffffffe76]⟩⟩
def layer10 : Jump := ⟨⟨11,#[0x83f07a0ec1c83706a0cc1882f05a0ac1482704a08c1081f03a06c0c81702a04c0880f01a02c0480700a00c00,0x214c2884f09a12c2484708a10c20]⟩,⟨26,#[0x698e4fd9c4b146618c219601046500411710f4653a31154c4305522dc1d24e948485141d1f290446d2c2117410844e801d11800443ec4110da1043f30088e79e2a3291cecb962222acb0708f3e381e330b463972a16f0c4044172f0c0a8a027d4110570090003c2b,0x9f6dc4a5a4047946984649c0108a3d50a201611795d1d9dbcf137447455c5b717]⟩,⟨10,#[0xfffff183ffffd8dffd59ffda357d616083fffc4e0d98b613ff677ffffffffffff0e44a163ff0cbff,0xffc4161d72ffd8a56bff1298c13fffffd8516d8effc31ffc30ffc2fffd6062459ffffffffff60fff,0xffd8f1383e100361305fffd4913fff0e06117bffffd86687ffffd715cc620f59efffff0dfff16bff,0x4e83bfffff649a4ffd90ffc33fffff4e59f1799116993ffc57fffff0b7ff173ffffd5bfffff163ff,0xffda2ffd27fffff0bbff177ffffc3afffff17d9cffd5c6605115fff0d3ffffd9b14d38ffd94143ff,0xf062ffc35ffc6069452fffffffc5bffd97fffff149a0ffd95ffffffffff16596fffff49928667ff,0xffc4254d95ffc84ffc06ffdacffd1d080000612b58fff38fff6effffffff5145412fff4705d17061,0xfffff01d766d4215689affffffffff6c085ffffffffff5d7ff09d3b3e5a6267fffffffffffffffff,0xffc196a7ff567ffffd2cffc01fffff0a0d43e8e46b7ff4780dffffffffff4f7fffffff593ff577ff,0xffd62fffffffd4afffffffd4347fffffdbcfffffffcfb3955f4e3ffffc86fffff00bff0a7ff69fff,0x5957803bff11190ffd20ffd3e10d54fffffffd3b5dd9661569fffff6bbffffc08ffc132c7ff7512d,0xffc23ffc2b6a97939bff220092cbff56fff554220a9bd21fff6989b3f1b1357ff00fffffd334a41a,0xffdbe49921fffff117ff093ff5efff737ff4b95c577ffffc9c053ffffc0f757ff4fd4b598d66dfff,0xfffffffdb2ffffffffff043ffffdcefffff5c4fdffd7406d29ffffffffff2740464582fffff4c7ff,0x6fcb4227ffffd57fffff505620701611bffffcd8fffffffda750015fffff35d4cffd67558b3fffff,0x11d83ffda802cd9ffffffffff61bff537ff75bff6a3ff39d6a5ebfffffff02bfffffffffc2c0452f,0x120fe280b63ad42ffd74fffff097ff05c9e2d57c56130ffc1dffdc0ffd683a01253bff73ffffffff,0x2ed0d2a48effc6a2e8ea229084106f3c4b7ffcdd1e84840c6a2e07a27cf0370493b4db408da404ec,0x12869ffd70603ffffcf6747ffffffffffffffffffffff70d886ad8465c8f2f0ee3bca11e90e3a4a1,0xffd6bfffffffd7bffffffffff6a7ff6e0f5ffffffffff64870fffffffdd825fffffd6924bff1b3ff,0xfffff2f8bd2e51141c4d2a8e92a08f448bf22bfffffff61da5fffff443ff5b3ff5f5aafffffffcbe,0x6b3fffffff1afff54bffffcae19bfffffffffdc4ffc7effd4f1edb9ffffffffff6bfffffd7fffd19,0x62ffffffff42fff5f92a748056bbff417ffffdb4ffc4f5f3ffffffffffff5cbfffffff6b7fffffff,0xffc7d6c5bafffffffffffffffffffffffff6304effd3c5b89145bff2fbfffffffffc95ffd1864fff,0xffffffffff5afff6cd6dfffff43fffffcad6c160fffffffffffffff18fffffd6afffff541b4ffdd9,0x7205a237ff348f4ffd46424f241bff3008a154de158cc385003fccb3805571551ffc0cffd986cbff,0xfffff6386dffd996dfff66bffffcf3fffffffffffffffffd15ffcf5ffc7f431441c50b5f8c8ffd7d,0xffcf44c5ba63dc94d1326e544ffd3715d43307ff6e3ffffd8dffffffffff6d913ffc90ffc64fffff,0xfffff729174d480ffd6dfffffffd6c29532ffc5931cd045bff3dbff653ffffca4ffdb5ffd48fffff,0xffc7429cd34dbffffcc946547460f316072ffce2fffff319cbffffffffff5b91a3d4a620fff3cc75,0x717fffffffffdccffc65fffff30bff721be49149ffdc3fffff6791416dccffcf646cf4ffd7fffc98,0x57bfffffff48bfffffffffc77fffff72fff6f3ff703ff6814ffffffffdc7ffffffffffffc78fffff,0xffdbdfffffffdc276bffffffffffff67d05ffd50ffffffffffffffffffffffc1efffff74fff6fdbb,0x42bffffffffffffffd9d707ff729c9ffdc6fffff313ffffd0fffffffffffffc61473fffffff713ff,0x48da21b8ce171cfffffffffff737fffffffffd0c497ffffc6246d73440ca1f105204c52bd80fffff,0x5bd134e7ffffd22fffff7450cffffffffff51d45ffc67fffff46bffffffffffff76dd2ffffffffff,0xffd0b4288b523ff1cc79454d14ebff545d02adceffc8cffdd3fffffffd0afffff5181f687fffffff,0x497ff763fffffff4dbffffd81fffff4690f5c3ffffd175848244060ffcb048c9637cc3ffcf717918,0xffd13493ff46dd624fffffda4ffffffffff49fff767ff4cffffffffffd141a3ff75134fffffffda3,0xffcf84655228bff75fffffca3ffccdffffffffff45ffffffff174ac4d7fffffff76dd509bffffdda,0x3ff4552817d144dfff33c9445bffffc76]⟩⟩
def layer11 : Jump := ⟨⟨11,#[0x400]⟩,⟨15,#[0x5c7a]⟩,⟨10,#[0xffc0afffffffffffffffffc25ffc200a7ff0a3ffffffffffffffc1ffffffffc2409ffffffffffc10,0x4c1803fff09bfffffffffc0effffffffff08bff057ff033ffffffffffffffc0706c02fffffffc03,0x37ff01bff05fff0101efffffffc05fffffffc16ffffffffffffc09fffffffffffffff00001ffc19,0x77fffffff04814ffc0bffc08fffffffc23ffffffffff087ffffc11ffc1c06bff]⟩⟩
def tier : Nat → Jump
  | 3 => layer3
  | 4 => layer4
  | 5 => layer5
  | 6 => layer6
  | 7 => layer7
  | 8 => layer8
  | 9 => layer9
  | 10 => layer10
  | 11 => layer11
  | _ => ⟨Direct.blank,Direct.blank,Direct.blank⟩
def lookup (t : Jump) (i h : Nat) :=
  let g := t.control.val i
  if g<1024 then g else
    let d := t.desc.val (g-1024)
    let mode := (d>>>8) % 128
    let span := d % 256
    let j := h ^^^ ((2*(mode % 8)+1)*(h>>>(mode/8+1)))
    t.values.val ((d>>>15)+j % span)
end CoNum4358.WordRows.FastJump

namespace CoAO3143.Cotree
open ProtocolProof
inductive ReadTree where
  | atom : Sig → ReadTree
  | fork : Bool → ReadTree → ReadTree → ReadTree

def ReadTree.value : ReadTree → Sig
  | .atom a => a
  | .fork d e f => bin d e.value f.value

def ReadTree.sources : ReadTree → Finset Sig
  | .atom a => {a}
  | .fork _ e f => e.sources ∪ f.sources

def ReadTree.linear : ReadTree → Prop
  | .atom _ => True
  | .fork _ e f => e.linear ∧ f.linear ∧ Disjoint e.sources f.sources

def ReadTree.plug : ReadTree → Sig → ReadTree → ReadTree
  | .atom a, z, r => if a = z then r else .atom a
  | .fork d e f, z, r => .fork d (e.plug z r) (f.plug z r)

private lemma plug_value (e : ReadTree) {z : Sig} {r : ReadTree} (hr : r.value=z) :
    (e.plug z r).value=e.value := by
  induction e with
  | atom a => by_cases h : a=z <;> simp [ReadTree.plug,ReadTree.value,h,hr]
  | fork d e f ih jh => simp [ReadTree.plug,ReadTree.value,ih,jh]

private lemma plug_mem (e : ReadTree) (z w : Sig) (r : ReadTree) :
    w ∈ (e.plug z r).sources ↔ (w ∈ e.sources ∧ w ≠ z) ∨ (z ∈ e.sources ∧ w ∈ r.sources) := by
  induction e with
  | atom a =>
    by_cases h : a=z
    · subst a; simp [ReadTree.plug,ReadTree.sources]
    · have hz : z ≠ a := Ne.symm h
      by_cases hw : w=a <;> simp_all [ReadTree.plug,ReadTree.sources]
  | fork d e f ih jh =>
    simp only [ReadTree.plug,ReadTree.sources,Finset.mem_union,ih,jh]; tauto

private lemma plug_linear (e : ReadTree) {z : Sig} {r : ReadTree} (he : e.linear) (hr : r.linear)
    (fresh : ∀ w ∈ r.sources, w ∈ e.sources → w = z) : (e.plug z r).linear := by
  induction e with
  | atom a => by_cases ha : a=z <;> simp [ReadTree.plug,ReadTree.linear,ha,hr]
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

theorem tight_tree {k t S} (h : Live k t S) (hz : t=0) (tight : S.card+t=k+1) :
    ∃ e : ReadTree, e.value = target ∧ e.linear ∧ e.sources = S := by
  induction h with
  | stop => exact ⟨.atom target,rfl,trivial,rfl⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    let z := bin d a b
    have hn : z ∉ U := fun hh => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hh))
    have size := CoAO3143.ProtocolProof.width tail
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
    obtain ⟨e,he,hl,hS⟩ := ih hz (by change (insert z U).card+t=k+1; rw [Finset.card_insert_of_notMem hn]; omega)
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

def leftChoice (d : Bool) (v : Sig) (p n : Row) : Bool :=
  if d then bit true p v else !(bit false n v)

def answer (p n : Row) : ReadTree → Sig
  | .atom a => a
  | .fork d l r => if leftChoice d l.value p n then answer p n l else answer p n r

theorem answer_mem (p n : Row) (t : ReadTree) : answer p n t ∈ t.sources := by
  induction t with
  | atom a => simp [answer,ReadTree.sources]
  | fork d l r ih jh =>
    simp only [answer,ReadTree.sources,Finset.mem_union]
    split <;> simp_all

def Together (t : ReadTree) (positive : Bool) (a b : Sig) : Prop :=
  ∃ fixed i j : Row, (if positive then answer fixed i t else answer i fixed t) = a ∧
    (if positive then answer fixed j t else answer j fixed t) = b

def Connected (t : ReadTree) (positive : Bool) (s : Finset Sig) : Prop :=
  ∀ f : Sig → Bool,
    (∀ a∈s, ∀ b∈s, Together t positive a b → f a = f b) → ∀ a∈s, ∀ b∈s, f a=f b

private theorem parent_side {l r : ReadTree} (dis : Disjoint l.sources r.sources)
    (d : Bool) (p n : Row) :
    decide (answer p n (.fork d l r) ∈ l.sources) = leftChoice d l.value p n := by
  cases en : leftChoice d l.value p n
  · have other := Finset.disjoint_left.mp dis
    have miss : answer p n r ∉ l.sources := fun hl => other hl (answer_mem p n r)
    simp [answer,en,miss]
  · simp [answer,en,answer_mem]

private theorem into_left {l r : ReadTree} (dis : Disjoint l.sources r.sources)
    {d : Bool} {p n : Row} {a : Sig} (member : a∈l.sources)
    (eq : answer p n (.fork d l r) =a) : answer p n l=a := by
  cases side : leftChoice d l.value p n
  · simp [answer,side] at eq
    exact (Finset.disjoint_left.mp dis member (eq ▸ answer_mem p n r)).elim
  · simpa [answer,side] using eq

private theorem into_right {l r : ReadTree} (dis : Disjoint l.sources r.sources)
    {d : Bool} {p n : Row} {a : Sig} (member : a∈r.sources)
    (eq : answer p n (.fork d l r) =a) : answer p n r=a := by
  cases side : leftChoice d l.value p n
  · simpa [answer,side] using eq
  · simp [answer,side] at eq
    exact (Finset.disjoint_left.mp dis (eq ▸ answer_mem p n l) member).elim

private theorem descend_left {l r : ReadTree} {d u : Bool} {a b : Sig}
    (dis : Disjoint l.sources r.sources) (ha : a∈l.sources) (hb : b∈l.sources)
    (h : Together (.fork d l r) u a b) : Together l u a b := by
  obtain ⟨z,i,j,hi,hj⟩ := h
  refine ⟨z,i,j,?_⟩
  cases u <;> exact ⟨into_left dis ha hi,into_left dis hb hj⟩

private theorem descend_right {l r : ReadTree} {d u : Bool} {a b : Sig}
    (dis : Disjoint l.sources r.sources) (ha : a∈r.sources) (hb : b∈r.sources)
    (h : Together (.fork d l r) u a b) : Together r u a b := by
  obtain ⟨z,i,j,hi,hj⟩ := h
  refine ⟨z,i,j,?_⟩
  cases u <;> exact ⟨into_right dis ha hi,into_right dis hb hj⟩

theorem incompatible (t : ReadTree) (linear : t.linear) (s : Finset Sig) (inside : s ⊆ t.sources)
    (linked : ∀ d, Connected t d s) {a b : Sig} (ha : a∈s) (hb : b∈s) : a=b := by
  induction t with
  | atom x =>
    have l := Finset.mem_singleton.mp (inside ha)
    have r := Finset.mem_singleton.mp (inside hb)
    exact l.trans r.symm
  | fork d l r ih jh =>
    obtain ⟨ll,lr,dis⟩ := linear
    let side := fun w : Sig => decide (w∈l.sources)
    have invariant (x y : Sig) (h : Together (.fork d l r) d x y) : side x=side y := by
      obtain ⟨z,i,j,hi,hj⟩ := h
      cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi hj <;>
        rw [←hi,←hj] <;> unfold side <;> rw [parent_side dis,parent_side dis] <;> rfl
    have fixed := linked d side (fun x _ y _ h => invariant x y h)
    by_cases al : a∈l.sources
    · have sub (w) (hw : w∈s) : w∈l.sources := by
        have e := fixed w hw a ha
        simpa [side,al] using e
      apply ih ll sub
      intro c f h
      apply linked c f
      intro x hx y hy hxy
      exact h x hx y hy (descend_left dis (sub x hx) (sub y hy) hxy)
    · have sub (w) (hw : w∈s) : w∈r.sources := by
        have e := fixed w hw a ha
        have miss : w∉l.sources := by simpa [side,al] using e
        exact (Finset.mem_union.mp (inside hw)).resolve_left miss
      apply jh lr sub
      intro c f h
      apply linked c f
      intro x hx y hy hxy
      exact h x hx y hy (descend_right dis (sub x hx) (sub y hy) hxy)

end CoAO3143.Cotree

namespace CoAO3143.OneShare
open Cotree

set_option maxRecDepth 16384 in
inductive F where
  | atom : Sig → F
  | port : F
  | fork : Bool → F → F → F

set_option maxRecDepth 16384 in
def F.val (z : Sig) : F → Sig
  | .atom a => a
  | .port => z
  | .fork d l r => bin d (l.val z) (r.val z)

set_option maxRecDepth 16384 in
def F.vars : F → List Sig
  | .atom a => [a]
  | .port => []
  | .fork _ l r => l.vars ++ r.vars

set_option maxRecDepth 16384 in
def F.ports : F → Nat
  | .atom _ => 0
  | .port => 1
  | .fork _ l r => l.ports+r.ports

set_option maxRecDepth 16384 in
def F.bind (f : Sig → F) : F → F
  | .atom a => f a
  | .port => .port
  | .fork d l r => .fork d (l.bind f) (r.bind f)

set_option maxRecDepth 16384 in
theorem bind_val (e : F) (f : Sig→F) (s : Sig) (ok : ∀a,(f a).val s=a) :
    (e.bind f).val s=e.val s := by
  induction e with
  | atom a => exact ok a
  | port => rfl
  | fork d l r ih jh => simp only [F.bind,F.val,ih,jh]

set_option maxRecDepth 16384 in
theorem bind_ports (e : F) (f : Sig→F) (closed : ∀x,(f x).ports=0) :
    (e.bind f).ports=e.ports := by
  induction e with
  | atom a => exact closed a
  | port => rfl
  | fork d l r ih jh => simp only [F.bind,F.ports,ih,jh]

set_option maxRecDepth 16384 in
theorem bind_vars (e : F) (f : Sig→F) : (e.bind f).vars=e.vars.flatMap (fun a => (f a).vars) := by
  induction e with
  | atom a => simp [F.bind,F.vars]
  | port => rfl
  | fork d l r ih jh => simp only [F.bind,F.vars,ih,jh,List.flatMap_append]

set_option maxRecDepth 16384 in
def weight (f : Sig→F) : List Sig → Nat
  | [] => 0
  | x::xs => (f x).ports + weight f xs

set_option maxRecDepth 16384 in
private theorem weight_append (f : Sig→F) (xs ys : List Sig) :
    weight f (xs++ys)=weight f xs+weight f ys := by
  induction xs with
  | nil => simp [weight]
  | cons a xs ih => simp [weight,ih,Nat.add_assoc]

set_option maxRecDepth 16384 in
theorem bind_weight (e : F) (f : Sig→F) : (e.bind f).ports=e.ports+weight f e.vars := by
  induction e with
  | atom a => simp [F.bind,F.ports,F.vars,weight]
  | port => rfl
  | fork d l r ih jh =>
    simp only [F.bind,F.ports,F.vars,ih,jh,weight_append]
    omega

set_option maxRecDepth 16384 in
private def tally (a : Sig) : List Sig → Nat
  | [] => 0
  | x::xs => (if x=a then 1 else 0)+tally a xs

set_option maxRecDepth 16384 in
private theorem tally_once (a : Sig) (xs : List Sig) (nd : xs.Nodup) :
    tally a xs=if a∈xs then 1 else 0 := by
  induction xs with
  | nil => simp [tally]
  | cons x xs ih =>
    obtain ⟨fresh,n⟩ := List.nodup_cons.mp nd
    by_cases eq : x=a
    · subst x; simp [tally,ih n,fresh]
    · simp [tally,ih n,eq,Ne.symm eq]

set_option maxRecDepth 16384 in
private theorem weight_pair (f : Sig→F) (a z : Sig)
    (od : ∀x,(f x).ports=(if x=a then 1 else 0)+(if x=z then 1 else 0)) (xs : List Sig) :
    weight f xs=tally a xs+tally z xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [weight,tally,od,ih]
    omega

set_option maxRecDepth 16384 in
def embed : ReadTree → F
  | .atom a => .atom a
  | .fork d l r => .fork d (embed l) (embed r)

set_option maxRecDepth 16384 in
theorem embed_ports (e : ReadTree) : (embed e).ports=0 := by
  induction e with
  | atom => rfl
  | fork _ _ _ ih jh => simp [embed,F.ports,ih,jh]

set_option maxRecDepth 16384 in
theorem embed_val (e : ReadTree) (s : Sig) : (embed e).val s=e.value := by
  induction e with
  | atom => rfl
  | fork _ _ _ ih jh => simp only [embed,F.val,ReadTree.value,ih,jh]

set_option maxRecDepth 16384 in
theorem embed_set (e : ReadTree) : (embed e).vars.toFinset=e.sources := by
  induction e with
  | atom a => simp [embed,F.vars,ReadTree.sources]
  | fork d l r ih jh => simp [embed,F.vars,ReadTree.sources,ih,jh]

set_option maxRecDepth 16384 in
theorem embed_nodup (e : ReadTree) (h : e.linear) : (embed e).vars.Nodup := by
  induction e with
  | atom a => simp [embed,F.vars]
  | fork d l r ih jh =>
    obtain ⟨hl,hr,dis⟩ := h
    apply (ih hl).append (jh hr)
    rw [List.disjoint_left]
    intro a h₁ h₂
    exact Finset.disjoint_left.mp dis
      (embed_set l ▸ List.mem_toFinset.mpr h₁) (embed_set r ▸ List.mem_toFinset.mpr h₂)

set_option maxRecDepth 16384 in
private theorem flat_nd {xs : List Sig} (nd : xs.Nodup) (f : Sig→List Sig) (back : Sig→Sig)
    (one : ∀ x∈xs,(f x).Nodup) (recover : ∀x∈xs,∀y∈f x,back y=x) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
    rw [List.flatMap_cons]
    apply (one a List.mem_cons_self).append
      (ih rest (fun x hx => one x (List.mem_cons_of_mem _ hx))
        (fun x hx => recover x (List.mem_cons_of_mem _ hx)))
    rw [List.disjoint_left]
    intro y ya ys
    obtain ⟨x,hx,yx⟩ := List.mem_flatMap.mp ys
    have E : a=x := (recover a List.mem_cons_self y ya).symm.trans
      (recover x (List.mem_cons_of_mem _ hx) y yx)
    exact fresh (by simpa only [E] using hx)

set_option maxRecDepth 16384 in
structure Factor (S : Finset Sig) where
  inner : F
  outer : F
  value : outer.val (inner.val zero)=target
  closed : inner.ports=0
  twice : outer.ports=2
  distinct : (inner.vars ++ outer.vars).Nodup
  sources : (inner.vars ++ outer.vars).toFinset=S

set_option maxRecDepth 16384 in
private def join (d : Bool) (a b : Sig) : F := .fork d (.atom a) (.atom b)

set_option maxRecDepth 16384 in
private theorem clean {U : Finset Sig} {a b : Sig} {d : Bool} (ab : a≠b) (au : a∉U) (bu : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (old : Factor (insert (bin d a b) U)) :
    Nonempty (Factor (insert a (insert b U))) := by
  let z := bin d a b
  let f := fun t : Sig => if t=z then join d a b else F.atom t
  let xs := old.inner.vars ++ old.outer.vars
  have mem (x : Sig) : x∈xs ↔ x=z ∨ x∈U := by
    change x∈old.inner.vars++old.outer.vars ↔ _
    rw [←List.mem_toFinset,old.sources,Finset.mem_insert]
  have ev (s x : Sig) : (f x).val s=x := by by_cases e : x=z <;> simp [f,e,join,F.val,z]
  have item (x w : Sig) : w∈(f x).vars ↔ (x=z ∧ (w=a ∨ w=b)) ∨ (x≠z ∧ w=x) := by
    by_cases e : x=z <;> simp [f,e,join,F.vars]
  let back := fun y : Sig => if y=a ∨ y=b then z else y
  have nd : (xs.flatMap (fun x => (f x).vars)).Nodup := by
    apply flat_nd old.distinct _ back
    · intro x hx; by_cases e : x=z <;> simp [f,e,join,F.vars,ab]
    · intro x hx y hy
      rcases (item x y).mp hy with ⟨xz,ya|yb⟩ | ⟨xz,yx⟩
      · simp [back,ya,xz]
      · simp [back,yb,xz]
      · rw [yx]
        have hu := (mem x).mp hx |>.resolve_left xz
        have na : x≠a := fun e => au (e ▸ hu)
        have nb : x≠b := fun e => bu (e ▸ hu)
        simp [back,na,nb]
  have vars : (old.inner.bind f).vars ++ (old.outer.bind f).vars=xs.flatMap (fun x => (f x).vars) := by
    rw [bind_vars,bind_vars,←List.flatMap_append]
  have cf (x : Sig) : (f x).ports=0 := by by_cases hx : x=z <;> simp [f,hx,join,F.ports]
  refine ⟨⟨old.inner.bind f,old.outer.bind f,?_,?_,?_,by rw [vars]; exact nd,?_⟩⟩
  · rw [bind_val _ _ _ (ev _),bind_val _ _ _ (ev _)]
    exact old.value
  · rw [bind_ports _ _ cf]; exact old.closed
  · rw [bind_ports _ _ cf]; exact old.twice
  · rw [vars]
    ext w
    simp only [List.mem_toFinset,List.mem_flatMap,Finset.mem_insert]
    constructor
    · rintro ⟨x,hx,hy⟩
      obtain ⟨_,e⟩ | ⟨xz,wx⟩ := (item x w).mp hy
      · tauto
      · rw [wx]
        exact Or.inr (Or.inr ((mem x).mp hx |>.resolve_left xz))
    · rintro (rfl|rfl|u)
      · exact ⟨z,(mem z).mpr (.inl rfl),(item _ _).mpr (.inl ⟨rfl,.inl rfl⟩)⟩
      · exact ⟨z,(mem z).mpr (.inl rfl),(item _ _).mpr (.inl ⟨rfl,.inr rfl⟩)⟩
      · have wz : w≠z := fun e => by
          have zu : z∈U := by simpa only [e] using u
          exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem zu))
        exact ⟨w,(mem w).mpr (.inr u),(item _ _).mpr (.inr ⟨wz,rfl⟩)⟩

set_option maxRecDepth 16384 in
private theorem shared {k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (au : a∈U) (bu : b∉U) (fresh : bin d a b∉insert a (insert b U))
    (tail : Live k 0 (insert (bin d a b) U)) (tight : (insert (bin d a b) U).card=k+1) :
    Nonempty (Factor (insert a (insert b U))) := by
  obtain ⟨e,ev,el,es⟩ := tight_tree tail rfl (by omega)
  let z := bin d a b
  let xs := (embed e).vars
  let f := fun x : Sig => if x=z then F.fork d .port (.atom b) else if x=a then .port else .atom x
  have mem (w : Sig) : w∈xs ↔ w=z ∨ w∈U := by
    change w∈(embed e).vars ↔ _
    rw [←List.mem_toFinset,embed_set,es,Finset.mem_insert]
  have zb : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have za : z≠a := fun E => zb (by simpa only [E] using au)
  have ab : a≠b := fun E => bu (E ▸ au)
  have item (x w : Sig) : w∈(f x).vars ↔ (x=z ∧ w=b) ∨ (x≠z ∧ x≠a ∧ w=x) := by
    by_cases ez : x=z
    · simp [f,ez,F.vars]
    · by_cases ea : x=a
      · simp [f,ea,Ne.symm za,F.vars]
      · simp [f,ez,ea,F.vars]
  have eval (x : Sig) : (f x).val a=x := by
    by_cases ez : x=z
    · simp only [f,if_pos ez,F.val]; exact ez.symm
    · by_cases ea : x=a
      · simp only [f,if_neg ez,if_pos ea,F.val]; exact ea.symm
      · simp only [f,if_neg ez,if_neg ea,F.val]
  let back := fun y : Sig => if y=b then z else y
  have nd : (xs.flatMap (fun x => (f x).vars)).Nodup := by
    apply flat_nd (embed_nodup e el) _ back
    · intro x hx
      by_cases ez : x=z
      · simp [f,ez,F.vars]
      · by_cases ea : x=a
        · simp [f,ea,Ne.symm za,F.vars]
        · simp [f,ez,ea,F.vars]
    · intro x hx y hy
      rcases (item x y).mp hy with ⟨xz,yb⟩ | ⟨xz,_,yx⟩
      · simp [back,yb,xz]
      · rw [yx]
        have hu := (mem x).mp hx |>.resolve_left xz
        have xb : x≠b := fun E => bu (E ▸ hu)
        simp [back,xb]
  have all (w : Sig) : w∈xs.flatMap (fun x => (f x).vars) ↔ w=b ∨ (w∈U ∧ w≠a) := by
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨x,hx,hy⟩
      rcases (item _ _).mp hy with ⟨_,wb⟩ | ⟨xz,xa,wx⟩
      · exact .inl wb
      · rw [wx]
        exact .inr ⟨(mem x).mp hx |>.resolve_left xz,xa⟩
    · rintro (rfl|⟨wu,wa⟩)
      · exact ⟨z,(mem z).mpr (.inl rfl),(item _ _).mpr (.inl ⟨rfl,rfl⟩)⟩
      · have wz : w≠z := fun E => zb (E ▸ wu)
        exact ⟨w,(mem w).mpr (.inr wu),(item _ _).mpr (.inr ⟨wz,wa,rfl⟩)⟩
  let inner := F.atom a
  let outer := (embed e).bind f
  have vs : inner.vars ++ outer.vars=a::xs.flatMap (fun x => (f x).vars) := by simp [inner,outer,F.vars,bind_vars,xs]
  have two : outer.ports=2 := by
    have od (x : Sig) : (f x).ports=(if x=a then 1 else 0)+(if x=z then 1 else 0) := by
      by_cases hx : x=z <;> by_cases ha : x=a <;> simp_all [f,F.ports]
    have az : a∈xs := (mem a).mpr (.inr au)
    have zz : z∈xs := (mem z).mpr (.inl rfl)
    change ((embed e).bind f).ports=2
    rw [bind_weight,embed_ports,weight_pair f a z od]
    change 0+(tally a xs+tally z xs)=2
    rw [tally_once _ _ (embed_nodup e el),tally_once _ _ (embed_nodup e el)]
    change 0+((if a∈xs then 1 else 0)+(if z∈xs then 1 else 0))=2
    simp [az,zz]
  refine ⟨⟨inner,outer,?_,rfl,two,?_,?_⟩⟩
  · change ((embed e).bind f).val a=target
    rw [bind_val _ _ _ eval,embed_val,ev]
  · rw [vs,List.nodup_cons]
    exact ⟨fun h => by simpa [ab] using (all a).mp h,nd⟩
  · rw [vs]
    ext w
    simp only [List.mem_toFinset,List.mem_cons,Finset.mem_insert,all]
    by_cases wa : w=a <;> simp_all

set_option maxRecDepth 16384 in
private theorem bin_swap (d : Bool) (a b : Sig) : bin d a b=bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

set_option maxRecDepth 16384 in
theorem factor_aux {k t S} (h : Live k t S) (hz : t=0) (slack : S.card+t=k) :
    Nonempty (Factor S) := by
  induction h with
  | stop => simp at slack
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb ab hf tail ih =>
    subst t
    have zu : bin d a b∉U := fun m => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have after := ProtocolProof.width tail
    rw [Finset.card_insert_of_notMem zu] at after
    by_cases au : a∈U
    · have ai : a∈insert b U := Finset.mem_insert_of_mem au
      rw [Finset.insert_eq_of_mem ai] at slack
      by_cases bu : b∈U
      · rw [Finset.insert_eq_of_mem bu] at slack; omega
      · rw [Finset.card_insert_of_notMem bu] at slack
        exact shared au bu hf tail (by rw [Finset.card_insert_of_notMem zu]; omega)
    · have ai : a∉insert b U := by simpa [ab] using au
      rw [Finset.card_insert_of_notMem ai] at slack
      by_cases bu : b∈U
      · rw [Finset.insert_eq_of_mem bu] at slack
        have hh := shared (d:=d) bu au
          (by simpa only [bin_swap d b a,Finset.insert_comm b a] using hf)
          (by simpa only [bin_swap d b a] using tail)
          (by rw [bin_swap d b a,Finset.card_insert_of_notMem zu]; omega)
        simpa only [Finset.insert_comm b a] using hh
      · rw [Finset.card_insert_of_notMem bu] at slack
        obtain ⟨old⟩ := ih rfl (by rw [Finset.card_insert_of_notMem zu]; omega)
        exact clean ab au bu hf old

set_option maxRecDepth 16384 in
theorem factor {k S} (h : Live k 0 S) (size : S.card=k) : Nonempty (Factor S) :=
  factor_aux h rfl (by omega)

end CoAO3143.OneShare

namespace CoAO3143.OneShare
open ProtocolProof
open Cotree (leftChoice)

def F.pick (z : Sig) (p n : Row) : F → Option Sig
  | .atom a => some a
  | .port => none
  | .fork d l r => if leftChoice d (l.val z) p n then l.pick z p n else r.pick z p n

theorem pick_mem (e : F) (z : Sig) (p n : Row) {a : Sig} (eq : e.pick z p n=some a) :
    a∈e.vars := by
  induction e with
  | atom u => simpa [F.pick,F.vars,eq_comm] using eq
  | port => contradiction
  | fork d l r ih jh =>
    simp only [F.pick] at eq
    change a∈l.vars++r.vars
    split at eq
    · exact List.mem_append_left _ (ih eq)
    · exact List.mem_append_right _ (jh eq)

def selected (z : Sig) : Option Sig → Sig
  | none => z
  | some a => a

private theorem bop (s d : Bool) (r : Row) (a b : Sig) :
    bit s r (bin d a b) = if d then bit s r a || bit s r b else bit s r a && bit s r b := by
  cases s <;> cases d <;> simp [bit,bin,BitVec.getLsbD_or,BitVec.getLsbD_and]

theorem pick_valid (e : F) (z : Sig) (p n : Row) (yes : separates p n (e.val z)) :
    separates p n (selected z (e.pick z p n)) := by
  induction e with
  | atom _ => exact yes
  | port => exact yes
  | fork d l r ih jh =>
    obtain ⟨hp,hn⟩ := yes
    change bit true p (bin d (l.val z) (r.val z))=true at hp
    change bit false n (bin d (l.val z) (r.val z))=false at hn
    rw [bop] at hp hn
    cases d <;> cases pl : bit true p (l.val z) <;> cases nl : bit false n (l.val z) <;>
      simp only [F.pick,leftChoice,Bool.false_eq_true,↓reduceIte,pl,nl,Bool.not_false,Bool.not_true] <;>
      first | exact ih (by simp_all [separates]) | exact jh (by simp_all [separates])

theorem target_always (p n : Row) : separates p n target := by
  constructor
  · change (BitVec.allOnes 160).getLsbD p.val=true
    rw [BitVec.getLsbD_allOnes]
    simp only [p.isLt,decide_true]
  · simp [bit,target]

def Miss (X : Finset Sig) (p n : Row) := ∀a∈X,¬separates p n a
def Factor.inside {S} (f : Factor S) := f.inner.vars.toFinset
def Factor.outside {S} (f : Factor S) := f.outer.vars.toFinset

theorem closed_input (e : F) (no : e.ports=0) : e.vars.toFinset.Nonempty := by
  induction e with
  | atom a => exact ⟨a,by simp [F.vars]⟩
  | port => simp [F.ports] at no
  | fork d l r ih jh =>
    change l.ports+r.ports=0 at no
    obtain ⟨a,ha⟩ := ih (by omega)
    exact ⟨a,List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp ha))⟩

theorem partition {S} (f : Factor S) : f.inside ∪ f.outside=S ∧ Disjoint f.inside f.outside := by
  constructor
  · simpa [Factor.inside,Factor.outside] using f.sources
  · rw [Finset.disjoint_left]
    have dis := List.disjoint_left.mp (List.disjoint_of_nodup_append f.distinct)
    intro a ha hb
    exact dis (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)

theorem inside_requires {S} (f : Factor S) (p n : Row) (no : Miss f.outside p n) :
    separates p n (f.inner.val zero) := by
  let z := f.inner.val zero
  have yes : separates p n (f.outer.val z) := by rw [show f.outer.val z=target from f.value]; exact target_always p n
  have step := pick_valid f.outer z p n yes
  cases eq : f.outer.pick z p n with
  | none => simpa [eq,selected] using step
  | some a =>
    have mem : a∈f.outside := List.mem_toFinset.mpr (pick_mem _ _ _ _ eq)
    exact False.elim (no a mem (by simpa [eq,selected] using step))

theorem inside_cross {S} (f : Factor S) {p p' n n' : Row}
    (hp : Miss f.outside p n') (hn : Miss f.outside p' n) :
    separates p n (f.inner.val zero) :=
  ⟨(inside_requires f p n' hp).1,(inside_requires f p' n hn).2⟩

theorem inside_answer {S} (f : Factor S) {p n : Row} (yes : separates p n (f.inner.val zero)) :
    ∃ a∈f.inside, f.inner.pick zero p n=some a ∧ separates p n a := by
  have data := pick_valid f.inner zero p n yes
  cases eq : f.inner.pick zero p n with
  | none =>
    have no : separates p n zero := by simpa [eq,selected] using data
    exact False.elim (by simpa [separates,bit,zero] using no)
  | some a => exact ⟨a,List.mem_toFinset.mpr (pick_mem _ _ _ _ eq),rfl,by simpa [eq,selected] using data⟩

theorem outside_answer {S} (f : Factor S) {p n : Row} (no : Miss f.inside p n) :
    ∃ a∈f.outside, f.outer.pick (f.inner.val zero) p n=some a ∧ separates p n a := by
  let z := f.inner.val zero
  have yes : separates p n (f.outer.val z) := by rw [show f.outer.val z=target from f.value]; exact target_always p n
  have data := pick_valid f.outer z p n yes
  cases eq : f.outer.pick z p n with
  | none =>
    have zin : separates p n (f.inner.val zero) := by simpa [eq,selected,z] using data
    obtain ⟨a,ha,_,valid⟩ := inside_answer f zin
    exact False.elim (no a ha valid)
  | some a => exact ⟨a,List.mem_toFinset.mpr (pick_mem _ _ _ _ eq),rfl,by simpa [eq,selected] using data⟩

end CoAO3143.OneShare

namespace CoAO3143.OneShare
open ProtocolProof
open Cotree (leftChoice)

def Together (e : F) (z : Sig) (side : Bool) (a b : Sig) : Prop :=
  ∃ fixed i j : Row,
    (if side then e.pick z fixed i else e.pick z i fixed)=some a ∧
    (if side then e.pick z fixed j else e.pick z j fixed)=some b

def Connected (rel : Sig → Sig → Prop) (X : Finset Sig) :=
  ∀ f : Sig→Bool, (∀a∈X,∀b∈X,rel a b→f a=f b) → ∀a∈X,∀b∈X,f a=f b

private theorem at_side {l r : F} (dis : l.vars.Disjoint r.vars) (s : Sig) (d : Bool) {a p n}
    (hit : (F.fork d l r).pick s p n=some a) :
    decide (a∈l.vars)=leftChoice d (l.val s) p n := by
  cases side : leftChoice d (l.val s) p n
  · have h : r.pick s p n=some a := by simpa only [F.pick,side,Bool.false_eq_true,↓reduceIte] using hit
    have na : a∉l.vars := fun mem => List.disjoint_left.mp dis mem (pick_mem _ _ _ _ h)
    simp [na]
  · have h : l.pick s p n=some a := by simpa only [F.pick,side,↓reduceIte] using hit
    simp [pick_mem _ _ _ _ h]

private theorem left_hit {l r : F} {d : Bool} {s a p n} (dis : l.vars.Disjoint r.vars) (mem : a∈l.vars)
    (hit : (F.fork d l r).pick s p n=some a) : l.pick s p n=some a := by
  have active := at_side dis s d hit
  have dir : leftChoice d (l.val s) p n=true := by simpa [mem] using active.symm
  simpa only [F.pick,dir,↓reduceIte] using hit

private theorem right_hit {l r : F} {d : Bool} {s a p n} (dis : l.vars.Disjoint r.vars) (mem : a∈r.vars)
    (hit : (F.fork d l r).pick s p n=some a) : r.pick s p n=some a := by
  have no : a∉l.vars := fun h => List.disjoint_left.mp dis h mem
  have active := at_side dis s d hit
  have dir : leftChoice d (l.val s) p n=false := by simpa [no] using active.symm
  simpa only [F.pick,dir,Bool.false_eq_true,↓reduceIte] using hit

private theorem descendL {l r : F} {d u : Bool} {s a b} (dis : l.vars.Disjoint r.vars)
    (ha : a∈l.vars) (hb : b∈l.vars) (e : Together (.fork d l r) s u a b) : Together l s u a b := by
  obtain ⟨f,i,j,hi,hj⟩ := e
  refine ⟨f,i,j,?_⟩
  cases u <;> exact ⟨left_hit dis ha hi,left_hit dis hb hj⟩

private theorem descendR {l r : F} {d u : Bool} {s a b} (dis : l.vars.Disjoint r.vars)
    (ha : a∈r.vars) (hb : b∈r.vars) (e : Together (.fork d l r) s u a b) : Together r s u a b := by
  obtain ⟨f,i,j,hi,hj⟩ := e
  refine ⟨f,i,j,?_⟩
  cases u <;> exact ⟨right_hit dis ha hi,right_hit dis hb hj⟩

theorem incompatible (e : F) (z : Sig) (nd : e.vars.Nodup) (X : Finset Sig) (inside : X⊆e.vars.toFinset)
    (linked : ∀d,Connected (Together e z d) X) {a b : Sig} (ha : a∈X) (hb : b∈X) : a=b := by
  induction e with
  | atom v =>
    have aa : a=v := by simpa [F.vars] using inside ha
    have bb : b=v := by simpa [F.vars] using inside hb
    exact aa.trans bb.symm
  | port => have bad := inside ha; simp [F.vars] at bad
  | fork d l r ih jh =>
    obtain ⟨ll,rr,dis⟩ := List.nodup_append'.mp (show (l.vars++r.vars).Nodup from nd)
    let side := fun x : Sig => decide (x∈l.vars)
    have invariant (x y : Sig) (related : Together (.fork d l r) z d x y) : side x=side y := by
      obtain ⟨f,i,j,hi,hj⟩ := related
      cases d <;> exact (at_side dis _ _ hi).trans (at_side dis _ _ hj).symm
    have same := linked d side (fun x _ y _ xy => invariant x y xy)
    by_cases al : a∈l.vars
    · have sub (w) (hw : w∈X) : w∈l.vars := by
        have eq := same w hw a ha
        simpa [side,al] using eq
      apply ih ll (fun w hw => List.mem_toFinset.mpr (sub w hw))
      intro c f good
      apply linked c f
      intro x hx y hy edge
      exact good x hx y hy (descendL dis (sub x hx) (sub y hy) edge)
    · have sub (w) (hw : w∈X) : w∈r.vars := by
        have eq := same w hw a ha
        have no : w∉l.vars := by simpa [side,al] using eq
        exact (List.mem_append.mp (List.mem_toFinset.mp (inside hw))).resolve_left no
      apply jh rr (fun w hw => List.mem_toFinset.mpr (sub w hw))
      intro c f good
      apply linked c f
      intro x hx y hy edge
      exact good x hx y hy (descendR dis (sub x hx) (sub y hy) edge)

def Edge (X : Finset Sig) (domain : Row→Row→Prop) (d : Bool) (a b : Sig) :=
  ∃ fixed i j : Row, if d then domain fixed i ∧ Forced X fixed i a ∧ domain fixed j ∧ Forced X fixed j b
    else domain i fixed ∧ Forced X i fixed a ∧ domain j fixed ∧ Forced X j fixed b

def Compatible (X : Finset Sig) (domain : Row→Row→Prop) :=
  ∀ Y⊆X, (∀d,Connected (Edge X domain d) Y) → ∀a∈Y,∀b∈Y,a=b

theorem compatible_of (e : F) (z : Sig) (nd : e.vars.Nodup) {X : Finset Sig} (labels : e.vars.toFinset=X)
    (domain : Row→Row→Prop)
    (route : ∀p n,domain p n → ∃ w∈X, e.pick z p n=some w ∧ separates p n w) :
    Compatible X domain := by
  have owns (p n : Row) (a : Sig) (ok : domain p n) (force : Forced X p n a) : e.pick z p n=some a := by
    obtain ⟨w,hw,resp,sep⟩ := route p n ok
    simpa only [force w hw sep] using resp
  have included (d : Bool) {a b} (h : Edge X domain d a b) : Together e z d a b := by
    obtain ⟨fixed,i,j,yes⟩ := h
    refine ⟨fixed,i,j,?_⟩
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte] at yes ⊢ <;>
      exact ⟨owns _ _ _ yes.1 yes.2.1,owns _ _ _ yes.2.2.1 yes.2.2.2⟩
  intro Y sub connected a ha b hb
  apply incompatible e z nd Y (by rwa [labels]) _ ha hb
  intro d f same
  apply connected d f
  intro v hv w hw edge
  exact same v hv w hw (included d edge)

def InGrid (U : Finset Sig) (p n : Row) := (∃m,Miss U p m) ∧ (∃q,Miss U q n)

theorem single_share_necessary {k S} (run : Live k 0 S) (size : S.card=k) :
    ∃ T U : Finset Sig, T.Nonempty ∧ T∪U=S ∧ Disjoint T U ∧
      (∀p n,InGrid U p n → ∃a∈T,separates p n a) ∧
      Compatible T (InGrid U) ∧ Compatible U (Miss T) := by
  obtain ⟨f⟩ := factor run size
  let T := f.inside
  let U := f.outside
  have split := partition f
  obtain ⟨nl,nr,_⟩ := List.nodup_append'.mp f.distinct
  have inner (p n : Row) (ok : InGrid U p n) :=
    inside_answer f (inside_cross f ok.1.choose_spec ok.2.choose_spec)
  refine ⟨T,U,closed_input f.inner f.closed,split.1,split.2,?_,?_,?_⟩
  · intro p n ok
    obtain ⟨a,ha,_,sep⟩ := inner p n ok
    exact ⟨a,ha,sep⟩
  · exact compatible_of f.inner zero nl rfl _ inner
  · exact compatible_of f.outer (f.inner.val zero) nr rfl _ (fun p n no => outside_answer f no)

end CoAO3143.OneShare

namespace CoNum4358.Tiny
open CoAO3143

def directed (w : K) (p : Fin 8) (n : Fin 7) : Bool :=
  w.getLsbD p.val && !(w.getLsbD (8+n.val))

theorem joint_bit (w : K) (p : Fin 8) (n : Fin 7) :
    (sep false (wide w)).getLsbD (p.val*7+n.val)=directed w p n := by
  have lim : p.val*7+n.val<56 := by omega
  have bd : p.val*7+n.val<160 := by omega
  have P : (p.val*7+n.val) % 56/7=p.val := by rw [Nat.mod_eq_of_lt lim]; omega
  have N : (p.val*7+n.val) % 7=n.val := by omega
  have A : (wide w).1.getLsbD (p.val*7+n.val)=w.getLsbD p.val := by
    change (pack _).getLsbD _=_
    rw [pack_bit _ _ bd]
    exact congrArg (fun j => w.getLsbD j) P
  have B : (wide w).2.getLsbD (p.val*7+n.val)=w.getLsbD (8+n.val) := by
    change (pack _).getLsbD _=_
    rw [pack_bit _ _ bd]
    exact congrArg (fun j => w.getLsbD (8+j)) N
  simp only [sep,directed,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,
    BitVec.getLsbD_not,bd,decide_true,Bool.true_and,A,B]

private theorem all_none (ws : List K) (p : Fin 8) (n : Fin 7)
    (h : (ws.all fun a => !(directed a p n))=true) :
    (unionSep false (ws.map wide)).getLsbD (p.val*7+n.val)=false := by
  induction ws with
  | nil => simp [unionSep]
  | cons a xs ih =>
    simp only [List.all_cons,Bool.and_eq_true,Bool.not_eq_true'] at h
    simp only [List.map_cons,unionSep,BitVec.getLsbD_or,joint_bit,h.1,ih h.2,Bool.false_or]

def fullMask : Nat := 0xffffffffffffff
def columnMask : Nat := 0x2040810204081
def cells (w : K) : Nat :=
  let v := w.toNat
  let u := v &&& 255
  let u := (u ||| (u<<<24)) &&& 0xf000000f
  let u := (u ||| (u<<<12)) &&& 0xc003000c003
  let rows := ((u ||| (u<<<6)) &&& columnMask)*127
  rows &&& (fullMask ^^^ ((v>>>8)*columnMask))

def missing (ws : List K) : Bool :=
  let total := ws.foldl (fun n a => n ||| cells a) 0
  if total==fullMask then false else
    let i := (fullMask ^^^ total).log2
    ws.all fun a => !(directed a (Fin.ofNat 8 (i/7)) (Fin.ofNat 7 i))

theorem missing_false {k ws} (h : Live k 0 (ws.map wide).toFinset) : missing ws=false := by
  have cell (p : Fin 8) (n : Fin 7)
      (fail : (ws.all fun a => !(directed a p n))=true) : False := by
    have z := all_none _ _ _ fail
    have cov : unionSep false (ws.map wide)=top := live_cover h rfl
    rw [cov] at z
    have bound : p.val*7+n.val<160 := by omega
    have yes : top.getLsbD (p.val*7+n.val)=true := by
      simp only [top,BitVec.getLsbD_allOnes,bound,decide_true]
    exact Bool.false_ne_true (z.symm.trans yes)
  unfold missing
  dsimp only
  split
  · rfl
  · exact Bool.eq_false_iff.mpr (cell _ _)

theorem wide_beq (a b : K) : (wide a==wide b)=(a==b) := by
  by_cases eq : a=b
  · subst a; simp
  · have no : wide a≠wide b := fun h => eq (wide_inj h)
    simp [no,eq]

def forced (ws : List K) (p : Fin 8) (n : Fin 7) (a : K) : Bool :=
  ws.all fun x => x==a || !(x.getLsbD p.val) || x.getLsbD (8+n.val)

theorem forced_eq (ws : List K) (p : Fin 8) (n : Fin 7) (a : K) :
    ProtocolProof.forcedB (ws.map wide) (pos p) (negRow n) (wide a)=forced ws p n a := by
  simp [ProtocolProof.forcedB,forced,pos_bit,neg_bit,wide_beq,Function.comp_def]

structure Rect where
  a : K
  b : K
  p : Fin 8
  q₁ : Fin 8
  q₂ : Fin 8
  n : Fin 7
  m₁ : Fin 7
  m₂ : Fin 7

def validRect (ws : List K) (r : Rect) :=
  r.a != r.b && forced ws r.p r.m₁ r.a && forced ws r.q₁ r.n r.a &&
    forced ws r.p r.m₂ r.b && forced ws r.q₂ r.n r.b

theorem invalid {k ws} (h : Live k 0 (ws.map wide).toFinset)
    (tight : (ws.map wide).toFinset.card=k+1) (r : Rect) : validRect ws r=false := by
  let c : ProtocolProof.Certificate :=
    ⟨wide r.a,wide r.b,pos r.p,pos r.q₁,pos r.q₂,negRow r.n,negRow r.m₁,negRow r.m₂⟩
  have proof := ProtocolProof.verify_false h tight c
  simpa [c,ProtocolProof.verify,validRect,forced_eq,bne,wide_beq] using proof

structure Prof where
  wire : K
  unique : Nat
  posMask : Nat
  negMask : Nat

def prof (a : K) (only : Nat) : Prof :=
  let u := cells a &&& only
  let high := columnMask<<<6
  let low := fullMask ^^^ high
  let p := (u ||| ((u&&&low)+low)) &&& high
  let z := u ||| (u>>>7)
  let z := z ||| (z>>>14)
  let z := z ||| (z>>>28)
  ⟨a,u,p,z % 128⟩

def propose (a b : Prof) : Option Rect :=
  let posBoth := a.posMask &&& b.posMask
  let negBoth := a.negMask &&& b.negMask
  if posBoth==0 || negBoth==0 then none else
    let p := posBoth.log2/7
    let n := negBoth.log2
    let band := 127<<<(7*p)
    let col := columnMask<<<n
    let A := fun x : Nat => Fin.ofNat 8 ((x&&&col).log2/7)
    let B := fun x : Nat => Fin.ofNat 7 ((x&&&band).log2 % 7)
    some ⟨a.wire,b.wire,Fin.ofNat 8 p,A a.unique,A b.unique,Fin.ofNat 7 n,B a.unique,B b.unique⟩

def firstHit : List Prof → Option Rect
  | [] => none
  | p::ps => (ps.findSome? (propose p)).orElse fun _ => firstHit ps

def restrict (ws : List K) : Bool :=
  let seen := ws.foldl (fun (p : Nat×Nat) a =>
    let u := cells a; (p.1|||u,p.2||| (u&&&p.1))) (0,0)
  let only := seen.1 ^^^ seen.2
  (firstHit (ws.map fun w => prof w only)).any (validRect ws)

theorem restrict_false {k ws} (h : Live k 0 (ws.map wide).toFinset)
    (tight : (ws.map wide).toFinset.card=k+1) : restrict ws=false := by
  unfold restrict
  dsimp only
  generalize firstHit _ = hint
  cases hint with
  | none => rfl
  | some r => exact invalid h tight r

end CoNum4358.Tiny

namespace CoNum4358.Tiny.ShareGrid
open CoAO3143
open CoAO3143.ProtocolProof (Forced separates)

def up (X : Finset K) : Finset Sig := X.image wide
def FreeCell (X : Finset K) (p : Fin 8) (n : Fin 7) := ∀a∈X,directed a p n=false
def Required (X : Finset K) (p : Fin 8) (n : Fin 7) :=
  (∃m,FreeCell X p m) ∧ (∃q,FreeCell X q n)
def Owner (X : Finset K) (p : Fin 8) (n : Fin 7) (a : K) := ∀b∈X,directed b p n=true → b=a

def Arc (X : Finset K) (D : Fin 8→Fin 7→Prop) (d : Bool) (a b : K) := if d then
  ∃ (p : Fin 8) (i j : Fin 7), D p i ∧ Owner X p i a ∧ D p j ∧ Owner X p j b
  else ∃ (n : Fin 7) (i j : Fin 8), D i n ∧ Owner X i n a ∧ D j n ∧ Owner X j n b

def Linked (r : K → K → Prop) (s : Finset K) :=
  ∀ c : K→Bool, (∀x∈s,∀y∈s,r x y → c x=c y) → ∀x∈s,∀y∈s,c x=c y

def Compatible (X : Finset K) (D : Fin 8→Fin 7→Prop) :=
  ∀ s⊆X, (∀d,Linked (Arc X D d) s) → ∀a∈s,∀b∈s,a=b

def Feasible (A B : Finset K) :=
  (∀p n,Required B p n → ∃w∈A,directed w p n=true) ∧
    Compatible A (Required B) ∧ Compatible B (FreeCell A)

theorem separates_iff (a : K) (p : Fin 8) (n : Fin 7) :
    separates (pos p) (negRow n) (wide a) ↔ directed a p n=true := by
  simp only [separates,pos_bit,neg_bit,directed,Bool.and_eq_true,Bool.not_eq_true']

theorem free_cell {X : Finset K} {p n} (h : FreeCell X p n) :
    OneShare.Miss (up X) (pos p) (negRow n) := by
  intro w hw yes
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hw
  exact Bool.false_ne_true ((h a ha).symm.trans ((separates_iff a p n).mp yes))

theorem required_grid {X : Finset K} {p n} (h : Required X p n) :
    OneShare.InGrid (up X) (pos p) (negRow n) := by
  obtain ⟨⟨m,hm⟩,⟨q,hq⟩⟩ := h
  exact ⟨⟨negRow m,free_cell hm⟩,⟨pos q,free_cell hq⟩⟩

theorem owner_forced {X : Finset K} {p n a} (h : Owner X p n a) :
    Forced (up X) (pos p) (negRow n) (wide a) := by
  intro w hw yes
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hw
  exact congrArg wide (h b hb ((separates_iff _ _ _).mp yes))

theorem restrict_graph {X : Finset K} {large : Row→Row→Prop} {D : Fin 8→Fin 7→Prop}
    (old : OneShare.Compatible (up X) large) (ok : ∀p n,D p n→large (pos p) (negRow n)) :
    Compatible X D := by
  have arcs (d : Bool) {a b} (edge : Arc X D d a b) : OneShare.Edge (up X) large d (wide a) (wide b) := by
    cases d
    · obtain ⟨n,i,j,hi,oi,hj,oj⟩ := edge
      exact ⟨negRow n,pos i,pos j,ok _ _ hi,owner_forced oi,ok _ _ hj,owner_forced oj⟩
    · obtain ⟨p,i,j,hi,oi,hj,oj⟩ := edge
      exact ⟨pos p,negRow i,negRow j,ok _ _ hi,owner_forced oi,ok _ _ hj,owner_forced oj⟩
  intro s sub all a ha b hb
  apply wide_inj
  apply old (up s) (Finset.image_mono wide sub) _ (wide a) (Finset.mem_image_of_mem _ ha)
    (wide b) (Finset.mem_image_of_mem _ hb)
  intro d color mono x hx y hy
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
  apply all d (fun a => color (wide a)) _ v hv w hw
  intro r hr t ht arc
  exact mono _ (Finset.mem_image_of_mem _ hr) _ (Finset.mem_image_of_mem _ ht) (arcs d arc)

theorem tight_plus_one {k : Nat} {X : Finset K} (run : Live k 0 (up X)) (size : X.card=k) :
    ∃ A⊆X, A.Nonempty ∧ Feasible A (X\A) := by
  classical
  have count : (up X).card=k := (Finset.card_image_of_injective _ wide_inj).trans size
  obtain ⟨T,U,tn,both,dis,cover,inner,outer⟩ := OneShare.single_share_necessary run count
  let A := X.filter fun a => wide a∈T
  have sub : A⊆X := Finset.filter_subset _ _
  have tt : up A=T := by
    ext w
    constructor
    · intro hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hv).2
    · intro hw
      have all : w∈up X := both ▸ Finset.mem_union_left U hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp all
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hv,hw⟩)
  have uu : up (X\A)=U := by
    ext w
    constructor
    · intro hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨vx,va⟩ := Finset.mem_sdiff.mp hv
      have all : wide v∈T∪U := by rw [both]; exact Finset.mem_image_of_mem _ vx
      exact (Finset.mem_union.mp all).resolve_left (fun vt => va (Finset.mem_filter.mpr ⟨vx,vt⟩))
    · intro hw
      have all : w∈up X := both ▸ Finset.mem_union_right T hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp all
      apply Finset.mem_image_of_mem
      apply Finset.mem_sdiff.mpr
      exact ⟨hv,fun va => Finset.disjoint_left.mp dis (Finset.mem_filter.mp va).2 hw⟩
  rw [←tt,←uu] at cover inner outer
  have na : A.Nonempty := by
    obtain ⟨v,hv⟩ := tn
    rw [←tt] at hv
    obtain ⟨x,hx,_⟩ := Finset.mem_image.mp hv
    exact ⟨x,hx⟩
  refine ⟨A,sub,na,?_,restrict_graph inner (fun _ _ h => required_grid h),
    restrict_graph outer (fun _ _ h => free_cell h)⟩
  intro p n need
  obtain ⟨v,hv,yes⟩ := cover (pos p) (negRow n) (required_grid need)
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
  exact ⟨a,ha,(separates_iff _ _ _).mp yes⟩

end CoNum4358.Tiny.ShareGrid

namespace CoNum4358.Tiny.Masks
open CoAO3143

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def posMask (x : Nat) :=
  let u := (x ||| (x<<<24)) &&& 0xf000000f
  let u := (u ||| (u<<<12)) &&& 0xc003000c003
  ((u ||| (u<<<6)) &&& columnMask)*127

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def negMask (x : Nat) := fullMask ^^^ (x*columnMask)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem pos_bits : ∀ (x : Fin 256) (p : Fin 8) (n : Fin 7),
    (posMask x.val).testBit (p.val*7+n.val)=x.val.testBit p.val := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem neg_bits : ∀ (x : Fin 128) (p : Fin 8) (n : Fin 7),
    (negMask x.val).testBit (p.val*7+n.val)= !(x.val.testBit n.val) := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem cells_bit (w : K) (p : Fin 8) (n : Fin 7) :
    (cells w).testBit (p.val*7+n.val)=directed w p n := by
  have loEq : (w.toNat &&& 255)=w.toNat % 2^8 := Nat.and_two_pow_sub_one_eq_mod _ 8
  let lo : Fin 256 := ⟨w.toNat % 2^8,Nat.mod_lt _ (by decide)⟩
  have high : w.toNat>>>8<128 := by
    rw [Nat.shiftRight_eq_div_pow]
    have lim : w.toNat<32768 := w.isLt
    omega
  let hi : Fin 128 := ⟨w.toNat>>>8,high⟩
  change ((posMask (w.toNat &&& 255) &&& negMask (w.toNat>>>8)).testBit _)=_
  rw [loEq]
  change ((posMask lo.val &&& negMask hi.val).testBit _)=_
  rw [Nat.testBit_and,pos_bits,neg_bits]
  change ((w.toNat % 2^8).testBit p.val && !(w.toNat>>>8).testBit n.val)=_
  simp only [directed,BitVec.getLsbD,Nat.testBit_mod_two_pow,p.isLt,decide_true,
    Bool.true_and,Nat.testBit_shiftRight]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def used : List W → Nat
  | [] => 0
  | w::ws => cells w.1 ||| used ws

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem used_bit (ws : List W) (p : Fin 8) (n : Fin 7) :
    (used ws).testBit (p.val*7+n.val)=
    (unionSep false ((ws.map Prod.fst).map wide)).getLsbD (p.val*7+n.val) := by
  induction ws with
  | nil => simp [used,unionSep]
  | cons w ws ih =>
    simp only [used,Nat.testBit_or,cells_bit,List.map_cons,unionSep,BitVec.getLsbD_or,
      joint_bit,ih]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def complete (mask : Nat) := (mask &&& fullMask)==fullMask

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem needed {k : Nat} {ws : List W} (h : Live k 0 ((ws.map Prod.fst).map wide).toFinset) :
    complete (used ws)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  have mask : fullMask.testBit i=decide (i<56) := Nat.testBit_two_pow_sub_one 56 i
  rw [Nat.testBit_and,mask]
  by_cases hi : i<56
  · let p : Fin 8 := ⟨i/7,by omega⟩
    let n : Fin 7 := ⟨i % 7,Nat.mod_lt _ (by decide)⟩
    have eq : p.val*7+n.val=i := by dsimp [p,n]; omega
    have cov : unionSep false ((ws.map Prod.fst).map wide)=top := live_cover h rfl
    have hit := used_bit ws p n
    have bd : i<160 := by omega
    rw [eq,cov] at hit
    simp only [top,BitVec.getLsbD_allOnes,bd,decide_true] at hit
    simp [hi,hit]
  · simp [hi]

end CoNum4358.Tiny.Masks

namespace CoNum4358.Tiny.Corners
open CoAO3143

set_option maxRecDepth 65536 in
def counts : List K → Nat × Nat
  | [] => (0,0)
  | a::xs => let r := counts xs; let w := cells a; (w ||| r.1,r.2 ||| (w &&& r.1))

set_option maxRecDepth 65536 in
theorem seen {xs : List K} {a : K} (ha : a∈xs) (i : Nat) (yes : (cells a).testBit i=true) :
    (counts xs).1.testBit i=true := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp [counts,Nat.testBit_or,yes]
    · simp [counts,Nat.testBit_or,ih ha]

set_option maxRecDepth 65536 in
theorem repeated {xs : List K} {a b : K} (ha : a∈xs) (hb : b∈xs) (ne : a≠b)
    (i : Nat) (pa : (cells a).testBit i=true) (pb : (cells b).testBit i=true) :
    (counts xs).2.testBit i=true := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact False.elim (ne rfl)
      · simp [counts,Nat.testBit_or,Nat.testBit_and,pa,seen hb i pb]
    · rcases hb with rfl | hb
      · simp [counts,Nat.testBit_or,Nat.testBit_and,pb,seen ha i pa]
      · simp [counts,Nat.testBit_or,ih ha hb]

set_option maxRecDepth 65536 in
def exclusive (xs : List K) := (counts xs).1 ^^^ (counts xs).2

set_option maxRecDepth 65536 in
theorem owns {xs : List K} {a : K} (ha : a∈xs) (p : Fin 8) (n : Fin 7)
    (hit : (cells a &&& exclusive xs).testBit (p.val*7+n.val)=true) :
    forced xs p n a=true := by
  let i := p.val*7+n.val
  change (cells a &&& exclusive xs).testBit i=true at hit
  rw [Nat.testBit_and,Bool.and_eq_true] at hit
  have one := seen ha i hit.1
  have no : (counts xs).2.testBit i=false := by
    have eq := hit.2
    rw [exclusive,Nat.testBit_xor,one] at eq
    cases h : (counts xs).2.testBit i <;> simp_all
  apply List.all_eq_true.mpr
  intro b hb
  by_cases eq : b=a
  · simp [eq]
  · have noB : directed b p n=false := by
      apply Bool.eq_false_iff.mpr
      intro dy
      have dy' : (cells b).testBit i=true := by simpa [i,Masks.cells_bit] using dy
      exact Bool.false_ne_true (no.symm.trans (repeated ha hb (Ne.symm eq) i hit.1 dy'))
    change (b==a || !(b.getLsbD p.val) || b.getLsbD (8+n.val))=true
    cases x : b.getLsbD p.val <;> cases y : b.getLsbD (8+n.val) <;> simp_all [directed]

set_option maxRecDepth 65536 in
def tagged (xs : List K) (a : K) := prof a (exclusive xs)

set_option maxRecDepth 65536 in
def pair (x y : Prof) :=
  match propose x y with
  | none => false
  | some r => x.wire != y.wire &&
    x.unique.testBit (r.p.val*7+r.m₁.val) && x.unique.testBit (r.q₁.val*7+r.n.val) &&
    y.unique.testBit (r.p.val*7+r.m₂.val) && y.unique.testBit (r.q₂.val*7+r.n.val)

set_option maxRecDepth 65536 in
theorem pair_no {k xs} (h : Live k 0 (xs.map wide).toFinset)
    (tight : (xs.map wide).toFinset.card=k+1) {a b} (ha : a∈xs) (hb : b∈xs) :
    pair (tagged xs a) (tagged xs b)=false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  unfold pair at yes
  split at yes
  · contradiction
  · rename_i r hr
    simp only [Bool.and_eq_true] at yes
    let witness : Rect := ⟨a,b,r.p,r.q₁,r.q₂,r.n,r.m₁,r.m₂⟩
    have bad : validRect xs witness=true := by
      change ((a != b) && forced xs r.p r.m₁ a && forced xs r.q₁ r.n a &&
        forced xs r.p r.m₂ b && forced xs r.q₂ r.n b)=true
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨yes.1.1.1.1,owns ha _ _ yes.1.1.1.2⟩,owns ha _ _ yes.1.1.2⟩,
        owns hb _ _ yes.1.2⟩,owns hb _ _ yes.2⟩
    exact Bool.false_ne_true ((invalid h tight witness).symm.trans bad)

set_option maxRecDepth 65536 in
def clash (xs : List K) :=
  let r := counts xs
  let only := r.1 ^^^ r.2
  scanPairs pair (xs.map fun a => prof a only)

set_option maxRecDepth 65536 in
private theorem scan_nil {α} (f : α → α → Bool) (as : List α)
    (zero : ∀a∈as,∀b∈as,f a b=false) : scanPairs f as=false := by
  induction as with
  | nil => rfl
  | cons a xs ih =>
    have na : (xs.any (f a))=false := by
      apply Bool.eq_false_iff.mpr
      intro hit
      obtain ⟨b,hb,yes⟩ := List.any_eq_true.mp hit
      exact Bool.false_ne_true ((zero a (List.mem_cons_self) b (List.mem_cons_of_mem _ hb)).symm.trans yes)
    have rest : scanPairs f xs=false := ih (fun a ha b hb =>
      zero a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    simp only [scanPairs,na,rest,Bool.false_or]

set_option maxRecDepth 65536 in
theorem clash_no {k xs} (h : Live k 0 (xs.map wide).toFinset)
    (tight : (xs.map wide).toFinset.card=k+1) : clash xs=false := by
  change scanPairs pair (xs.map (tagged xs))=false
  apply scan_nil
  intro a ha b hb
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
  exact pair_no h tight hu hv

end CoNum4358.Tiny.Corners

namespace CoNum4358.Tiny.ShareGrid
open CoAO3143

set_option maxRecDepth 65536 in
def Covered (X : Finset K) (D : Fin 8 → Fin 7 → Prop) :=
  ∀p n,D p n → ∃w∈X,directed w p n=true

set_option maxRecDepth 65536 in
theorem outer_covered {A B : Finset K} (all : ∀p n,∃w∈A∪B,directed w p n=true) :
    Covered B (FreeCell A) := by
  intro p n miss
  obtain ⟨a,am,hit⟩ := all p n
  refine ⟨a,(Finset.mem_union.mp am).resolve_left ?_,hit⟩
  intro ha
  exact Bool.false_ne_true ((miss a ha).symm.trans hit)

set_option maxRecDepth 65536 in
private theorem two_linked {R : K→K→Prop} {a b : K} (edge : R a b) :
    Linked R ({a,b} : Finset K) := by
  intro c mono x hx y hy
  have eq := mono a (by simp) b (by simp) edge
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with xa|xb <;> rcases hy with ya|yb <;> simp_all only

set_option maxRecDepth 65536 in
theorem no_rectangle {X : Finset K} {D : Fin 8→Fin 7→Prop}
    (apart : Compatible X D) (cover : Covered X D) (r : Rect)
    (pA : D r.p r.m₁) (aP : Owner X r.p r.m₁ r.a)
    (nA : D r.q₁ r.n) (aN : Owner X r.q₁ r.n r.a)
    (pB : D r.p r.m₂) (bP : Owner X r.p r.m₂ r.b)
    (nB : D r.q₂ r.n) (bN : Owner X r.q₂ r.n r.b) : r.a=r.b := by
  have exists_owner (p n a) (h : D p n) (o : Owner X p n a) : a∈X := by
    obtain ⟨w,hw,yes⟩ := cover _ _ h
    simpa only [o w hw yes] using hw
  have ma := exists_owner _ _ _ pA aP
  have mb := exists_owner _ _ _ pB bP
  have sub : ({r.a,r.b} : Finset K)⊆X := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    obtain hv|hv := hv
    · simpa only [hv] using ma
    · simpa only [hv] using mb
  apply apart _ sub _ _ (by simp) _ (by simp)
  intro d
  apply two_linked
  cases d
  · exact ⟨r.n,r.q₁,r.q₂,nA,aN,nB,bN⟩
  · exact ⟨r.p,r.m₁,r.m₂,pA,aP,pB,bP⟩

set_option maxRecDepth 65536 in
theorem free_shrink {X Y : Finset K} (sub : X⊆Y) {p n} (h : FreeCell Y p n) :
    FreeCell X p n := fun a ha => h a (sub ha)

set_option maxRecDepth 65536 in
theorem required_shrink {X Y : Finset K} (sub : X⊆Y) {p n} (h : Required Y p n) :
    Required X p n := by
  obtain ⟨⟨m,hm⟩,⟨q,hq⟩⟩ := h
  exact ⟨⟨m,free_shrink sub hm⟩,⟨q,free_shrink sub hq⟩⟩

set_option maxRecDepth 65536 in
theorem owner_shrink {X Y : Finset K} (sub : X⊆Y) {p n a} (h : Owner Y p n a) :
    Owner X p n a := fun b hb => h b (sub hb)

set_option maxRecDepth 65536 in
def cov (xs : List K) := (Corners.counts xs).1
set_option maxRecDepth 65536 in
def noBit (s : Nat) (p : Fin 8) (n : Fin 7) := !s.testBit (p.val*7+n.val)

set_option maxRecDepth 65536 in
theorem noBit_free {xs : List K} {p n} (h : noBit (cov xs) p n=true) : FreeCell xs.toFinset p n := by
  intro a ha
  apply Bool.eq_false_iff.mpr
  intro yes
  have sep := Corners.seen (List.mem_toFinset.mp ha) (p.val*7+n.val) (by rwa [Masks.cells_bit])
  have no : (cov xs).testBit (p.val*7+n.val)=false := by simpa only [noBit,Bool.not_eq_true'] using h
  exact Bool.false_ne_true (no.symm.trans sep)

set_option maxRecDepth 65536 in
def productBit (s : Nat) (p : Fin 8) (n : Fin 7) : Bool :=
  let uncovered := fullMask ^^^ s
  let m := Fin.ofNat 7 (((uncovered >>> (p.val*7)) &&& 127).log2)
  let q := Fin.ofNat 8 (((uncovered &&& (columnMask <<< n.val)).log2)/7)
  noBit s p m && noBit s q n

set_option maxRecDepth 65536 in
theorem productBit_required {xs : List K} {p n} (h : productBit (cov xs) p n=true) :
    Required xs.toFinset p n := by
  let mask := fullMask ^^^ cov xs
  let m := Fin.ofNat 7 (((mask >>> (p.val*7)) &&& 127).log2)
  let q := Fin.ofNat 8 (((mask &&& (columnMask <<< n.val)).log2)/7)
  change (noBit (cov xs) p m && noBit (cov xs) q n)=true at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hp,hn⟩ := h
  exact ⟨⟨m,noBit_free hp⟩,⟨q,noBit_free hn⟩⟩

set_option maxRecDepth 65536 in
theorem forced_owner {xs : List K} {p n a} (h : forced xs p n a=true) :
    Owner xs.toFinset p n a := by
  intro b hb yes
  have eq := List.all_eq_true.mp h b (List.mem_toFinset.mp hb)
  simp only [directed,Bool.and_eq_true,Bool.not_eq_true'] at yes
  simpa [yes.1,yes.2] using eq

set_option maxRecDepth 65536 in
def rectBit (xs : List K) (dom : Fin 8→Fin 7→Bool) (r : Rect) :=
  validRect xs r && dom r.p r.m₁ && dom r.q₁ r.n && dom r.p r.m₂ && dom r.q₂ r.n

set_option maxRecDepth 65536 in
theorem rectBit_false {X : Finset K} {xs : List K} (sub : X⊆xs.toFinset)
    {D : Fin 8→Fin 7→Prop} (apart : Compatible X D) (cover : Covered X D)
    {dom : Fin 8→Fin 7→Bool} (valid : ∀p n, dom p n=true → D p n) (r : Rect) :
    rectBit xs dom r=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [rectBit,validRect,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ne,ap⟩,an⟩,bp⟩,bn⟩,pa⟩,na⟩,pb⟩,nb⟩ := h
  exact ne (no_rectangle apart cover r (valid _ _ pa) (owner_shrink sub (forced_owner ap))
    (valid _ _ na) (owner_shrink sub (forced_owner an))
    (valid _ _ pb) (owner_shrink sub (forced_owner bp))
    (valid _ _ nb) (owner_shrink sub (forced_owner bn)))

end CoNum4358.Tiny.ShareGrid

namespace CoNum4358.Tiny.ShareGrid
open CoAO3143

set_option maxRecDepth 65536 in
theorem owned_miss {A B : Finset K} {a p n} (own : Owner (A∪B) p n a) (na : a∉B) :
    FreeCell B p n := by
  intro b mb
  apply Bool.eq_false_iff.mpr
  intro hit
  have eq := own b (Finset.mem_union_right _ mb) hit
  exact na (by simpa only [eq] using mb)

set_option maxRecDepth 65536 in
private theorem own_miss_left {A B : Finset K} {a p n} (own : Owner (A∪B) p n a) (na : a∉A) :
    FreeCell A p n := by
  intro b mb
  apply Bool.eq_false_iff.mpr
  intro hit
  have eq := own b (Finset.mem_union_left _ mb) hit
  exact na (by simpa only [eq] using mb)

set_option maxRecDepth 65536 in
private theorem free_req {A : Finset K} {p n} (no : FreeCell A p n) : Required A p n :=
  ⟨⟨n,no⟩,⟨p,no⟩⟩

set_option maxRecDepth 65536 in
theorem opposite {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    (r : Rect) (h : validRect xs r=true) : decide (r.a∈A)≠decide (r.b∈A) := by
  simp only [validRect,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨⟨⟨⟨ne,ap⟩,an⟩,bp⟩,bn⟩ := h
  have lift {p n v} (h : forced xs p n v=true) : Owner (A∪B) p n v := by rw [←same]; exact forced_owner h
  have aP := lift ap
  have aN := lift an
  have bP := lift bp
  have bN := lift bn
  intro eq
  by_cases ma : r.a∈A
  · have mb : r.b∈A := by simpa [ma] using eq.symm
    have high : A⊆A∪B := Finset.subset_union_left
    have noA : r.a∉B := fun h => Finset.disjoint_left.mp dis ma h
    have noB : r.b∉B := fun h => Finset.disjoint_left.mp dis mb h
    exact ne (no_rectangle good.2.1 good.1 r
      (free_req (owned_miss aP noA)) (owner_shrink high aP)
      (free_req (owned_miss aN noA)) (owner_shrink high aN)
      (free_req (owned_miss bP noB)) (owner_shrink high bP)
      (free_req (owned_miss bN noB)) (owner_shrink high bN))
  · have mb : r.b∉A := by simpa [ma] using eq.symm
    have high : B⊆A∪B := Finset.subset_union_right
    exact ne (no_rectangle good.2.2 (outer_covered union) r
      (own_miss_left aP ma) (owner_shrink high aP)
      (own_miss_left aN ma) (owner_shrink high aN)
      (own_miss_left bP mb) (owner_shrink high bP)
      (own_miss_left bN mb) (owner_shrink high bN))

set_option maxRecDepth 65536 in
def shade (xs : List K) (a b : Prof) :=
  match propose a b with
  | none => false
  | some r => r.a==a.wire && r.b==b.wire && validRect xs r

set_option maxRecDepth 65536 in
theorem shade_opposite {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    {a b : Prof} (ok : shade xs a b=true) : decide (a.wire∈A)≠decide (b.wire∈A) := by
  unfold shade at ok
  split at ok
  · contradiction
  · rename_i r hr
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    have neq := opposite dis good union same r ok.2
    simpa only [ok.1.1,ok.1.2] using neq

end CoNum4358.Tiny.ShareGrid

namespace CoNum4358.Tiny.ShareGrid.Forest
open CoAO3143

structure Label where
  wire : K
  root : K
  flip : Bool
deriving DecidableEq, Repr

def Correct (color : K→Bool) (ls : List Label) := ∀v∈ls,color v.wire=xor (color v.root) v.flip

def seed (xs : List K) := xs.map fun w => Label.mk w w false
theorem seed_ok (c : K→Bool) (xs : List K) : Correct c (seed xs) := by
  intro l hl
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp hl
  simp

def locate (ls : List Label) (x : K) := ls.find? fun v => v.wire==x

private theorem located {ls : List Label} {x l} (h : locate ls x=some l) : l∈ls ∧ l.wire=x := by
  have hit : (fun v : Label => v.wire==x) l=true := List.find?_some (p:=fun v : Label => v.wire==x) (a:=l) h
  exact ⟨List.mem_of_find?_eq_some h,beq_iff_eq.mp hit⟩

def rebase (a b : Label) (v : Label) :=
  if v.root=b.root then ⟨v.wire,a.root,xor v.flip (!(xor a.flip b.flip))⟩ else v

private theorem xor_rebase {a b x y z : Bool} (different : xor a x≠xor b y) :
    xor b z=xor a (xor z (!(xor x y))) := by
  cases a <;> cases b <;> cases x <;> cases y <;> cases z <;> simp_all

private theorem rebase_ok (c : K→Bool) {ls} (valid : Correct c ls) {a b : Label}
    (ma : a∈ls) (mb : b∈ls) (ne : c a.wire≠c b.wire) : Correct c (ls.map (rebase a b)) := by
  intro l hl
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hl
  have e : xor (c a.root) a.flip≠xor (c b.root) b.flip := by rwa [←valid a ma,←valid b mb]
  by_cases h : v.root=b.root
  · rw [show rebase a b v=⟨v.wire,a.root,xor v.flip (!(xor a.flip b.flip))⟩ from if_pos h]
    change c v.wire=xor (c a.root) (xor v.flip (!(xor a.flip b.flip)))
    rw [valid v hv,h]
    exact xor_rebase (z:=v.flip) e
  · simpa only [rebase,if_neg h] using valid v hv

def link (x y : K) (ls : List Label) : Option (List Label) := do
  let some a := locate ls x | return ls
  let some b := locate ls y | return ls
  if a.root=b.root then
    if a.flip=b.flip then none else return ls
  else return ls.map (rebase a b)

theorem link_ok (c : K→Bool) {ls} (valid : Correct c ls) {x y} (ne : c x≠c y) :
    ∃ rs,link x y ls=some rs ∧ Correct c rs ∧ rs.map Label.wire=ls.map Label.wire := by
  cases ha : locate ls x with
  | none => exact ⟨ls,by simp [link,ha],valid,rfl⟩
  | some a =>
    cases hb : locate ls y with
    | none => exact ⟨ls,by simp [link,ha,hb],valid,rfl⟩
    | some b =>
      obtain ⟨am,ax⟩ := located ha
      obtain ⟨bm,byy⟩ := located hb
      have diff : c a.wire≠c b.wire := by simpa only [ax,byy] using ne
      by_cases same : a.root=b.root
      · have flip : a.flip≠b.flip := by
          intro h
          apply diff
          rw [valid a am,valid b bm,same,h]
        exact ⟨ls,by simp [link,ha,hb,same,flip],valid,rfl⟩
      · refine ⟨_,by simp [link,ha,hb,same],rebase_ok c valid am bm diff,?_⟩
        rw [List.map_map]
        apply List.map_congr_left
        intro v hv
        by_cases e : v.root=b.root <;> simp [Function.comp_def,rebase,e]

def edges (xs : List K) : List Prof → List (K×K)
  | [] => []
  | a::r => (r.filterMap (fun b => if shade xs a b then some (a.wire,b.wire) else none))++edges xs r

theorem edges_valid {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    (items : List Prof) (e : K×K) (mem : e∈edges xs items) :
    decide (e.1∈A)≠decide (e.2∈A) := by
  induction items with
  | nil => simp [edges] at mem
  | cons a r ih =>
    rcases List.mem_append.mp mem with h|h
    · obtain ⟨b,_,yes⟩ := List.mem_filterMap.mp h
      by_cases ok : shade xs a b=true
      · have heq : (a.wire,b.wire)=e := by simpa [ok] using yes
        rw [←heq]
        exact shade_opposite dis good union same ok
      · simp [ok] at yes
    · exact ih h

def compile : List (K×K) → List Label → Option (List Label)
  | [],ls => some ls
  | e::es,ls => (link e.1 e.2 ls).bind (compile es)

theorem compile_ok (c : K→Bool) (es : List (K×K)) (ls : List Label) (valid : Correct c ls)
    (ne : ∀e∈es,c e.1≠c e.2) : ∃rs,compile es ls=some rs ∧ Correct c rs ∧ rs.map Label.wire=ls.map Label.wire := by
  induction es generalizing ls with
  | nil => exact ⟨ls,rfl,valid,rfl⟩
  | cons e es ih =>
    obtain ⟨mid,eq,gm,wm⟩ := link_ok c valid (ne e List.mem_cons_self)
    obtain ⟨rs,out,gr,wr⟩ := ih mid gm (fun v hv => ne v (List.mem_cons_of_mem _ hv))
    exact ⟨rs,by simp [compile,eq,out],gr,wr.trans wm⟩

end CoNum4358.Tiny.ShareGrid.Forest

namespace CoNum4358.Tiny.ShareGrid
open CoAO3143

set_option maxRecDepth 65536 in
def estimateProduct (used : Nat) :=
  let u := fullMask ^^^ used
  let high := columnMask<<<6
  let low := fullMask ^^^ high
  let p := ((u ||| ((u&&&low)+low)) &&& high)>>>6
  let z := u ||| (u>>>7)
  let z := z ||| (z>>>14)
  let z := z ||| (z>>>28)
  p*(z % 128)

set_option maxRecDepth 65536 in
def uncoveredProduct (left right prod : Nat) :=
  let missing := prod &&& (fullMask ^^^ left)
  if missing==0 then false else
    let i := missing.log2
    let p := Fin.ofNat 8 (i/7)
    let n := Fin.ofNat 7 i
    productBit right p n && noBit left p n

set_option maxRecDepth 65536 in
theorem product_no {A B : Finset K} {xs ys : List K} (left : A⊆xs.toFinset) (right : B⊆ys.toFinset)
    (guarantee : Covered A (Required B)) (mask : Nat) : uncoveredProduct (cov xs) (cov ys) mask=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  unfold uncoveredProduct at h
  dsimp only at h
  split at h
  · contradiction
  · rw [Bool.and_eq_true] at h
    obtain ⟨hp,hn⟩ := h
    obtain ⟨w,hw,yes⟩ := guarantee _ _ (required_shrink right (productBit_required hp))
    exact Bool.false_ne_true ((noBit_free hn w (left hw)).symm.trans yes)

set_option maxRecDepth 65536 in
def localRect (xs : List K) (mask : Nat) (dom : Fin 8→Fin 7→Bool) :=
  let only := Corners.exclusive xs &&& mask
  (firstHit (xs.map fun a => prof a only)).any (rectBit xs dom)

set_option maxRecDepth 65536 in
theorem local_no {X : Finset K} {xs : List K} (sub : X⊆xs.toFinset)
    {D : Fin 8→Fin 7→Prop} (apart : Compatible X D) (cover : Covered X D)
    {dom : Fin 8→Fin 7→Bool} (valid : ∀p n,dom p n=true → D p n) (mask : Nat) :
    localRect xs mask dom=false := by
  unfold localRect
  dsimp only
  generalize firstHit _ = hint
  cases hint with
  | none => rfl
  | some r => exact rectBit_false sub apart cover valid r

set_option maxRecDepth 65536 in
def partialBlock (left right : List K) :=
  let ca := cov left
  let cb := cov right
  let p := estimateProduct cb
  uncoveredProduct ca cb p || localRect left p (productBit cb) ||
    localRect right (fullMask ^^^ ca) (noBit ca)

set_option maxRecDepth 65536 in
theorem partial_no {A B : Finset K} {xs ys : List K} (left : A⊆xs.toFinset) (right : B⊆ys.toFinset)
    (good : Feasible A B) (union : ∀p n,∃w∈A∪B,directed w p n=true) :
    partialBlock xs ys=false := by
  have pa := product_no left right good.1 (estimateProduct (cov ys))
  have pb := local_no left good.2.1 good.1 (fun _ _ h => required_shrink right (productBit_required h))
    (estimateProduct (cov ys))
  have pc := local_no right good.2.2 (outer_covered union) (fun _ _ h => free_shrink left (noBit_free h))
    (fullMask ^^^ cov xs)
  simp only [partialBlock,pa,pb,pc,Bool.false_or]

set_option maxRecDepth 65536 in
def possible : List K → List K → List K → Bool
  | a,b,[] => !a.isEmpty && !(partialBlock a b)
  | a,b,h::rs =>
    !(partialBlock (a++h::rs) (b++h::rs)) &&
      (possible (h::a) b rs || possible a (h::b) rs)

set_option maxRecDepth 65536 in
theorem possible_yes {A B : Finset K} (na : A.Nonempty) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true)
    (left right rest : List K) (al : A⊆(left++rest).toFinset) (br : B⊆(right++rest).toFinset)
    (dis : Disjoint A B) : possible left right rest=true := by
  induction rest generalizing left right with
  | nil =>
    simp only [List.append_nil] at al br
    have lne : left≠[] := by
      obtain ⟨a,ha⟩ := na
      intro e
      have bad := al ha
      simp [e] at bad
    simp [possible,lne,partial_no al br good union]
  | cons h rs ih =>
    have ok := partial_no al br good union
    simp only [possible,ok,Bool.not_false,Bool.true_and,Bool.or_eq_true]
    by_cases ha : h∈A
    · left
      apply ih (h::left) right
      · intro x hx
        have old := al hx
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at old ⊢
        tauto
      · intro x hx
        have old := br hx
        have ne : x≠h := by
          intro eq
          exact Finset.disjoint_left.mp dis ha (by simpa only [eq] using hx)
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at old ⊢
        tauto
    · right
      apply ih left (h::right)
      · intro x hx
        have old := al hx
        have ne : x≠h := fun eq => ha (by simpa only [eq] using hx)
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at old ⊢
        tauto
      · intro x hx
        have old := br hx
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at old ⊢
        tauto

set_option maxRecDepth 65536 in
theorem reports_one (xs : List K) (p : Fin 8) (n : Fin 7) :
    (unionSep false (xs.map wide)).getLsbD (p.val*7+n.val)=true ↔
      ∃a∈xs,directed a p n=true := by
  induction xs with
  | nil => simp [unionSep]
  | cons a xs ih =>
    simp only [List.map_cons,unionSep,BitVec.getLsbD_or,joint_bit,Bool.or_eq_true,ih,List.mem_cons]
    constructor
    · rintro (h|⟨b,hb,byes⟩)
      · exact ⟨a,.inl rfl,h⟩
      · exact ⟨b,.inr hb,byes⟩
    · rintro ⟨b,(ba|bs),yes⟩
      · subst b; exact .inl yes
      · exact .inr ⟨b,bs,yes⟩

end CoNum4358.Tiny.ShareGrid

namespace CoNum4358.Tiny.ShareGrid.Forest
open CoAO3143

set_option maxRecDepth 65536 in
structure Block where
  key : K
  lhs : List K
  rhs : List K
deriving Repr

set_option maxRecDepth 65536 in
def band (ls : List Label) (r : K) (b : Bool) :=
  (ls.filter (fun l => l.root==r && l.flip==b)).map Label.wire

set_option maxRecDepth 65536 in
def blocks (ls : List Label) := (ls.map Label.root).eraseDups.map fun r => Block.mk r (band ls r false) (band ls r true)

set_option maxRecDepth 65536 in
def pool : List Block → List K
  | [] => []
  | g::gs => g.lhs ++ (g.rhs ++ pool gs)

set_option maxRecDepth 65536 in
theorem in_pool {gs : List Block} {g x} (mem : g∈gs) (h : x∈g.lhs ∨ x∈g.rhs) : x∈pool gs := by
  induction gs with
  | nil => simp at mem
  | cons v vs ih =>
    rcases List.mem_cons.mp mem with e|m
    · rw [e] at h
      simp only [pool,List.mem_append]
      tauto
    · exact List.mem_append_right _ (List.mem_append_right _ (ih m))

set_option maxRecDepth 65536 in
theorem pack_all {ls : List Label} {x} (h : x∈ls.map Label.wire) : x∈pool (blocks ls) := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
  let g := Block.mk v.root (band ls v.root false) (band ls v.root true)
  apply in_pool (g:=g)
  · apply List.mem_map.mpr
    have m : v.root∈ls.map Label.root := List.mem_map.mpr ⟨v,hv,rfl⟩
    exact ⟨v.root,by simpa using m,rfl⟩
  · have hm : v.wire∈band ls v.root v.flip := by
      apply List.mem_map.mpr
      exact ⟨v,List.mem_filter.mpr ⟨hv,by simp⟩,rfl⟩
    cases e : v.flip
    · left; simpa only [g,e] using hm
    · right; simpa only [g,e] using hm

set_option maxRecDepth 65536 in
def Painted (c : K→Bool) (gs : List Block) := ∀g∈gs,
  (∀x∈g.lhs,c x=c g.key) ∧ (∀x∈g.rhs,c x= !(c g.key))

set_option maxRecDepth 65536 in
theorem bands_painted (c : K→Bool) {ls} (ok : Correct c ls) : Painted c (blocks ls) := by
  intro g hg
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hg
  have part (b : Bool) (x : K) (hx : x∈band ls r b) : c x=xor (c r) b := by
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hx
    obtain ⟨m,test⟩ := List.mem_filter.mp hl
    simp only [Bool.and_eq_true,beq_iff_eq] at test
    simpa only [test.1,test.2] using ok l m
  constructor
  · intro x hx; simpa using part false x hx
  · intro x hx; simpa using part true x hx

set_option maxRecDepth 65536 in
def solve : List Block → List K → List K → Bool
  | [],a,b => !a.isEmpty && !(uncoveredProduct (cov a) (cov b) (estimateProduct (cov b)))
  | g::gs,a,b =>
    let anySide := pool (g::gs)
    let cA := cov (a++anySide)
    let cB := cov (b++anySide)
    !(uncoveredProduct cA cB (estimateProduct cB)) &&
      (solve gs (g.lhs++a) (g.rhs++b) || solve gs (g.rhs++a) (g.lhs++b))

set_option maxRecDepth 65536 in
private theorem advance {T : Finset K} {used yes no rest : List K}
    (old : T⊆(used++(yes++(no++rest))).toFinset) (exclude : ∀v∈no,v∉T) :
    T⊆((yes++used)++rest).toFinset := by
  intro v hv
  have m := old hv
  simp only [List.mem_toFinset,List.mem_append] at m ⊢
  have out : v∉no := fun h => exclude v h hv
  tauto

set_option maxRecDepth 65536 in
private theorem swap_lists {T : Finset K} {used xs ys zs : List K}
    (old : T⊆(used++(xs++(ys++zs))).toFinset) :
    T⊆(used++(ys++(xs++zs))).toFinset := by
  intro v h
  have m := old h
  simp only [List.mem_toFinset,List.mem_append] at m ⊢
  tauto

set_option maxRecDepth 65536 in
theorem solve_ok {A B : Finset K} (na : A.Nonempty) (dis : Disjoint A B)
    (guarantee : Covered A (Required B)) (gs : List Block) (a b : List K)
    (good : Painted (fun x => decide (x∈A)) gs)
    (left : A⊆(a++pool gs).toFinset) (right : B⊆(b++pool gs).toFinset) :
    solve gs a b=true := by
  induction gs generalizing a b with
  | nil =>
    simp only [pool,List.append_nil] at left right
    have lne : a≠[] := by
      intro e
      obtain ⟨v,hv⟩ := na
      have bad := left hv
      simp [e] at bad
    simp [solve,lne,product_no left right guarantee]
  | cons g gs ih =>
    have prod := product_no left right guarantee (estimateProduct (cov (b++pool (g::gs))))
    have parts := good g List.mem_cons_self
    have gr : Painted (fun x => decide (x∈A)) gs := fun v hv => good v (List.mem_cons_of_mem _ hv)
    simp only [solve,prod,Bool.not_false,Bool.true_and,Bool.or_eq_true]
    by_cases key : g.key∈A
    · left
      have noR (x) (h : x∈g.rhs) : x∉A := by simpa [key] using parts.2 x h
      have noL (x) (h : x∈g.lhs) : x∉B := by
        have xa : x∈A := by simpa [key] using parts.1 x h
        exact fun xb => Finset.disjoint_left.mp dis xa xb
      exact ih _ _ gr (advance left noR) (advance (swap_lists right) noL)
    · right
      have noL (x) (h : x∈g.lhs) : x∉A := by simpa [key] using parts.1 x h
      have noR (x) (h : x∈g.rhs) : x∉B := by
        have xa : x∈A := by simpa [key] using parts.2 x h
        exact fun xb => Finset.disjoint_left.mp dis xa xb
      exact ih _ _ gr (advance (swap_lists left) noL) (advance right noR)

set_option maxRecDepth 65536 in
def shadePossible (xs : List K) :=
  let unique := Corners.exclusive xs
  let pairs := edges xs (xs.map fun x => prof x unique)
  (compile pairs (seed xs)).any (fun ls => solve (blocks ls) [] [])

set_option maxRecDepth 65536 in
theorem shade_yes {k : Nat} {xs : List K} (live : Live k 0 (xs.map wide).toFinset)
    (size : xs.toFinset.card=k) : shadePossible xs=true := by
  have eq : (xs.map wide).toFinset=up xs.toFinset := by ext w; simp [up]
  have l : Live k 0 (up xs.toFinset) := by rw [←eq]; exact live
  obtain ⟨A,sub,na,good⟩ := tight_plus_one l size
  let B := xs.toFinset\A
  have union : A∪B=xs.toFinset := by
    ext x
    change x∈A∪(xs.toFinset\A) ↔ _
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro (ha|⟨hx,_⟩)
      · exact sub ha
      · exact hx
    · intro hx
      by_cases ha : x∈A
      · exact .inl ha
      · exact .inr ⟨hx,ha⟩
  have dis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  have cv : ∀p n,∃w∈A∪B,directed w p n=true := by
    intro p n
    rw [union]
    have cov : unionSep false (xs.map wide)=top := live_cover live rfl
    have bd : p.val*7+n.val<160 := by omega
    have yes : (unionSep false (xs.map wide)).getLsbD (p.val*7+n.val)=true := by
      rw [cov]; simp only [top,BitVec.getLsbD_allOnes,bd,decide_true]
    obtain ⟨w,hw,hy⟩ := (reports_one xs p n).mp yes
    exact ⟨w,List.mem_toFinset.mpr hw,hy⟩
  let c := fun x : K => decide (x∈A)
  let pairs := edges xs (xs.map fun x => prof x (Corners.exclusive xs))
  obtain ⟨ls,got,valid,words⟩ := compile_ok c pairs (seed xs) (seed_ok _ _) (fun e h =>
    edges_valid dis good cv union.symm _ e h)
  have covers (v : K) (h : v∈A∪B) : v∈pool (blocks ls) := by
    apply pack_all
    rw [words]
    simpa [seed,union] using h
  have left : A⊆([]++pool (blocks ls)).toFinset := fun _ hv =>
    List.mem_toFinset.mpr (covers _ (Finset.mem_union_left _ hv))
  have right : B⊆([]++pool (blocks ls)).toFinset := fun _ hv =>
    List.mem_toFinset.mpr (covers _ (Finset.mem_union_right _ hv))
  have ok := solve_ok na dis good.1 _ [] [] (bands_painted c valid) left right
  change (compile pairs (seed xs)).any _=true
  simp only [got,Option.any_some,ok]

end CoNum4358.Tiny.ShareGrid.Forest

namespace CoNum4358.Tiny
open CoAO3143

set_option maxRecDepth 10000 in
structure Table where
  count : Nat
  row : Nat → Nat × List W
  loc : Nat → List W → Nat

set_option maxRecDepth 10000 in
def Valid (k : Nat) (T : Table) := ∀ i<T.count, ¬Trace k (T.row i).1 (T.row i).2.toFinset

set_option maxRecDepth 10000 in
def matched (T : Table) (q : Nat) (ws : List W) :=
  let i := T.loc q ws
  let r := T.row i
  decide (i<T.count) && r.1==q && ws.isPerm r.2

set_option maxRecDepth 10000 in
theorem matched_false {k T q ws} (v : Valid k T) (h : Trace k q ws.toFinset) :
    matched T q ws=false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [matched,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.isPerm_iff] at bad
  obtain ⟨⟨idx,qeq⟩,perm⟩ := bad
  have eqs : ws.toFinset=(T.row (T.loc q ws)).2.toFinset := by
    ext t; simpa using perm.mem_iff (a:=t)
  exact v _ idx (by rwa [qeq,←eqs])

set_option maxRecDepth 10000 in
theorem good_of {k q S} (run : Trace k q S) : Good k S := by
  cases run with
  | done q w orig c₀ c₃ =>
    constructor
    · rw [Finset.image_singleton,orig,target_value]
      exact Live.stop
    · intro s; exact ⟨w,Finset.mem_singleton_self _,by cases s <;> assumption⟩
  | step _ _ _ _ _ _ _ _ facts _ => exact facts

set_option maxRecDepth 10000 in
def cap (ws : List W) (s : Bool) := ws.any fun w => capability s w.2
set_option maxRecDepth 10000 in
def isGoal (w : W) := w.1==255 && w.2.1.separates && w.2.2.separates
set_option maxRecDepth 10000 in
private theorem goal_of {q S} (h : Trace 0 q S) : ∃u∈S,isGoal u=true := by
  cases h with
  | done q w o a b => exact ⟨w,Finset.mem_singleton_self _,by simp [isGoal,o,a,b]⟩

set_option maxRecDepth 10000 in
def overfull (k : Nat) (cs : List K) := decide (k+1<cs.length)
set_option maxRecDepth 10000 in
def rectBound (k : Nat) (cs : List K) := (cs.length==k+1) && restrict cs

set_option maxRecDepth 10000 in
theorem no_over {k : Nat} {cs : List K} (nd₀ : cs.Nodup) (h : Live k 0 (cs.map wide).toFinset) : overfull k cs=false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [overfull,Bool.and_eq_true,decide_eq_true_eq] at bad
  have nd : (cs.map wide).Nodup := nd₀.map wide_inj
  have eq := List.toFinset_card_of_nodup nd
  rw [List.length_map] at eq
  have width := ProtocolProof.width h
  omega

set_option maxRecDepth 10000 in
theorem no_rect {k : Nat} {cs : List K} (nd₀ : cs.Nodup) (h : Live k 0 (cs.map wide).toFinset) : rectBound k cs=false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [rectBound,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at bad
  have nd : (cs.map wide).Nodup := nd₀.map wide_inj
  have eq := List.toFinset_card_of_nodup nd
  rw [List.length_map] at eq
  exact Bool.false_ne_true ((restrict_false h (by omega)).symm.trans bad.2)

set_option maxRecDepth 10000 in
def blocked (k q : Nat) (T : Table) (ws : List W) : Bool :=
  let cs := ws.map Prod.fst
  !(cap ws true && cap ws false) || overfull k cs || missing cs ||
    (if k==0 then !(ws.any isGoal) else rectBound k cs || matched T q ws)

set_option maxRecDepth 10000 in
theorem blocked_false {k q T ws} (v : Valid k T) (nd : (ws.map Prod.fst).Nodup) (run : Trace k q ws.toFinset) :
    blocked k q T ws=false := by
  have f := good_of run
  have both (s : Bool) : cap ws s=true := by
    obtain ⟨x,hx,ok⟩ := f.caps s
    exact List.any_eq_true.mpr ⟨x,List.mem_toFinset.mp hx,ok⟩
  let cs := ws.map Prod.fst
  have same : (cs.map wide).toFinset=ws.toFinset.image (fun w => wide w.1) := by
    ext x; simp [cs]
  have orig : Live k 0 (cs.map wide).toFinset := by rw [same]; exact f.live
  change (!(cap ws true && cap ws false) || overfull k cs || missing cs ||
    (if k==0 then !(ws.any isGoal) else rectBound k cs || matched T q ws))=false
  rw [both,both,no_over nd orig,missing_false orig]
  by_cases eq : k=0
  · subst k
    obtain ⟨w,owns,yes⟩ := goal_of run
    have hit : ws.any isGoal=true := List.any_eq_true.mpr ⟨w,List.mem_toFinset.mp owns,yes⟩
    simp [hit]
  · have rr : rectBound k cs=false := no_rect nd orig
    simp [eq,matched_false v run,rr]

set_option maxRecDepth 10000 in
def remaining (ws : List W) (a b : W) (ka kb : Bool) :=
  ws.filter fun z => (z != a || ka) && (z != b || kb)

set_option maxRecDepth 10000 in
def branch (k q : Nat) (T : Table) (ws : List W) (a b : W) (d : Bool) :=
  let z := make d a b
  decide (pay d a b≤q) && z.1 != 0 && z.1 != 32767 &&
    !(bare.contains z.1) && !(ws.any fun w => w.1==z.1) &&
      options.any fun ka => options.any fun kb =>
        !(blocked k (q-pay d a b) T (z::remaining ws a b ka kb))

set_option maxRecDepth 10000 in
def check (k q : Nat) (T : Table) (ws : List W) :=
  decide (ws.map Prod.fst).Nodup && !(scanPairs (fun a b => options.any (branch k q T ws a b)) ws)

set_option maxRecDepth 10000 in
theorem mcomm (d : Bool) (a b : W) : make d a b=make d b a := by
  cases d <;> simp [make,makeKW,mergePair,mergeFlag,BitVec.or_comm,BitVec.and_comm,Bool.or_comm,Bool.and_comm]

set_option maxRecDepth 10000 in
theorem pcomm (d : Bool) (a b : W) : pay d a b=pay d b a := by simp [pay,Bool.or_comm]

end CoNum4358.Tiny

namespace CoNum4358.Tiny.Fast
open CoAO3143

set_option maxRecDepth 65536 in
def retain (a b : W) (ka kb : Bool) (rest : List W) : List W :=
  let r := if kb then b::rest else rest
  if ka then a::r else r

set_option maxRecDepth 65536 in
theorem retained {ws : List W} {a b : W} {U : Finset W}
    (sub : ws.toFinset=insert a (insert b U)) :
    (retain a b (decide (a∈U)) (decide (b∈U)) (remaining ws a b false false)).toFinset=U := by
  let rest := remaining ws a b false false
  have rem (x : W) : x∈rest ↔ x∈ws ∧ x≠a ∧ x≠b := by
    simp only [rest,remaining,List.mem_filter,Bool.or_false,Bool.and_eq_true,bne_iff_ne]
  have keep (x : W) (ka kb : Bool) : x∈retain a b ka kb rest ↔
      (ka=true ∧ x=a) ∨ (kb=true ∧ x=b) ∨ x∈rest := by
    cases ka <;> cases kb <;> simp only [retain,Bool.false_eq_true,↓reduceIte,List.mem_cons] <;> tauto
  ext x
  rw [List.mem_toFinset,keep,rem]
  have mem : x∈ws ↔ x=a ∨ x=b ∨ x∈U := by rw [←List.mem_toFinset,sub]; simp
  rw [mem]
  simp only [decide_eq_true_eq]
  by_cases xa : x=a <;> by_cases xb : x=b <;> subst_vars <;> tauto

set_option maxRecDepth 65536 in
theorem retained_clean {ws : List W} {a b : W}
    (nd : (ws.map Prod.fst).Nodup) (ha : a∈ws) (hb : b∈ws) (ne : a≠b)
    (ka kb : Bool) : ((retain a b ka kb (remaining ws a b false false)).map Prod.fst).Nodup := by
  let r := remaining ws a b false false
  have subr : r.Sublist ws := List.filter_sublist
  have inj := List.inj_on_of_nodup_map nd
  have ab : a.1≠b.1 := fun eq => ne (inj ha hb eq)
  have nr : (r.map Prod.fst).Nodup := nd.sublist (subr.map _)
  have both (v : W) (hv : v∈ws) (side : v=a ∨ v=b) : v.1∉r.map Prod.fst := by
    intro has
    obtain ⟨x,hx,e⟩ := List.mem_map.mp has
    have eq : x=v := inj (subr.subset hx) hv e
    subst x
    change v∈remaining ws a b false false at hx
    rcases side with rfl | rfl <;> simp [remaining] at hx
  have na := both a ha (Or.inl rfl)
  have nb := both b hb (Or.inr rfl)
  change ((retain a b ka kb r).map Prod.fst).Nodup
  cases ka <;> cases kb <;> simp [retain,nr,na,nb,ab]

set_option maxRecDepth 65536 in
def possible (ws : List W) (mask : Nat) :=
  if mask==fullMask then true else
    let i := (fullMask ^^^ mask).log2
    ws.any fun w => directed w.1 (Fin.ofNat 8 (i/7)) (Fin.ofNat 7 i)

set_option maxRecDepth 65536 in
theorem possible_yes {k : Nat} {ws : List W} (h : Live k 0 ((ws.map Prod.fst).map wide).toFinset) (mask : Nat) :
    possible ws mask=true := by
  unfold possible
  split
  · rfl
  · let i := (fullMask ^^^ mask).log2
    let p := Fin.ofNat 8 (i/7)
    let n := Fin.ofNat 7 i
    have atBit (ls : List W) : (unionSep false ((ls.map Prod.fst).map wide)).getLsbD (p.val*7+n.val)=
        (ls.any fun w => directed w.1 p n) := by
      induction ls with
      | nil => simp [unionSep]
      | cons a ls ih => simp only [List.map_cons,unionSep,BitVec.getLsbD_or,joint_bit,List.any_cons,ih]
    have cov : unionSep false ((ws.map Prod.fst).map wide)=top := live_cover h rfl
    have pos : p.val*7+n.val<160 := by omega
    have eq := atBit ws
    rw [cov] at eq
    have ht : top.getLsbD (p.val*7+n.val)=true := by simp only [top,BitVec.getLsbD_allOnes,pos,decide_true]
    exact eq.symm.trans ht

set_option maxRecDepth 65536 in
def finish (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false &&
    (if k==0 then ws.any isGoal else !(rectBound k (ws.map Prod.fst) || matched T q ws))

set_option maxRecDepth 65536 in
theorem finish_yes {k q T ws} (val : Valid k T) (nd : (ws.map Prod.fst).Nodup)
    (h : Trace k q ws.toFinset) : finish k q T ws=true := by
  have old := blocked_false val nd h
  unfold blocked at old
  simp only [Bool.or_eq_false_iff] at old
  have cp : (cap ws true && cap ws false)=true := by simpa using old.1.1.1
  unfold finish
  rw [cp,Bool.true_and]
  split <;> rename_i hk <;> simpa [hk] using old.2

set_option maxRecDepth 65536 in
theorem length_ok {k q : Nat} {ws : List W} (nd : (ws.map Prod.fst).Nodup)
    (h : Trace k q ws.toFinset) : ws.length≤k+1 := by
  have live := (good_of h).live
  have eq : ((ws.map Prod.fst).map wide).toFinset=ws.toFinset.image (fun w=>wide w.1) := by
    ext; simp
  rw [←eq] at live
  have n := no_over nd live
  simpa [overfull] using n

set_option maxRecDepth 65536 in
def tryGate (k q : Nat) (T : Table) (ws rest : List W) (a b : W)
    (restMask ca cb : Nat) (d : Bool) :=
  let z := make d a b
  let payNow := pay d a b
  decide (payNow≤q) && z.1 != 0 && z.1 != 32767 && !(bare.contains z.1) &&
    !(ws.any fun w => w.1==z.1) &&
    (let base := restMask ||| cells z.1
     options.any fun ka => options.any fun kb =>
       decide (1+rest.length+ka.toNat+kb.toNat≤k+1) &&
       (let fringe := z::retain a b ka kb rest
        let mask := (if ka then ca else 0) ||| (if kb then cb else 0) ||| base
        possible fringe mask && finish k (q-payNow) T fringe))

set_option maxRecDepth 65536 in
private theorem found {k q T ws U d a b} (val : Valid k T)
    (hn : (ws.map Prod.fst).Nodup) (sub : ws.toFinset=insert a (insert b U)) (ne : a≠b)
    (bd : pay d a b≤q) (pr : (make d a b).1≠0 ∧ (make d a b).1≠32767)
    (nu : (make d a b).1∉ws.toFinset.image Prod.fst) (nr : (make d a b).1∉bare)
    (child : Trace k (q-pay d a b) (insert (make d a b) U)) (rm ca cb : Nat) :
    (options.any (tryGate k q T ws (remaining ws a b false false) a b rm ca cb))=true := by
  let z := make d a b
  let ka := decide (a∈U)
  let kb := decide (b∈U)
  let rest := remaining ws a b false false
  let r := retain a b ka kb rest
  let nw := z::r
  have eq : r.toFinset=U := retained sub
  have step : Trace k (q-pay d a b) nw.toFinset := by simpa [nw,eq,z] using child
  have ha : a∈ws := by rw [←List.mem_toFinset,sub]; simp
  have hb : b∈ws := by rw [←List.mem_toFinset,sub]; simp
  have ns : (r.map Prod.fst).Nodup := retained_clean hn ha hb ne ka kb
  have nu' : z.1∉r.map Prod.fst := by
    intro bad
    obtain ⟨v,hv,he⟩ := List.mem_map.mp bad
    have hu : v∈U := by rw [←eq]; exact List.mem_toFinset.mpr hv
    have hw : v∈ws.toFinset := by rw [sub]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
    exact nu (Finset.mem_image.mpr ⟨v,hw,he⟩)
  have nd : (nw.map Prod.fst).Nodup := .cons nu' ns
  have sz : nw.length=1+rest.length+ka.toNat+kb.toNat := by
    change (z::retain a b ka kb rest).length=_
    cases ka <;> cases kb <;> simp [retain] <;> omega
  have lim : 1+rest.length+ka.toNat+kb.toNat≤k+1 := sz ▸ length_ok nd step
  have fin := finish_yes val nd step
  have live : Live k 0 ((nw.map Prod.fst).map wide).toFinset := by
    have eq : ((nw.map Prod.fst).map wide).toFinset=nw.toFinset.image (fun w=>wide w.1) := by
      ext; simp
    rw [eq]; exact (good_of step).live
  have no : (ws.any fun w => w.1==z.1)=false := by
    apply Bool.eq_false_iff.mpr
    intro bad
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp bad
    exact nu (Finset.mem_image.mpr ⟨x,List.mem_toFinset.mpr hx,beq_iff_eq.mp he⟩)
  apply List.any_eq_true.mpr
  refine ⟨d,all_options _,?_⟩
  have en : (decide (pay d a b≤q) && z.1 != 0 && z.1 != 32767 && !(bare.contains z.1) &&
      !(ws.any fun w => w.1==z.1))=true := by
    simp [bd,show z.1∉bare from nr,no]
    exact pr
  dsimp only [tryGate]
  rw [en,Bool.true_and]
  apply List.any_eq_true.mpr
  refine ⟨ka,all_options _,List.any_eq_true.mpr ⟨kb,all_options _,?_⟩⟩
  change (decide (1+rest.length+ka.toNat+kb.toNat≤k+1) && (possible nw _ && finish k _ T nw))=true
  simp [lim,possible_yes live,fin]

end CoNum4358.Tiny.Fast

namespace CoNum4358.Tiny.MaskFast
open CoAO3143
open Fast (retain retained retained_clean finish finish_yes length_ok)

set_option maxRecDepth 65536 in
abbrev Post := Nat → Nat → Table → List W → Bool
set_option maxRecDepth 65536 in
def SoundPost (post : Post) : Prop := ∀ {k q : Nat} {T : Table} {ws : List W},
  Valid k T → (ws.map Prod.fst).Nodup → Trace k q ws.toFinset → post k q T ws=true

set_option maxRecDepth 65536 in
def tryGate (post : Post) (k q : Nat) (T : Table) (ws rest : List W) (a b : W)
    (restMask ca cb : Nat) (d : Bool) :=
  let z := make d a b
  let payNow := pay d a b
  decide (payNow≤q) && z.1 != 0 && z.1 != 32767 && !(bare.contains z.1) &&
    !(ws.any fun w => w.1==z.1) &&
    (let base := restMask ||| cells z.1
     options.any fun ka => options.any fun kb =>
       decide (1+rest.length+ka.toNat+kb.toNat≤k+1) &&
       (let fringe := z::retain a b ka kb rest
        let mask := (if ka then ca else 0) ||| (if kb then cb else 0) ||| base
        Masks.complete mask && post k (q-payNow) T fringe))

set_option maxRecDepth 65536 in
def nodeWith (post : Post) (k q : Nat) (T : Table) (ws : List W) :=
  decide (ws.map Prod.fst).Nodup &&
  !(scanPairs (fun a b =>
    let rest := remaining ws a b false false
    let mask := Masks.used rest
    options.any (tryGate post k q T ws rest a b mask (cells a.1) (cells b.1))) ws)

set_option maxRecDepth 65536 in
private theorem found (post : Post) (safe : SoundPost post) {k q T ws U d a b} (val : Valid k T)
    (hn : (ws.map Prod.fst).Nodup) (sub : ws.toFinset=insert a (insert b U)) (ne : a≠b)
    (bd : pay d a b≤q) (pr : (make d a b).1≠0 ∧ (make d a b).1≠32767)
    (nu : (make d a b).1∉ws.toFinset.image Prod.fst) (nr : (make d a b).1∉bare)
    (child : Trace k (q-pay d a b) (insert (make d a b) U)) :
    (options.any (tryGate post k q T ws (remaining ws a b false false) a b
      (Masks.used (remaining ws a b false false)) (cells a.1) (cells b.1)))=true := by
  let z := make d a b
  let ka := decide (a∈U)
  let kb := decide (b∈U)
  let rest := remaining ws a b false false
  let r := retain a b ka kb rest
  let nw := z::r
  have eq : r.toFinset=U := retained sub
  have step : Trace k (q-pay d a b) nw.toFinset := by simpa [nw,eq,z] using child
  have ha : a∈ws := by rw [←List.mem_toFinset,sub]; simp
  have hb : b∈ws := by rw [←List.mem_toFinset,sub]; simp
  have ns : (r.map Prod.fst).Nodup := retained_clean hn ha hb ne ka kb
  have nu' : z.1∉r.map Prod.fst := by
    intro bad
    obtain ⟨v,hv,he⟩ := List.mem_map.mp bad
    have hu : v∈U := by rw [←eq]; exact List.mem_toFinset.mpr hv
    have hw : v∈ws.toFinset := by rw [sub]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
    exact nu (Finset.mem_image.mpr ⟨v,hw,he⟩)
  have nd : (nw.map Prod.fst).Nodup := .cons nu' ns
  have sz : nw.length=1+rest.length+ka.toNat+kb.toNat := by
    change (z::retain a b ka kb rest).length=_
    cases ka <;> cases kb <;> simp [retain] <;> omega
  have lim : 1+rest.length+ka.toNat+kb.toNat≤k+1 := sz ▸ length_ok nd step
  have fin := safe val nd step
  have live : Live k 0 ((nw.map Prod.fst).map wide).toFinset := by
    have eq : ((nw.map Prod.fst).map wide).toFinset=nw.toFinset.image (fun w=>wide w.1) := by
      ext; simp
    rw [eq]; exact (good_of step).live
  have no : (ws.any fun w => w.1==z.1)=false := by
    apply Bool.eq_false_iff.mpr
    intro bad
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp bad
    exact nu (Finset.mem_image.mpr ⟨x,List.mem_toFinset.mpr hx,beq_iff_eq.mp he⟩)
  apply List.any_eq_true.mpr
  refine ⟨d,all_options _,?_⟩
  have en : (decide (pay d a b≤q) && z.1 != 0 && z.1 != 32767 && !(bare.contains z.1) &&
      !(ws.any fun w => w.1==z.1))=true := by
    simp [bd,show z.1∉bare from nr,no]
    exact pr
  dsimp only [tryGate]
  rw [en,Bool.true_and]
  apply List.any_eq_true.mpr
  refine ⟨ka,all_options _,List.any_eq_true.mpr ⟨kb,all_options _,?_⟩⟩
  let mask := (if ka then cells a.1 else 0) ||| (if kb then cells b.1 else 0) |||
    (Masks.used rest ||| cells z.1)
  have same : mask=Masks.used nw := by
    change ((if ka then cells a.1 else 0) ||| (if kb then cells b.1 else 0) |||
      (Masks.used rest ||| cells z.1))=Masks.used (z::retain a b ka kb rest)
    cases ka <;> cases kb <;> simp only [↓reduceIte,Bool.false_eq_true,retain,Masks.used,
      Nat.or_zero,Nat.zero_or] <;> ac_rfl
  change (decide (1+rest.length+ka.toNat+kb.toNat≤k+1) &&
    (Masks.complete mask && post k _ T nw))=true
  rw [same,Masks.needed live,fin]
  simp [lim]

set_option maxRecDepth 65536 in
theorem nodeWith_ok (post : Post) (safe : SoundPost post) {k q T ws} (val : Valid k T) (yes : nodeWith post k q T ws=true) : ¬Trace (k+1) q ws.toFinset := by
  intro h
  simp only [nodeWith,Bool.and_eq_true,decide_eq_true_eq] at yes
  generalize eq : ws.toFinset=S at h
  cases h with
  | step d a b ne bd pr nu nr facts child =>
    have ha : a∈ws := by rw [←List.mem_toFinset,eq]; simp
    have hb : b∈ws := by rw [←List.mem_toFinset,eq]; simp
    have nu' : (make d a b).1∉ws.toFinset.image Prod.fst := by rwa [eq]
    have A := found post safe val yes.1 eq ne bd pr nu' nr child
    have B := found post safe (k:=k) (q:=q) (d:=d) val yes.1 (eq.trans (Finset.insert_comm _ _ _)) ne.symm
      (by rwa [pcomm d b a]) (by rwa [mcomm d b a]) (by rwa [mcomm d b a])
      (by rwa [mcomm d b a]) (by rwa [pcomm d b a,mcomm d b a])
    have same := scanPairs_complete (fun a b =>
      let rest := remaining ws a b false false
      let mask := Masks.used rest
      options.any (tryGate post k q T ws rest a b mask (cells a.1) (cells b.1))) ha hb ne
      A B
    simpa [same] using yes.2

end CoNum4358.Tiny.MaskFast

namespace CoNum4358.Tiny.Corners
open CoAO3143

def limit (k : Nat) (cs : List K) := cs.length==k+1 && clash cs

theorem limit_no {k : Nat} {cs : List K} (nd : cs.Nodup)
    (h : Live k 0 (cs.map wide).toFinset) : limit k cs=false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [limit,Bool.and_eq_true,beq_iff_eq] at bad
  have n := List.toFinset_card_of_nodup (nd.map wide_inj)
  rw [List.length_map] at n
  exact Bool.false_ne_true ((clash_no h (by omega)).symm.trans bad.2)

def post (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false &&
    (if k==0 then ws.any isGoal else !(limit k (ws.map Prod.fst) || matched T q ws))

theorem sound : MaskFast.SoundPost post := by
  intro k q T ws v nd h
  have old := Fast.finish_yes v nd h
  have loc := good_of h
  have live : Live k 0 ((ws.map Prod.fst).map wide).toFinset := by
    have E : ((ws.map Prod.fst).map wide).toFinset=ws.toFinset.image (fun w=>wide w.1) := by ext; simp
    rw [E]; exact loc.live
  unfold Fast.finish at old
  unfold post
  by_cases z : k=0
  · simpa [z] using old
  · have a := limit_no nd live
    have b := no_rect nd live
    simpa [z,a,b] using old

end CoNum4358.Tiny.Corners

namespace CoNum4358.Tiny.Splice
open CoAO3143
open WordRows

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def stamp (q : Nat) (ws : List W) :=
  (ws.foldl (fun s w => let x := emit w; s+(x ^^^ (x>>>7))*(x+89587)) (q*17+ws.length*467)) % 65536

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def stored (k i : Nat) := let row := WordRows.row (BicolorBase.tier k) i; (row.1,row.2.map read)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def bank (parent i k : Nat) : Table :=
  ⟨(BicolorBase.tier k).total,stored k,fun q ws => FastJump.lookup (FastJump.tier parent) i (stamp q ws)⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def shadeBound (k : Nat) (cs : List K) := cs.length==k && !(ShareGrid.Forest.shadePossible cs)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem source_ok {k cs} (nd : cs.Nodup) (run : Live k 0 (cs.map wide).toFinset) :
    shadeBound k cs=false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [shadeBound,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at bad
  have card := List.toFinset_card_of_nodup nd
  have cap := ShareGrid.Forest.shade_yes run (card.trans bad.1)
  exact Bool.false_ne_true (bad.2.symm.trans cap)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def post (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false &&
    (if k==0 then ws.any isGoal else
      !(Corners.limit k (ws.map Prod.fst) || matched T q ws || shadeBound k (ws.map Prod.fst)))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem sound : MaskFast.SoundPost post := by
  intro k q T ws val nd h
  have narrow : Live k 0 ((ws.map Prod.fst).map wide).toFinset := by
    have E : ((ws.map Prod.fst).map wide).toFinset=ws.toFinset.image (fun w=>wide w.1) := by ext; simp
    rw [E]; exact (good_of h).live
  have old := Corners.sound val nd h
  have ma := matched_false val h
  have li := Corners.limit_no nd narrow
  have sh := source_ok nd narrow
  simpa only [Corners.post,post,li,ma,sh,Bool.false_or] using old

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
def Layer (k : Nat) := ∀i<(BicolorBase.tier k).total,¬Trace k (stored k i).1 (stored k i).2.toFinset

end CoNum4358.Tiny.Splice

namespace CoNum4358.Tiny.Splice
open CoAO3143
open CoNum4358.WordRows

set_option maxRecDepth 65536 in
def orbitItem (check : Nat → Nat → Bool) (k i : Nat) :=
  let ref := (Orbits.tier (k+1)).val i
  if ref==0 then check k i else
    let j := ref-1
    let source := stored (k+1) i
    let target := stored (k+1) j
    decide (j<i) && source.1==target.1 && (source.2.map Reflection.wire).isPerm target.2

set_option maxRecDepth 65536 in
theorem orbit_complete {k : Nat} {check : Nat → Nat → Bool}
    (actual : ∀ i,check k i=true → ¬Trace (k+1) (stored (k+1) i).1 (stored (k+1) i).2.toFinset)
    (data : ∀i<(BicolorBase.tier (k+1)).total,orbitItem check k i=true) : Layer (k+1) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have checked := data i hi
    unfold orbitItem at checked
    dsimp only at checked
    split at checked
    · exact actual i checked
    · simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.isPerm_iff] at checked
      obtain ⟨⟨before,quota⟩,per⟩ := checked
      have no := ih _ before (by omega)
      intro h
      have reflected := Reflection.trace h
      have identical : ((stored (k+1) i).2.toFinset.image Reflection.wire)=
          (stored (k+1) ((Orbits.tier (k+1)).val i-1)).2.toFinset := by
        ext x
        have p := per.mem_iff (a:=x)
        simpa only [Finset.mem_image,List.mem_toFinset,List.mem_map] using p
      exact no (by rw [←quota,←identical]; exact reflected)

end CoNum4358.Tiny.Splice

namespace CoNum4358.Tiny.ShareGrid.Forest
open CoAO3143

set_option maxRecDepth 65536 in
inductive Bundle where
  | empty
  | more (left right total : Nat) (leftUsed rightUsed : Bool) (tail : Bundle)

set_option maxRecDepth 65536 in
def Bundle.total : Bundle → Nat
  | .empty => 0
  | .more _ _ u _ _ _ => u

set_option maxRecDepth 65536 in
def bundle : List Block → Bundle
  | [] => .empty
  | g::gs =>
    let rest := bundle gs
    let l := cov g.lhs
    let r := cov g.rhs
    .more l r (l ||| (r ||| rest.total)) (!g.lhs.isEmpty) (!g.rhs.isEmpty) rest

set_option maxRecDepth 65536 in
def ground : Bundle → Nat → Nat → Bool → Bool
  | .empty,a,b,used => used && !(uncoveredProduct a b (estimateProduct b))
  | .more x y u cx cy tail,a,b,used =>
    let ca := a ||| u
    let cb := b ||| u
    !(uncoveredProduct ca cb (estimateProduct cb)) &&
      (ground tail (x|||a) (y|||b) (cx||used) || ground tail (y|||a) (x|||b) (cy||used))

set_option maxRecDepth 65536 in
theorem cov_append (xs ys : List K) : cov (xs++ys)=cov xs ||| cov ys := by
  induction xs with
  | nil => simp [cov,Corners.counts]
  | cons x xs ih =>
    change cells x ||| cov (xs++ys)=(cells x ||| cov xs) ||| cov ys
    rw [ih,Nat.or_assoc]

set_option maxRecDepth 65536 in
theorem full_bundle (gs : List Block) : (bundle gs).total=cov (pool gs) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change cov g.lhs ||| (cov g.rhs ||| (bundle gs).total)=cov (g.lhs++(g.rhs++pool gs))
    rw [ih,cov_append,cov_append]

set_option maxRecDepth 65536 in
theorem used_append (a b : List K) : (a++b).isEmpty.not=(a.isEmpty.not || b.isEmpty.not) := by
  cases a <;> cases b <;> rfl

set_option maxRecDepth 65536 in
theorem bundle_eq (gs : List Block) (a b : List K) :
    ground (bundle gs) (cov a) (cov b) (!a.isEmpty)=solve gs a b := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    simp only [ground,bundle,solve,pool,cov_append,full_bundle]
    have h1 := ih (g.lhs++a) (g.rhs++b)
    have h2 := ih (g.rhs++a) (g.lhs++b)
    simp only [cov_append,used_append] at h1 h2
    rw [h1,h2]

end CoNum4358.Tiny.ShareGrid.Forest

namespace CoNum4358.Tiny.ShareGrid.Forest
open CoAO3143

structure Indicator where
  wire : K
  rows : Nat
  cols : Nat

def rowSpread (u : Nat) :=
  let x := u ||| (u>>>1)
  let y := x ||| (x>>>2)
  (y ||| (y>>>3)) &&& columnMask &&& fullMask

def colSpread (u : Nat) :=
  let x := u ||| (u>>>7)
  let y := x ||| (x>>>14)
  (y ||| (y>>>28)) &&& 127

def indicator (only : Nat) (w : K) :=
  let u := cells w &&& only
  Indicator.mk w (rowSpread u) (colSpread u)

def contrary (a b : Indicator) :=
  a.wire != b.wire && (a.rows &&& b.rows) != 0 && (a.cols &&& b.cols) != 0

def simpleEdges : List Indicator → List (K×K)
  | [] => []
  | a::r => (r.filterMap (fun b => if contrary a b then some (a.wire,b.wire) else none))++simpleEdges r

def cheapPossible (xs : List K) :=
  let unique := Corners.exclusive xs
  let pairs := simpleEdges (xs.map (indicator unique))
  (compile pairs (seed xs)).any (fun ls => ground (bundle (blocks ls)) 0 0 false)

private theorem has_bit {m : Nat} (no : m≠0) : ∃i,m.testBit i=true := by
  by_contra fail
  apply no
  apply Nat.eq_of_testBit_eq
  intro i
  have zero : m.testBit i=false := Bool.eq_false_iff.mpr (fun hit => fail ⟨i,hit⟩)
  simp [zero]

private theorem grid_column : ∀i : Fin 56,columnMask.testBit i.val=true → ∃p : Fin 8,p.val*7=i.val := by
  decide +kernel

private theorem row_cell {u : Nat} {p : Fin 8} (hit : (rowSpread u).testBit (p.val*7)=true) :
    ∃n : Fin 7,u.testBit (p.val*7+n.val)=true := by
  simp only [rowSpread,Nat.testBit_and,Bool.and_eq_true] at hit
  have h := hit.1.1
  simp only [Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true] at h
  have from_bit (i) (yes : u.testBit i=true) (j : Fin 7) (eq : p.val*7+j.val=i) :
      ∃n : Fin 7,u.testBit (p.val*7+n.val)=true := ⟨j,by rwa [eq]⟩
  rcases h with ((h|h)|(h|h))|((h|h)|(h|h))
  · exact from_bit _ h ⟨0,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨1,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨2,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨3,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨3,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨4,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨5,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨6,by decide⟩ (by dsimp <;> omega)
private theorem col_cell {u : Nat} {n : Fin 7} (hit : (colSpread u).testBit n.val=true) :
    ∃p : Fin 8,u.testBit (p.val*7+n.val)=true := by
  simp only [colSpread,Nat.testBit_and,Bool.and_eq_true] at hit
  have h := hit.1
  simp only [Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true] at h
  have from_bit (i) (yes : u.testBit i=true) (j : Fin 8) (eq : j.val*7+n.val=i) :
      ∃p : Fin 8,u.testBit (p.val*7+n.val)=true := ⟨j,by rwa [eq]⟩
  rcases h with ((h|h)|(h|h))|((h|h)|(h|h))
  · exact from_bit _ h ⟨0,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨1,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨2,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨3,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨4,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨5,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨6,by decide⟩ (by dsimp <;> omega)
  · exact from_bit _ h ⟨7,by decide⟩ (by dsimp <;> omega)
private theorem meet_rows {u v : Nat} (h : rowSpread u &&& rowSpread v≠0) :
    ∃p : Fin 8,∃i j : Fin 7,u.testBit (p.val*7+i.val)=true ∧ v.testBit (p.val*7+j.val)=true := by
  obtain ⟨z,hit⟩ := has_bit h
  rw [Nat.testBit_and,Bool.and_eq_true] at hit
  have data := hit.1
  simp only [rowSpread,Nat.testBit_and,Bool.and_eq_true] at data
  have m : fullMask.testBit z=decide (z<56) := Nat.testBit_two_pow_sub_one 56 z
  have small : z<56 := by simpa only [m,decide_eq_true_eq] using data.2
  obtain ⟨p,eq⟩ := grid_column ⟨z,small⟩ data.1.2
  have eq' : p.val*7=z := eq
  obtain ⟨i,hi⟩ := row_cell (p:=p) (by simpa only [eq'] using hit.1)
  obtain ⟨j,hj⟩ := row_cell (p:=p) (by simpa only [eq'] using hit.2)
  exact ⟨p,i,j,hi,hj⟩

private theorem meet_cols {u v : Nat} (h : colSpread u &&& colSpread v≠0) :
    ∃n : Fin 7,∃i j : Fin 8,u.testBit (i.val*7+n.val)=true ∧ v.testBit (j.val*7+n.val)=true := by
  obtain ⟨z,hit⟩ := has_bit h
  rw [Nat.testBit_and,Bool.and_eq_true] at hit
  have data := hit.1
  simp only [colSpread,Nat.testBit_and,Bool.and_eq_true] at data
  have m : (127 : Nat).testBit z=decide (z<7) := Nat.testBit_two_pow_sub_one 7 z
  have small : z<7 := by simpa only [m,decide_eq_true_eq] using data.2
  let n : Fin 7 := ⟨z,small⟩
  obtain ⟨i,hi⟩ := col_cell (n:=n) hit.1
  obtain ⟨j,hj⟩ := col_cell (n:=n) hit.2
  exact ⟨n,i,j,hi,hj⟩

theorem contrary_opposite {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    {a b : K} (ha : a∈xs) (hb : b∈xs)
    (ok : contrary (indicator (Corners.exclusive xs) a) (indicator (Corners.exclusive xs) b)=true) :
    decide (a∈A)≠decide (b∈A) := by
  simp only [contrary,indicator,Bool.and_eq_true,bne_iff_ne] at ok
  obtain ⟨p,i,j,pi,pj⟩ := meet_rows ok.1.2
  obtain ⟨n,s,t,ns,nt⟩ := meet_cols ok.2
  let r : Rect := ⟨a,b,p,s,t,n,i,j⟩
  apply opposite dis good union same r
  change ((a != b) && forced xs p i a && forced xs s n a && forced xs p j b && forced xs t n b)=true
  simp only [Bool.and_eq_true,bne_iff_ne]
  exact ⟨⟨⟨⟨ok.1.1,Corners.owns ha _ _ pi⟩,Corners.owns ha _ _ ns⟩,Corners.owns hb _ _ pj⟩,Corners.owns hb _ _ nt⟩
theorem simpleEdges_valid {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    (items : List Indicator) (mk : ∀v∈items,∃x∈xs,v=indicator (Corners.exclusive xs) x)
    (e : K×K) (mem : e∈simpleEdges items) : decide (e.1∈A)≠decide (e.2∈A) := by
  induction items with
  | nil => simp [simpleEdges] at mem
  | cons a r ih =>
    rcases List.mem_append.mp mem with h|h
    · obtain ⟨b,hb,yes⟩ := List.mem_filterMap.mp h
      by_cases ok : contrary a b=true
      · have eq : (a.wire,b.wire)=e := by simpa [ok] using yes
        obtain ⟨x,hx,ex⟩ := mk a List.mem_cons_self
        obtain ⟨y,hy,ey⟩ := mk b (List.mem_cons_of_mem _ hb)
        rw [←eq,ex,ey]
        change decide (x∈A)≠decide (y∈A)
        exact contrary_opposite (a:=x) (b:=y) dis good union same hx hy (by simpa only [ex,ey] using ok)
      · simp [ok] at yes
    · exact ih (fun v hv => mk v (List.mem_cons_of_mem _ hv)) h

theorem cheap_yes {k : Nat} {xs : List K} (live : Live k 0 (xs.map wide).toFinset)
    (size : xs.toFinset.card=k) : cheapPossible xs=true := by
  have eq : (xs.map wide).toFinset=up xs.toFinset := by ext w; simp [up]
  have l : Live k 0 (up xs.toFinset) := by rw [←eq]; exact live
  obtain ⟨A,sub,na,good⟩ := tight_plus_one l size
  let B := xs.toFinset\A
  have union : A∪B=xs.toFinset := by
    ext x
    change x∈A∪(xs.toFinset\A) ↔ _
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro (ha|⟨hx,_⟩)
      · exact sub ha
      · exact hx
    · intro hx
      by_cases ha : x∈A
      · exact .inl ha
      · exact .inr ⟨hx,ha⟩
  have dis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  have cv : ∀p n,∃w∈A∪B,directed w p n=true := by
    intro p n
    rw [union]
    have cov : unionSep false (xs.map wide)=top := live_cover live rfl
    have bd : p.val*7+n.val<160 := by omega
    have yes : (unionSep false (xs.map wide)).getLsbD (p.val*7+n.val)=true := by
      rw [cov]; simp only [top,BitVec.getLsbD_allOnes,bd,decide_true]
    obtain ⟨w,hw,hy⟩ := (reports_one xs p n).mp yes
    exact ⟨w,List.mem_toFinset.mpr hw,hy⟩
  let c := fun x : K => decide (x∈A)
  let pairs := simpleEdges (xs.map (indicator (Corners.exclusive xs)))
  obtain ⟨ls,got,valid,words⟩ := compile_ok c pairs (seed xs) (seed_ok _ _) (fun e h =>
    simpleEdges_valid dis good cv union.symm _ (fun v hv => by
      obtain ⟨x,hx,ex⟩ := List.mem_map.mp hv
      exact ⟨x,hx,ex.symm⟩) e h)
  have covers (v : K) (h : v∈A∪B) : v∈pool (blocks ls) := by
    apply pack_all
    rw [words]
    simpa [seed,union] using h
  have left : A⊆([]++pool (blocks ls)).toFinset := fun _ hv =>
    List.mem_toFinset.mpr (covers _ (Finset.mem_union_left _ hv))
  have right : B⊆([]++pool (blocks ls)).toFinset := fun _ hv =>
    List.mem_toFinset.mpr (covers _ (Finset.mem_union_right _ hv))
  have ok := solve_ok na dis good.1 _ [] [] (bands_painted c valid) left right
  change (compile pairs (seed xs)).any _=true
  have g := bundle_eq (blocks ls) [] []
  change ground (bundle (blocks ls)) 0 0 false=solve (blocks ls) [] [] at g
  simpa only [got,Option.any_some,g] using ok

end CoNum4358.Tiny.ShareGrid.Forest

namespace CoNum4358.Tiny.Splice
open CoAO3143
open CoNum4358.WordRows
open ShareGrid.Forest (cheapPossible cheap_yes)

def bitPost (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false && (if k==0 then ws.any isGoal else
    !(Corners.limit k (ws.map Prod.fst) || matched T q ws ||
      (ws.length==k && !(cheapPossible (ws.map Prod.fst)))))

theorem bit_sound : MaskFast.SoundPost bitPost := by
  intro k q T ws val nd h
  have narrow : Live k 0 ((ws.map Prod.fst).map wide).toFinset := by
    have E : ((ws.map Prod.fst).map wide).toFinset=ws.toFinset.image (fun w=>wide w.1) := by ext; simp
    rw [E]; exact (good_of h).live
  have old := Corners.sound val nd h
  have ma := matched_false val h
  have li := Corners.limit_no nd narrow
  have sh : (ws.length==k && !(cheapPossible (ws.map Prod.fst)))=false := by
    apply Bool.eq_false_iff.mpr
    intro bad
    simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at bad
    have count : (ws.map Prod.fst).toFinset.card=k := by rw [List.toFinset_card_of_nodup nd,List.length_map,bad.1]
    exact Bool.false_ne_true (bad.2.symm.trans (cheap_yes narrow count))
  simpa only [Corners.post,bitPost,ma,li,sh,Bool.false_or] using old

def bitEntry (k i : Nat) :=
  let r := stored (k+1) i
  MaskFast.nodeWith bitPost k r.1 (bank (k+1) i k) r.2

theorem bit_layer {k : Nat} (prior : Layer k)
    (data : ∀i<(BicolorBase.tier (k+1)).total,orbitItem bitEntry k i=true) : Layer (k+1) := by
  apply orbit_complete _ data
  intro i ok
  exact MaskFast.nodeWith_ok bitPost bit_sound (T:=bank (k+1) i k) prior ok

def bitSegment (k g : Nat) (b : Fin 8) :=
  let i := (g*8+b.val)*16
  CoAO3143.Memo.allAt (orbitItem bitEntry k) i (min 16 ((BicolorBase.tier (k+1)).total-i))

theorem bitCollect {k} (prior : Layer k) (groups : Nat)
    (cover : (BicolorBase.tier (k+1)).total≤groups*8*16)
    (parts : ∀ a : Fin groups,∀ b : Fin 8,bitSegment k a.val b=true) :
    Layer (k+1) := by
  apply bit_layer prior
  intro i hi
  have row : i/16<groups*8 := by omega
  let a : Fin groups := ⟨i/16/8,by omega⟩
  let b : Fin 8 := ⟨i/16 % 8,Nat.mod_lt _ (by decide)⟩
  have place : a.val*8+b.val=i/16 := by dsimp [a,b]; omega
  have yes := parts a b
  unfold bitSegment at yes
  rw [place] at yes
  apply CoAO3143.Memo.allAt_get yes i (by omega)
  omega

end CoNum4358.Tiny.Splice

namespace CoNum4358.Tiny.Splice
open CoNum4358.WordRows
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem verified2 : Layer 2 := by intro i h; exact (Nat.not_lt_zero _ h).elim
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check3_0 (b : Fin 8) : bitSegment 2 0 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem verified3 : Layer 3 := by
  apply bitCollect verified2 1 (by decide +kernel)
  intro a b
  fin_cases a
  · exact check3_0 b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check4_0 (b : Fin 8) : bitSegment 3 0 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem verified4 : Layer 4 := by
  apply bitCollect verified3 1 (by decide +kernel)
  intro a b
  fin_cases a
  · exact check4_0 b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check5_0 (b : Fin 8) : bitSegment 4 0 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check5_1 (b : Fin 8) : bitSegment 4 1 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem verified5 : Layer 5 := by
  apply bitCollect verified4 2 (by decide +kernel)
  intro a b
  fin_cases a
  · exact check5_0 b
  · exact check5_1 b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check6_0 (b : Fin 8) : bitSegment 5 0 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check6_1 (b : Fin 8) : bitSegment 5 1 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check6_2 (b : Fin 8) : bitSegment 5 2 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check6_3 (b : Fin 8) : bitSegment 5 3 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem verified6 : Layer 6 := by
  apply bitCollect verified5 4 (by decide +kernel)
  intro a b
  fin_cases a
  · exact check6_0 b
  · exact check6_1 b
  · exact check6_2 b
  · exact check6_3 b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check7_0 (b : Fin 8) : bitSegment 6 0 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check7_1 (b : Fin 8) : bitSegment 6 1 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check7_2 (b : Fin 8) : bitSegment 6 2 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check7_3 (b : Fin 8) : bitSegment 6 3 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check7_4 (b : Fin 8) : bitSegment 6 4 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check7_5 (b : Fin 8) : bitSegment 6 5 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem verified7 : Layer 7 := by
  apply bitCollect verified6 6 (by decide +kernel)
  intro a b
  fin_cases a
  · exact check7_0 b
  · exact check7_1 b
  · exact check7_2 b
  · exact check7_3 b
  · exact check7_4 b
  · exact check7_5 b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check8_0 (b : Fin 8) : bitSegment 7 0 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check8_1 (b : Fin 8) : bitSegment 7 1 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check8_2 (b : Fin 8) : bitSegment 7 2 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check8_3 (b : Fin 8) : bitSegment 7 3 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check8_4 (b : Fin 8) : bitSegment 7 4 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check8_5 (b : Fin 8) : bitSegment 7 5 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check8_6 (b : Fin 8) : bitSegment 7 6 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem verified8 : Layer 8 := by
  apply bitCollect verified7 7 (by decide +kernel)
  intro a b
  fin_cases a
  · exact check8_0 b
  · exact check8_1 b
  · exact check8_2 b
  · exact check8_3 b
  · exact check8_4 b
  · exact check8_5 b
  · exact check8_6 b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check9_0 (b : Fin 8) : bitSegment 8 0 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check9_1 (b : Fin 8) : bitSegment 8 1 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check9_2 (b : Fin 8) : bitSegment 8 2 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check9_3 (b : Fin 8) : bitSegment 8 3 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem verified9 : Layer 9 := by
  apply bitCollect verified8 4 (by decide +kernel)
  intro a b
  fin_cases a
  · exact check9_0 b
  · exact check9_1 b
  · exact check9_2 b
  · exact check9_3 b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check10_0 (b : Fin 8) : bitSegment 9 0 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem verified10 : Layer 10 := by
  apply bitCollect verified9 1 (by decide +kernel)
  intro a b
  fin_cases a
  · exact check10_0 b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem check11_0 (b : Fin 8) : bitSegment 10 0 b=true := by fin_cases b <;> decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem verified11 : Layer 11 := by
  apply bitCollect verified10 1 (by decide +kernel)
  intro a b
  fin_cases a
  · exact check11_0 b
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem no_tiny : ¬ Trace 11 1 roots.toFinset := by
  have no := verified11 0 (by decide +kernel)
  have q : (stored 11 0).1=1 := by decide +kernel
  have same : (stored 11 0).2.toFinset=roots.toFinset := by decide +kernel
  simpa only [q,same] using no
end CoNum4358.Tiny.Splice

end PEqualNP.Outside.L_meta_4358_aux

open PEqualNP.Outside.L_meta_4358_aux

theorem PEqualNP.Outside.L_meta_4358 : have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (6 : ℕ) → Bool) → List Bool := fun (x2 : Fin (6 : ℕ) → Bool) => [x2 (0 : Fin (6 : ℕ)), x2 (1 : Fin (6 : ℕ)), Bool.false, x2 (2 : Fin (6 : ℕ)), x2 (3 : Fin (6 : ℕ)), x2 (4 : Fin (6 : ℕ)), x2 (5 : Fin (6 : ℕ))]; ∀ (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x3 →     (have x8 : Fin (11 : ℕ) → (Fin (6 : ℕ) → Bool) → Bool := fun (x8 : Fin (11 : ℕ)) (x9 : Fin (6 : ℕ) → Bool) => (x3.wires (x2 x9)).getD ((7 : ℕ) + ↑x8) Bool.false;       ∃ (x9 : Fin (8 : ℕ) → Fin (11 : ℕ)), (∀ (x10 x11 : Fin (8 : ℕ)), x10 ≠ x11 → ∃ (x13 : Fin (6 : ℕ) → Bool), x8 (x9 x10) x13 ≠ x8 (x9 x11) x13) ∧ ∀ (x10 x11 : Fin (8 : ℕ)), ∃ (x12 : Fin (6 : ℕ) → Bool), x8 (x9 x10) x12 ≠ (Bool.false :: Bool.true :: List.ofFn x12).getD (↑x11) Bool.false) →       x3.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x3 = x1 → List.Forall₂ (fun (x11 x12 : PEqualNP.CircuitLowerBounds.Gate) => x11.op = x12.op ∧ List.Forall₂ (fun (x13 x14 : ℕ) => x14 = x13 + (1 : ℕ) ∨ x14 = (0 : ℕ) ∧ (x13 = x5 ∨ x13 = x6)) x11.inputs x12.inputs) x3.gates x4.gates → (∀ (x12 : Fin (7 : ℕ) → Bool), (x4.wires (Bool.true :: List.ofFn x12)).getD (x3.output + (1 : ℕ)) Bool.false = (x1 x12 || x12 (0 : Fin (7 : ℕ)) || x12 (3 : Fin (7 : ℕ)))) → (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false] && x13.inputs.contains (2 : ℕ)) x3.gates).length ≥ (2 : ℕ) := by
  dsimp only
  intro C D a b fan _ size computes links promote
  exact CoNum4358.exclusion CoThetaSeven.checked_lower
    (fun h => CoNum4358.Tiny.Splice.no_tiny (CoNum4358.Tiny.shadow_to_tiny (CoNum4358.shadow_root h))) C D a b fan size computes links promote
