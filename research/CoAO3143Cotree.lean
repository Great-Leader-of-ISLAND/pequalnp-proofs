import PEqualNP.CoAO3143Protocol

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

/-- With exactly enough binary gates to merge the frontier down to one,
    no branch can share an operand. The target is a read-once formula on
    the current signals. -/
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

private theorem bit_op (d s : Bool) (i : Row) (a b : Sig) :
    bit s i (bin d a b) = if d then bit s i a || bit s i b else bit s i a && bit s i b := by
  cases s <;> cases d <;> simp [bit,bin,BitVec.getLsbD_and,BitVec.getLsbD_or]

theorem answer_valid (p n : Row) (t : ReadTree) (h : separates p n t.value) :
    separates p n (answer p n t) := by
  induction t with
  | atom a => exact h
  | fork d l r ih jh =>
    rcases h with ⟨hp,hn⟩
    change bit true p (bin d l.value r.value)=true at hp
    change bit false n (bin d l.value r.value)=false at hn
    rw [bit_op] at hp hn
    cases d <;> cases pl : bit true p l.value <;> cases nl : bit false n l.value <;>
      simp only [answer,leftChoice,Bool.false_eq_true, ↓reduceIte,pl,nl,Bool.not_false,Bool.not_true] <;>
      first | exact ih (by simp_all [separates]) | exact jh (by simp_all [separates])

/-- Two coordinates on opposing sides give two equivalence relations on labels. -/
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

/-- The first read-once split separating the selected leaves must disconnect
    the graph of shared positive rows or the graph of shared negative rows. -/
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
