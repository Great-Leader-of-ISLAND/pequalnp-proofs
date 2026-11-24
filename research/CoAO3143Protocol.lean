import PEqualNP.CoAO3143Bridge

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
      refine ⟨?_,child_valid (e ▸ (sound p n).2)⟩
      rcases child_mem d a b p n with l | r
      · simp [l]
      · simp [r]
    · rw [show new p n = old p n by simp [new,e]]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (other p n e)),(sound p n).2⟩

private theorem width {k t S} (h : Live k t S) : S.card+t ≤ k+1 := by
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
    · simp [bit,target,top,BitVec.getLsbD_allOnes]
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

/-- Two distinct forced separators cannot both be forced at the two off-corner
    pairs of rectangles sharing (p,n), whenever the width budget is tight. -/
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
