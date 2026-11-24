import PEqualNP.CoNine3024Cotree

namespace CoBankProof3004
open CoNine3024Cotree CoAO3143Restriction
abbrev R := Fin 14
abbrev J := Fin 8

def rawList : List Nat :=
  [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,
   14003410187812864,55389823207997440,189297016294081033,155696362464477250,
   218994303132270608,183565875465490436,229736628138025984,270286071508633728,
   288160007407550752]
def val (z : Nat) : Wire Nat := z.testBit
def raw (j : R) : Wire Nat := val (rawList.getD j.val 0)

structure Cert where
  labels : J → R
  pos : J → Nat
  neg : J → Nat
  a : J
  b : J
  p : Nat
  n₁ : Nat
  n₂ : Nat
  p₁ : Nat
  p₂ : Nat
  n : Nat

def Own (c : Cert) (p n : Nat) (a : J) : Prop :=
  ∀ j : J, sep p n (raw (c.labels j)) → j=a

def Check (z : Nat) (c : Cert) : Prop :=
  (∀ i j : J, c.labels i = c.labels j → i = j) ∧ c.a ≠ c.b ∧
  (∀ i : J, sep (c.pos i) (c.neg i) (val z) ∧
      sep (c.pos i) (c.neg i) (raw (c.labels i)) ∧
      ∀ j : R, sep (c.pos i) (c.neg i) (raw j) → j=c.labels i) ∧
  sep c.p c.n₁ (val z) ∧ sep c.p c.n₂ (val z) ∧
  sep c.p₁ c.n (val z) ∧ sep c.p₂ c.n (val z) ∧
  Own c c.p c.n₁ c.a ∧ Own c c.p c.n₂ c.b ∧ Own c c.p₁ c.n c.a ∧ Own c c.p₂ c.n c.b

instance (z : Nat) (c : Cert) : Decidable (Check z c) := by unfold Check Own sep; infer_instance

structure Nine where
  pos : Fin 9 → Nat
  neg : Fin 9 → Nat

def CheckNine (z : Nat) (t : Nine) : Prop :=
  (∀ i, sep (t.pos i) (t.neg i) (val z)) ∧
  (∀ i j, i ≠ j → ∀ v : R, sep (t.pos i) (t.neg i) (raw v) →
    sep (t.pos j) (t.neg j) (raw v) → False)

instance (z : Nat) (t : Nine) : Decidable (CheckNine z t) := by unfold CheckNine sep; infer_instance

noncomputable section
local instance : DecidableEq (Wire Nat) := Classical.decEq _

private theorem width {out : Wire Nat} {k S} (c : Cone out k S) : S.card ≤ k+1 := by
  induction c with
  | stop => simp
  | @gate k U d a b fresh tail ih =>
    rw [Finset.card_insert_of_notMem fresh] at ih
    have x := Finset.card_insert_le a (insert b U)
    have y := Finset.card_insert_le b U
    omega

private theorem cut_sep {out : Wire Nat} {k S} (c : Cone out k S) {p n}
    (test : sep p n out) : ∃ u ∈ S, sep p n u := by
  induction c with
  | stop => exact ⟨_,Finset.mem_singleton_self _,test⟩
  | @gate k U d a b fresh tail ih =>
    obtain ⟨u,hu,vs⟩ := ih
    rcases Finset.mem_insert.mp hu with eq|hu
    · subst u
      refine ⟨pick d a b p n,?_,pick_sep d a b p n vs⟩
      rcases pick_mem d a b p n with e|e <;> simp [e]
    · exact ⟨u,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),vs⟩

/-- The check excludes even a shared binary cone of at most seven nodes. -/
theorem excluded {z : Nat} (c : Cert) (ck : Check z c) {k S} (run : Cone (val z) k S)
    (cap : k≤7) (ground : ∀ w∈S, ∃ j : R, w=raw j) : False := by
  obtain ⟨distinct,ab,ess,s₁,s₂,s₃,s₄,o₁,o₂,o₃,o₄⟩ := ck
  let label := fun i => raw (c.labels i)
  have inj : Function.Injective label := by
    intro i j eq
    obtain ⟨_,sepI,only⟩ := ess i
    have same : sep (c.pos i) (c.neg i) (label j) := eq ▸ sepI
    exact distinct i j (only _ same).symm
  have inside (i : J) : label i ∈ S := by
    obtain ⟨yes,_,only⟩ := ess i
    obtain ⟨w,hw,separator⟩ := cut_sep run yes
    obtain ⟨j,rfl⟩ := ground w hw
    have hj := only j separator
    simpa only [label,← hj] using hw
  let A := Finset.univ.image label
  have sub : A ⊆ S := by intro w hw; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw; exact inside i
  have size : A.card=8 := by simp [A,Finset.card_image_of_injective _ inj]
  have upper := width run
  have low := Finset.card_le_card sub
  have eq : S=A := (Finset.eq_of_subset_of_card_le sub (by omega)).symm
  have tight : S.card=k+1 := by omega
  have own {p n a} (o : Own c p n a) : Forced S p n (label a) := by
    intro w hw diff
    rw [eq] at hw
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
    exact congrArg label (o j diff)
  exact ab (inj (forced_pair run tight s₁ s₂ s₃ s₄ (own o₁) (own o₂) (own o₃) (own o₄)))

theorem nine_excluded {z : Nat} (t : Nine) (ck : CheckNine z t) {k S} (run : Cone (val z) k S)
    (cap : k≤7) (ground : ∀ w∈S, ∃ j : R, w=raw j) : False := by
  have get (i : Fin 9) := cut_sep run (ck.1 i)
  choose f member separates using get
  let embed (i : Fin 9) : ↥S := ⟨f i,member i⟩
  have inj : Function.Injective embed := by
    intro i j h
    by_contra ne
    have same : f i = f j := congrArg Subtype.val h
    obtain ⟨v,hv⟩ := ground _ (member i)
    have a : sep (t.pos i) (t.neg i) (raw v) := by rw [← hv]; exact separates i
    have b : sep (t.pos j) (t.neg j) (raw v) := by rw [← hv,same]; exact separates j
    exact ck.2 i j ne v a b
  have big : 9 ≤ S.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective embed inj
  have bound := width run
  omega

end

def make (labels ps ns : List Nat) (a b p n₁ n₂ p₁ p₂ n : Nat) : Cert :=
  { labels := fun i => ⟨(labels.getD i.val 0)%14, by omega⟩
    pos := fun i => ps.getD i.val 0
    neg := fun i => ns.getD i.val 0
    a := ⟨a%8,by omega⟩
    b := ⟨b%8,by omega⟩
    p := p, n₁ := n₁, n₂ := n₂, p₁ := p₁, p₂ := p₂, n := n }

def nine (ps ns : List Nat) : Nine := ⟨fun i => ps.getD i.val 0,fun i => ns.getD i.val 0⟩

#print axioms nine_excluded
#print axioms excluded
end CoBankProof3004
