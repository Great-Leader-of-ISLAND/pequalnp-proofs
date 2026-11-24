import Mathlib

/- Independent representatives for any finite list of large palettes in a
four-cycle-free simple graph. Different palettes may use the same vertex. -/
namespace Co5326Transversal

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def FourFree : Prop := ∀ (p q : V), p ≠ q → ∀ (B : Finset V),
    (B.filter fun x => G.Adj p x ∧ G.Adj q x).card ≤ 1

def safe (p : V) (B : Finset V) : Finset V := B.filter fun x => ¬G.Adj p x

def bad (k : Nat) (A B : Finset V) : Finset V := A.filter fun a => (safe G a B).card < k

theorem bad_card (H : FourFree G) {k : Nat} (A B : Finset V) (big : 2*k ≤ B.card) :
    (bad G k A B).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra ne
  have sp := (Finset.mem_filter.mp hp).2
  have sq := (Finset.mem_filter.mp hq).2
  let common := B.filter fun x => G.Adj p x ∧ G.Adj q x
  have low : common.card ≤ 1 := H p q ne B
  have cover : B ⊆ (safe G p B ∪ safe G q B) ∪ common := by
    intro x hx
    by_cases pa : G.Adj p x
    · by_cases qa : G.Adj q x
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,pa,qa⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,qa⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,pa⟩))
  have upper := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have pair := Finset.card_union_le (safe G p B) (safe G q B)
  change (safe G p B).card < k at sp
  change (safe G q B).card < k at sq
  omega

def bads (k : Nat) (A : Finset V) (bs : List (Finset V)) : Finset V :=
  bs.foldr (fun B rest => bad G k A B ∪ rest) ∅

private theorem bads_card (H : FourFree G) (k : Nat) (A : Finset V) (bs : List (Finset V))
    (big : ∀ B∈bs, 2*k ≤ B.card) : (bads G k A bs).card ≤ bs.length := by
  induction bs with
  | nil => simp [bads]
  | cons B bs ih =>
    have hb := bad_card G H A B (big B List.mem_cons_self)
    have hr := ih (fun D h => big D (List.mem_cons_of_mem _ h))
    have hu := Finset.card_union_le (bad G k A B) (bads G k A bs)
    change (bad G k A B ∪ bads G k A bs).card ≤ bs.length+1
    omega

private theorem of_bad {k : Nat} {a : V} {A B : Finset V} (bs : List (Finset V))
    (hB : B∈bs) (ha : a∈bad G k A B) : a∈bads G k A bs := by
  induction bs with
  | nil => simp at hB
  | cons D ds ih =>
    rcases List.mem_cons.mp hB with eq | hm
    · subst D; exact Finset.mem_union_left _ ha
    · exact Finset.mem_union_right _ (ih hm)

theorem pick (H : FourFree G) (k : Nat) (A : Finset V) (bs : List (Finset V))
    (room : bs.length < A.card) (big : ∀ B∈bs, 2*k ≤ B.card) :
    ∃ a∈A, ∀ B∈bs, k ≤ (safe G a B).card := by
  have notSub : ¬ A ⊆ bads G k A bs := by
    intro hyp
    have h := (Finset.card_le_card hyp).trans (bads_card G H k A bs big)
    omega
  obtain ⟨a,ha,hnot⟩ : ∃ a∈A, a∉bads G k A bs := by
    by_contra! h
    exact notSub h
  refine ⟨a,ha,?_⟩
  intro B hB
  by_contra! small
  exact hnot (of_bad G bs hB (Finset.mem_filter.mpr ⟨ha,small⟩))

/-- An independent selection meeting the palettes and containing only supplied vertices. -/
def Selection (bs : List (Finset V)) : Prop := ∃ S : Finset V,
    (∀ x∈S, ∀ y∈S, ¬G.Adj x y) ∧
    (∀ B∈bs, ∃ x∈S, x∈B) ∧ (∀ x∈S, ∃ B∈bs, x∈B)

private theorem extend {bs : List (Finset V)} {A : Finset V} {a : V} (ha : a∈A)
    (sel : Selection G (bs.map (safe G a))) : Selection G (A::bs) := by
  obtain ⟨S,ind,hit,used⟩ := sel
  have quiet {x} (hx : x∈S) : ¬G.Adj a x := by
    obtain ⟨B,hB,hxB⟩ := used x hx
    obtain ⟨B,_,rfl⟩ := List.mem_map.mp hB
    exact (Finset.mem_filter.mp hxB).2
  refine ⟨insert a S,?_,?_,?_⟩
  · intro x hx y hy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact G.loopless.irrefl _
      · exact quiet hy
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact fun edge => quiet hx (G.symm edge)
      · exact ind x hx y hy
  · intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact ⟨a,Finset.mem_insert_self _ _,ha⟩
    · obtain ⟨x,hx,hxB⟩ := hit (safe G a B) (List.mem_map_of_mem hB)
      exact ⟨x,Finset.mem_insert_of_mem hx,(Finset.mem_filter.mp hxB).1⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨A,List.mem_cons_self,ha⟩
    · obtain ⟨B,hB,hxB⟩ := used x hx
      obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hB
      exact ⟨B,List.mem_cons_of_mem _ hB,(Finset.mem_filter.mp hxB).1⟩

private theorem linear_le_pow (r : Nat) : r+1 ≤ 2^r := by
  induction r with
  | zero => decide
  | succ r ih => rw [pow_succ]; omega

theorem transversal (H : FourFree G) (r : Nat) (A : Finset V) (bs : List (Finset V))
    (len : bs.length=r) (room : 2^r ≤ A.card) (big : ∀ B∈bs, 2^r ≤ B.card) :
    Selection G (A::bs) := by
  induction r generalizing A bs with
  | zero =>
    cases bs with
    | cons B bs => simp at len
    | nil =>
      obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<A.card by simpa only [pow_zero] using room)
      apply extend G ha
      exact ⟨∅,by simp,by simp,by simp⟩
  | succ r ih =>
    have many : bs.length < A.card := by
      have h := linear_le_pow (r+1)
      omega
    have bounds : ∀ B∈bs, 2*(2^r) ≤ B.card := by
      intro B hb
      simpa [pow_succ,Nat.mul_comm] using big B hb
    obtain ⟨a,ha,keep⟩ := pick G H (2^r) A bs many bounds
    apply extend G ha
    cases bs with
    | nil => simp at len
    | cons B bs =>
      apply ih (safe G a B) (bs.map (safe G a)) (by simpa using len) (keep _ List.mem_cons_self)
      intro C hC
      obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hC
      exact keep D (List.mem_cons_of_mem _ hD)

#print axioms transversal
end Co5326Transversal
