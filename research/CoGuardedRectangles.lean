import Mathlib

namespace CoGuardedRectangles

structure Test (α : Type*) where
  holds : Set α → Prop
  up : ∀ {U V : Set α}, U ⊆ V → holds U → holds V

inductive Block (α β : Type*) where
  | leaf (P : Test α) (L : Test β)
  | join (a b : Block α β)
  | meet (a b : Block α β)
  | point (P : Test α) (a : Block α β)
  | line (L : Test β) (a : Block α β)

inductive RectTerm (α β : Type*) where
  | rect (P : Set α) (L : Set β)
  | join (a b : RectTerm α β)
  | meet (a b : RectTerm α β)

def Block.eval {α β : Type*} (X : Set α) (Y : Set β) : Block α β → Prop
  | .leaf P L => P.holds X ∧ L.holds Y
  | .join a b => a.eval X Y ∨ b.eval X Y
  | .meet a b => a.eval X Y ∧ b.eval X Y
  | .point P a => P.holds X ∧ a.eval X Y
  | .line L a => L.holds Y ∧ a.eval X Y

def RectTerm.eval {α β : Type*} (X : Set α) (Y : Set β) : RectTerm α β → Prop
  | .rect P L => (∃ p ∈ X, p ∈ P) ∧ (∃ l ∈ Y, l ∈ L)
  | .join a b => a.eval X Y ∨ b.eval X Y
  | .meet a b => a.eval X Y ∧ b.eval X Y

def Block.compile {α β : Type*} (A : Set α) (B : Set β) : Block α β → RectTerm α β
  | .leaf P L => .rect {p | p ∈ A ∧ P.holds {p}} {l | l ∈ B ∧ L.holds {l}}
  | .join a b => .join (a.compile A B) (b.compile A B)
  | .meet a b => .meet (a.compile A B) (b.compile A B)
  | .point P a => a.compile {p | p ∈ A ∧ P.holds {p}} B
  | .line L a => a.compile A {l | l ∈ B ∧ L.holds {l}}

theorem compile_sound {α β : Type*} (b : Block α β) (X : Set α) (Y : Set β) :
    ∀ A B, (b.compile A B).eval X Y →
      b.eval X Y ∧ (∃ p ∈ X, p ∈ A) ∧ (∃ l ∈ Y, l ∈ B) := by
  induction b with
  | leaf P L =>
    rintro A B ⟨⟨p,hp,ha,hP⟩,l,hl,hb,hL⟩
    exact ⟨⟨P.up (Set.singleton_subset_iff.mpr hp) hP,
      L.up (Set.singleton_subset_iff.mpr hl) hL⟩,⟨p,hp,ha⟩,⟨l,hl,hb⟩⟩
  | join a b ia ib =>
    rintro A B (h|h)
    · obtain ⟨h,x,y⟩ := ia A B h
      exact ⟨Or.inl h,x,y⟩
    · obtain ⟨h,x,y⟩ := ib A B h
      exact ⟨Or.inr h,x,y⟩
  | meet a b ia ib =>
    rintro A B ⟨ha,hb⟩
    obtain ⟨h,x,y⟩ := ia A B ha
    exact ⟨⟨h,(ib A B hb).1⟩,x,y⟩
  | point P a ih =>
    intro A B h
    obtain ⟨h,⟨p,hp,ha,hP⟩,y⟩ := ih {p | p ∈ A ∧ P.holds {p}} B h
    exact ⟨⟨P.up (Set.singleton_subset_iff.mpr hp) hP,h⟩,⟨p,hp,ha⟩,y⟩
  | line L a ih =>
    intro A B h
    obtain ⟨h,x,⟨l,hl,hb,hL⟩⟩ := ih A {l | l ∈ B ∧ L.holds {l}} h
    exact ⟨⟨L.up (Set.singleton_subset_iff.mpr hl) hL,h⟩,x,⟨l,hl,hb⟩⟩

theorem compile_pair {α β : Type*} (b : Block α β) (p : α) (l : β) :
    ∀ A B, (b.compile A B).eval {p} {l} ↔ p ∈ A ∧ l ∈ B ∧ b.eval {p} {l} := by
  induction b with
  | leaf P L => intro A B; simp [Block.compile,RectTerm.eval,Block.eval] <;> tauto
  | join a b ia ib =>
    intro A B; simp only [Block.compile,RectTerm.eval,Block.eval,ia,ib]; tauto
  | meet a b ia ib =>
    intro A B; simp only [Block.compile,RectTerm.eval,Block.eval,ia,ib]; tauto
  | point P a ih =>
    intro A B; simp only [Block.compile,Block.eval,ih,Set.mem_setOf_eq]; tauto
  | line L a ih =>
    intro A B; simp only [Block.compile,Block.eval,ih,Set.mem_setOf_eq]; tauto

def RectTerm.depth {α β : Type*} : RectTerm α β → ℕ
  | .rect _ _ => 0
  | .join a b => max a.depth b.depth
  | .meet a b => (max a.depth b.depth)+1

/-- A rectangle reads the point and line once each. A join chooses a child.
An intersection joins both proofs and therefore adds their joint counts. -/
inductive PairReads {α β : Type*} (p : α) (l : β) : RectTerm α β → ℕ → Prop where
  | rect {A : Set α} {B : Set β} : p ∈ A → l ∈ B → PairReads p l (.rect A B) 1
  | left {a b k} : PairReads p l a k → PairReads p l (.join a b) k
  | right {a b k} : PairReads p l b k → PairReads p l (.join a b) k
  | both {a b i j} : PairReads p l a i → PairReads p l b j → PairReads p l (.meet a b) (i+j)

theorem pair_witness {α β : Type*} (t : RectTerm α β) (p : α) (l : β)
    (h : t.eval {p} {l}) : ∃ k ≤ 2^t.depth, PairReads p l t k := by
  induction t with
  | rect A B =>
    have hh : p ∈ A ∧ l ∈ B := by simpa [RectTerm.eval] using h
    exact ⟨1,by decide,.rect hh.1 hh.2⟩
  | join a b ia ib =>
    rcases h with h|h
    · obtain ⟨i,hi,w⟩ := ia h
      exact ⟨i,hi.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left _ _)),.left w⟩
    · obtain ⟨i,hi,w⟩ := ib h
      exact ⟨i,hi.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right _ _)),.right w⟩
  | meet a b ia ib =>
    obtain ⟨i,hi,u⟩ := ia h.1
    obtain ⟨j,hj,v⟩ := ib h.2
    have ha := hi.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left a.depth b.depth))
    have hb := hj.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right a.depth b.depth))
    refine ⟨i+j,?_,.both u v⟩
    simp only [RectTerm.depth,pow_succ]
    omega

end CoGuardedRectangles
