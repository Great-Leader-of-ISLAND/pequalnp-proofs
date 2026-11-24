import Init

namespace CoRow3241

abbrev Mask (α : Type) := α → Prop

def Covered {α : Type} (s x : Mask α) : Prop := ∃ a, s a ∧ x a

def Up {α : Type} (f : Mask α → Prop) : Prop :=
  ∀ {x y : Mask α}, (∀ a, x a → y a) → f x → f y

theorem exact_operand {α : Type} (n : Mask α) (f g : Mask α → Prop)
    (uf : Up f) (ug : Up g)
    (exactly : ∀ x, (f x ∧ g x) ↔ Covered n x) :
    (∀ x, f x ↔ Covered n x) ∨ (∀ x, g x ↔ Covered n x) := by
  classical
  let q : Mask α := fun a => ¬ n a
  have no : ¬(f q ∧ g q) := by
    intro both
    obtain ⟨a,ha,hn⟩ := (exactly q).mp both
    exact hn ha
  have clean (h : Mask α → Prop) (uh : Up h) (reject : ¬h q)
      (positive : ∀ x, Covered n x → h x) : ∀ x, h x ↔ Covered n x := by
    intro x
    refine ⟨?_,positive x⟩
    intro hx
    apply Classical.byContradiction
    intro absent
    apply reject (uh (fun a hxa hna => absent ⟨a,hna,hxa⟩) hx)
  by_cases hf : f q
  · exact Or.inr (clean g ug (fun hg => no ⟨hf,hg⟩) (fun x good => ((exactly x).mpr good).2))
  · exact Or.inl (clean f uf hf (fun x good => ((exactly x).mpr good).1))

inductive Expr (α : Type) where
  | input (a : α)
  | const (b : Bool)
  | join (u v : Expr α)
  | meet (u v : Expr α)

def eval {α : Type} (x : Mask α) : Expr α → Prop
  | .input a => x a
  | .const b => b = true
  | .join u v => eval x u ∨ eval x v
  | .meet u v => eval x u ∧ eval x v

noncomputable def marked {α : Type} (q : Mask α) : Expr α → Mask α
  | .input a => fun b => b=a
  | .const _ => fun _ => False
  | .join u v => fun b => marked q u b ∨ marked q v b
  | .meet u v => by
    classical
    exact if eval q u then marked q v else marked q u

theorem prune {α : Type} (q : Mask α) (t : Expr α) (off : ¬ eval q t) :
    (∀ a, marked q t a → ¬q a) ∧ (∀ x, eval x t → Covered (marked q t) x) := by
  classical
  induction t with
  | input a =>
    exact ⟨fun b e => e ▸ off,fun x hx => ⟨a,rfl,hx⟩⟩
  | const b => exact ⟨fun _ h => h.elim,fun _ h => (off h).elim⟩
  | join u v hu hv =>
    have a := hu (fun h => off (Or.inl h))
    have b := hv (fun h => off (Or.inr h))
    refine ⟨fun i h => h.elim (a.1 i) (b.1 i),?_⟩
    intro x h
    cases h with
    | inl l =>
      obtain ⟨i,hi,hx⟩ := a.2 x l
      exact ⟨i,Or.inl hi,hx⟩
    | inr r =>
      obtain ⟨i,hi,hx⟩ := b.2 x r
      exact ⟨i,Or.inr hi,hx⟩
  | meet u v hu hv =>
    by_cases hit : eval q u
    · have a := hv (fun h => off ⟨hit,h⟩)
      simp only [marked,if_pos hit]
      exact ⟨a.1,fun x h => a.2 x h.2⟩
    · have a := hu hit
      simp only [marked,if_neg hit]
      exact ⟨a.1,fun x h => a.2 x h.1⟩

theorem row_support {α : Type} (n : Mask α) (t : Expr α)
    (exactly : ∀ x, eval x t ↔ Covered n x) :
    ∀ a, marked (fun i => ¬n i) t a ↔ n a := by
  classical
  let q : Mask α := fun i => ¬n i
  have off : ¬eval q t := fun h => by
    obtain ⟨a,ha,hn⟩ := (exactly q).mp h
    exact hn ha
  have h := prune q t off
  intro a
  refine ⟨fun ha => Classical.not_not.mp (h.1 a ha),?_⟩
  intro hn
  obtain ⟨b,hb,e⟩ := h.2 (fun b => b=a) ((exactly _).mpr ⟨a,hn,rfl⟩)
  exact e ▸ hb

#print axioms CoRow3241.row_support
#print axioms CoRow3241.exact_operand
end CoRow3241
