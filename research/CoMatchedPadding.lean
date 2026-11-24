import Mathlib

namespace CoMatchedPadding

abbrev Tag := Fin 7

def extra : Finset (Tag × Tag) :=
  {(1,1),(1,2),(2,2),(2,3),(3,3),(3,1),
   (4,4),(4,5),(5,5),(5,6),(6,6),(6,4), (0,1),(4,0)}

def allowed (s t : Tag) : Prop := (s,t) ∈ extra ∨ (s=0 ∧ t=0)
instance (s t : Tag) : Decidable (allowed s t) := by unfold allowed; infer_instance

theorem template_data :
    extra.card = 14 ∧ (0,0) ∉ extra ∧
    (∀ s : Tag, s≠0 → (s,s) ∈ extra) ∧
    (∀ s : Tag, s≠0 → ∃ t u : Tag, t≠u ∧ (s,t)∈extra ∧ (s,u)∈extra) ∧
    (∀ t : Tag, t≠0 → ∃ s u : Tag, s≠u ∧ (s,t)∈extra ∧ (u,t)∈extra) ∧
    (∀ s t u v : Tag, allowed s u → allowed s v → allowed t u → allowed t v → s=t ∨ u=v) := by
  decide +kernel

def join {α : Type*} (I : α → α → Prop) (a b : Tag × α) : Prop :=
  (a.1 = 0 ∧ b.1 = 0 ∧ I a.2 b.2) ∨ (a.2 = b.2 ∧ (a.1,b.1) ∈ extra)

theorem tag_of_edge {α : Type*} {I : α → α → Prop} {a b} (h : join I a b) : allowed a.1 b.1 := by
  rcases h with h|h
  · exact Or.inr ⟨h.1,h.2.1⟩
  · exact Or.inl h.2

theorem label_of_edge {α : Type*} {I : α → α → Prop} {a b} (h : join I a b)
    (hn : ¬(a.1=0 ∧ b.1=0)) : a.2=b.2 := by
  rcases h with h|h
  · exact False.elim (hn ⟨h.1,h.2.1⟩)
  · exact h.1

theorem old_of_edge {α : Type*} {I : α → α → Prop} {a b} (h : join I a b)
    (ha : a.1=0) (hb : b.1=0) : I a.2 b.2 := by
  rcases h with h|h
  · exact h.2.2
  · exact False.elim (template_data.2.1 (by simpa [ha,hb] using h.2))

theorem equal_left_tags {α : Type*} {I : α → α → Prop} {a b c : Tag × α}
    (ne : a≠b) (eq : a.1=b.1) (ac : join I a c) (bc : join I b c) : a.1=0 ∧ c.1=0 := by
  by_contra hn
  have hn' : ¬(b.1=0 ∧ c.1=0) := by simpa [←eq] using hn
  exact ne (Prod.ext eq ((label_of_edge ac hn).trans (label_of_edge bc hn').symm))

theorem equal_right_tags {α : Type*} {I : α → α → Prop} {a c d : Tag × α}
    (ne : c≠d) (eq : c.1=d.1) (ac : join I a c) (ad : join I a d) : a.1=0 ∧ c.1=0 := by
  by_contra hn
  have hn' : ¬(a.1=0 ∧ d.1=0) := by simpa [←eq] using hn
  exact ne (Prod.ext eq ((label_of_edge ac hn).symm.trans (label_of_edge ad hn')))

theorem no_four {α : Type*} (I : α → α → Prop)
    (old : ∀ i k j l, I i j → I i l → I k j → I k l → i=k ∨ j=l)
    {a b c d : Tag × α} (ac : join I a c) (ad : join I a d)
    (bc : join I b c) (bd : join I b d) : a=b ∨ c=d := by
  by_contra! hn
  have abcd := template_data.2.2.2.2.2 _ _ _ _ (tag_of_edge ac) (tag_of_edge ad)
    (tag_of_edge bc) (tag_of_edge bd)
  have z : a.1=0 ∧ b.1=0 ∧ c.1=0 ∧ d.1=0 := by
    rcases abcd with eq|eq
    · have l := equal_left_tags hn.1 eq ac bc
      have r := equal_left_tags hn.1 eq ad bd
      exact ⟨l.1,eq.symm.trans l.1,l.2,r.2⟩
    · have l := equal_right_tags hn.2 eq ac ad
      have r := equal_right_tags hn.2 eq bc bd
      exact ⟨l.1,r.1,l.2,eq.symm.trans l.2⟩
  rcases old _ _ _ _ (old_of_edge ac z.1 z.2.2.1) (old_of_edge ad z.1 z.2.2.2)
      (old_of_edge bc z.2.1 z.2.2.1) (old_of_edge bd z.2.1 z.2.2.2) with eq|eq
  · exact hn.1 (Prod.ext (z.1.trans z.2.1.symm) eq)
  · exact hn.2 (Prod.ext (z.2.2.1.trans z.2.2.2.symm) eq)

def matching {α : Type*} (π : Equiv.Perm α) : Equiv.Perm (Tag × α) where
  toFun a := (a.1, if a.1=0 then π a.2 else a.2)
  invFun a := (a.1, if a.1=0 then π.symm a.2 else a.2)
  left_inv := by rintro ⟨s,i⟩; by_cases h:s=0 <;> simp [h]
  right_inv := by rintro ⟨s,i⟩; by_cases h:s=0 <;> simp [h]

theorem match_edge {α : Type*} (I : α → α → Prop) (π : Equiv.Perm α)
    (hm : ∀ i, I i (π i)) (a : Tag × α) : join I a (matching π a) := by
  obtain ⟨s,i⟩ := a
  by_cases h : s=0
  · exact Or.inl ⟨h,h,by simpa [matching,h] using hm i⟩
  · exact Or.inr ⟨by simp [matching,h],template_data.2.2.1 s h⟩

theorem min_two {α : Type*} (I : α → α → Prop) (π : Equiv.Perm α)
    (hm : ∀ i, I i (π i)) (a : Tag × α) :
    (∃ c d, c≠d ∧ join I a c ∧ join I a d) ∧
    (∃ c d, c≠d ∧ join I c a ∧ join I d a) := by
  obtain ⟨s,i⟩ := a
  by_cases h : s=0
  · subst s
    constructor
    · exact ⟨(0,π i),(1,i),fun e => (by decide : (0:Tag)≠1) (congrArg Prod.fst e),
        Or.inl ⟨rfl,rfl,hm i⟩,Or.inr ⟨rfl,by decide⟩⟩
    · exact ⟨(0,π.symm i),(4,i),fun e => (by decide : (0:Tag)≠4) (congrArg Prod.fst e),
        Or.inl ⟨rfl,rfl,by simpa using hm (π.symm i)⟩,Or.inr ⟨rfl,by decide⟩⟩
  · obtain ⟨t,u,htu,st,su⟩ := template_data.2.2.2.1 s h
    obtain ⟨v,w,hvw,vs,ws⟩ := template_data.2.2.2.2.1 s h
    exact ⟨⟨(t,i),(u,i),fun e => htu (congrArg Prod.fst e),Or.inr ⟨rfl,st⟩,Or.inr ⟨rfl,su⟩⟩,
      ⟨(v,i),(w,i),fun e => hvw (congrArg Prod.fst e),Or.inr ⟨rfl,vs⟩,Or.inr ⟨rfl,ws⟩⟩⟩

end CoMatchedPadding
