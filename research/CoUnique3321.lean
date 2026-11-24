import PEqualNP.CoClean3321

namespace CoUnique3321
open CoClean3321

noncomputable def addLine {L : Type} (y : Side L) (l : L) : Side L := by
  classical
  exact fun m => if m=l then true else y m

def neighbor {L : Type} (T : L→Prop) (y : Side L) := ∃ l, T l ∧ y l=true

def growsLines {P L : Type} (B : Signal P L) :=
  ∀ x y y', (∀ l, y l=true → y' l=true) → B x y=true → B x y'=true

/-- The rest of a circuit reads a pivot only through a single OR(p,B).
The new point p is separated from the old points X. -/
def throughOR {P L : Type} (I : P→L→Prop) (T : L→Prop) (B : Signal P L) :=
  ∃ tail : Side P→Side L→Bool→Bool, ∀ x y p,
    (tail x y (p || B x y)=true ↔ edge I x y ∨ (p=true ∧ neighbor T y))

private theorem shadow {P L : Type} {I : P→L→Prop} {T : L→Prop} {B : Signal P L}
    (readOnce : throughOR I T B) {x : Side P} {y : Side L}
    (active : B x y=true) (n : neighbor T y) : edge I x y := by
  obtain ⟨tail,ht⟩ := readOnce
  have a := (ht x y true).mpr (Or.inr ⟨rfl,n⟩)
  have b : tail x y (false || B x y)=true := by simpa [active] using a
  rcases (ht x y false).mp b with e|⟨bad,_⟩
  · exact e
  · contradiction

/-- Independent activation forces all pivot-neighbor lines to be covered by
selected old points, and none of those lines can already be selected. -/
theorem independent_blocks_all {P L : Type} {I : P→L→Prop} {T : L→Prop}
    {B : Signal P L} (mB : growsLines B) (readOnce : throughOR I T B)
    {x : Side P} {y : Side L} (ind : ¬edge I x y) (active : B x y=true) :
    (¬neighbor T y) ∧ (∀ l, T l → ∃ u, x u=true ∧ I u l) := by
  classical
  refine ⟨fun n => ind (shadow readOnce active n),?_⟩
  intro l hl
  have active' : B x (addLine y l)=true := by
    apply mB x y (addLine y l) _ active
    intro i hi
    by_cases h : i=l <;> simp [addLine,h,hi]
  have n : neighbor T (addLine y l) := ⟨l,hl,by simp [addLine]⟩
  obtain ⟨u,k,link,hu,hk⟩ := shadow readOnce active' n
  by_cases h : k=l
  · exact ⟨u,hu,h ▸ link⟩
  · exact False.elim (ind ⟨u,k,link,hu,by simpa [addLine,h] using hk⟩)

/-- Exact semantic criterion for a unique OR read, allowing arbitrary reuse
of its output and arbitrary computation elsewhere. -/
theorem or_criterion {P L : Type} {I : P→L→Prop} {T : L→Prop} {B : Signal P L}
    (mB : growsLines B) : throughOR I T B ↔
      ∀ x y, B x y=true → edge I x y ∨ (∀ l, T l → ∃ u, x u=true ∧ I u l) := by
  classical
  constructor
  · intro h x y active
    by_cases e : edge I x y
    · exact Or.inl e
    · exact Or.inr (independent_blocks_all mB h e active).2
  · intro guard
    refine ⟨fun x y b => decide (edge I x y ∨ (b=true ∧ neighbor T y)),?_⟩
    intro x y p
    simp only [decide_eq_true_eq]
    constructor
    · rintro (e|⟨on,n⟩)
      · exact Or.inl e
      · cases hp : p with
        | true => exact Or.inr ⟨rfl,n⟩
        | false =>
          have active : B x y=true := by simpa [hp] using on
          rcases guard x y active with e|cover
          · exact Or.inl e
          · obtain ⟨l,hl,yl⟩ := n
            obtain ⟨u,xu,ul⟩ := cover l hl
            exact Or.inl ⟨u,l,ul,xu,yl⟩
    · rintro (e|⟨on,n⟩)
      · exact Or.inl e
      · exact Or.inr ⟨by simp [on],n⟩

/-- Square-freeness between the pivot and each remaining point turns coverage
into an injection. This uses no finiteness assumptions or chosen incidence labels. -/
theorem inject_neighbors {P L : Type} {I : P→L→Prop} {T : L→Prop}
    (noSquare : ∀ u l m, T l → T m → I u l → I u m → l=m)
    {B : Signal P L} (mB : growsLines B) (readOnce : throughOR I T B)
    {x : Side P} {y : Side L} (ind : ¬edge I x y) (active : B x y=true) :
    ∃ f : {l // T l} → {u // x u=true}, Function.Injective f := by
  classical
  have cover := (independent_blocks_all mB readOnce ind active).2
  let f (a : {l // T l}) : {u // x u=true} :=
    ⟨Classical.choose (cover a.val a.property),
      (Classical.choose_spec (cover a.val a.property)).1⟩
  have hit (a : {l // T l}) : I (f a).val a.val :=
    (Classical.choose_spec (cover a.val a.property)).2
  refine ⟨f,?_⟩
  intro a b eq
  apply Subtype.ext
  exact noSquare (f a).val a.val b.val a.property b.property (hit a) (by rw [eq]; exact hit b)

def throughAND {P L : Type} (I : P→L→Prop) (T : L→Prop) (B : Signal P L) :=
  ∃ tail : Side P→Side L→Bool→Bool, ∀ x y p,
    (tail x y (p && B x y)=true ↔ edge I x y ∨ (p=true ∧ neighbor T y))

theorem and_accepts_each {P L : Type} {I : P→L→Prop} {T : L→Prop} {B : Signal P L}
    (readOnce : throughAND I T B) {l : L} (hl : T l) : B zero (single l)=true := by
  classical
  obtain ⟨tail,ht⟩ := readOnce
  have n : neighbor T (single l) := ⟨l,hl,by simp [single]⟩
  have a := (ht zero (single l) true).mpr (Or.inr ⟨rfl,n⟩)
  cases h : B zero (single l) with
  | true => rfl
  | false =>
    have b : tail zero (single l) (false && B zero (single l))=true := by simpa [h] using a
    rcases (ht zero (single l) false).mp b with ⟨_,_,_,v,_⟩|⟨bad,_⟩
    · simp [zero] at v
    · contradiction

#print axioms CoUnique3321.or_criterion
#print axioms CoUnique3321.inject_neighbors
#print axioms CoUnique3321.and_accepts_each
end CoUnique3321
