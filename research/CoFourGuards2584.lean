import Mathlib

namespace CoFourGuards2584

def tests (ap al bp bl : Prop) : Prop := (ap ∨ al) ∧ (bp ∨ bl)

theorem crossing {aq ar at' au bq br bt bu : Prop}
    (qt : tests aq at' bq bt) (ru : tests ar au br bu)
    (qu : ¬ tests aq au bq bu) (rt : ¬ tests ar at' br bt) :
    (aq ∨ ar) ∧ (bq ∨ br) := by
  unfold tests at *
  tauto

variable {X Y : Type*}

def flag (P : X → Prop) (L : Y → Prop) (A B : X → Prop) (U V : Y → Prop)
    (x : X) (y : Y) : Prop := P x ∧ L y ∧ tests (A x) (U y) (B x) (V y)

def twoPoints (P : X → Prop) (L : Y → Prop) (A B : X → Prop) (U V : Y → Prop)
    (x x' : X) (y : Y) : Prop :=
  (P x ∨ P x') ∧ L y ∧ tests (A x ∨ A x') (U y) (B x ∨ B x') (V y)

/-- Given a bad witness with central point p and line e, two other points
    cannot have different exceptional lines, both different from e. -/
theorem exclusive_tip
    (I : X → Y → Prop) (P : X → Prop) (L : Y → Prop)
    (A B : X → Prop) (U V : Y → Prop)
    (square : ∀ x x' y y', x ≠ x' → y ≠ y' →
      ¬ (I x y ∧ I x y' ∧ I x' y ∧ I x' y'))
    (pairs : ∀ x y, flag P L A B U V x y → I x y)
    (triples : ∀ x x' y, twoPoints P L A B U V x x' y → I x y ∨ I x' y)
    (p q r : X) (e t u : Y) (hp : P p) (ha : A p) (hb : B p) (he : L e)
    (qp : q ≠ p) (rp : r ≠ p) (te : t ≠ e) (ue : u ≠ e)
    (qt : flag P L A B U V q t) (ru : flag P L A B U V r u) : t = u := by
  by_contra tu
  have star (y : Y) (hy : L y) : I p y :=
    pairs p y ⟨hp,hy,Or.inl ha,Or.inl hb⟩
  have it := pairs q t qt
  have iu := pairs r u ru
  have pt := star t qt.2.1
  have pu := star u ru.2.1
  have pe := star e he
  have qu : ¬ I q u := fun bad =>
    square q p t u qp tu ⟨it,bad,pt,pu⟩
  have rt : ¬ I r t := fun bad =>
    square r p u t rp (Ne.symm tu) ⟨iu,bad,pu,pt⟩
  have qe : ¬ I q e := fun bad =>
    square q p t e qp te ⟨it,bad,pt,pe⟩
  have re : ¬ I r e := fun bad =>
    square r p u e rp ue ⟨iu,bad,pu,pe⟩
  have branches := crossing qt.2.2 ru.2.2
    (fun h => qu (pairs q u ⟨qt.1,ru.2.1,h⟩))
    (fun h => rt (pairs r t ⟨ru.1,qt.2.1,h⟩))
  have neg := triples q r e ⟨Or.inl qt.1,he,Or.inl branches.1,Or.inl branches.2⟩
  exact neg.elim qe re

end CoFourGuards2584
