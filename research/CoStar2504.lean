import Mathlib

namespace PhaseTwo.Star2504

abbrev Input := Fin 8 → Bool
def atOne (j : Fin 8) : Input := fun i => decide (i=j)
def center (i : Fin 4) : Fin 8 := (![1,2,4,7] : Fin 4 → Fin 8) i
def witness (i : Fin 4) : Fin 8 := (![5,6,6,5] : Fin 4 → Fin 8) i
def ed : List (Fin 8 × Fin 8) := [(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)]
def f (a : Input) : Bool := ed.any fun e => a e.1 && a e.2
def onF (a : Input) : Bool := f a || a 0 || a 3
def usesStars (outer : Bool) (force : Fin 4 → Bool) (bank : Fin 4 → Input → Bool) (a : Input) : Prop :=
  outer=true ∨ ∃ i, (force i=true ∨ a (center i)=true) ∧ bank i a=true

theorem cover_unique : ∀ mask : Fin 256,
    (∀ e ∈ ed, mask.val.testBit e.1.val=true ∨ mask.val.testBit e.2.val=true) →
    ((Finset.univ : Finset (Fin 8)).filter (fun i => mask.val.testBit i.val=true)).card ≤ 4 →
    mask.val=150 := by decide +kernel

theorem star_lifts_fail (outer : Bool) (force : Fin 4 → Bool)
    (bank : Fin 4 → Input → Bool) (privateLeaf : ∀ i, bank i (atOne (witness i))=true) :
    ¬ ∀ a, usesStars outer force bank a ↔ onF a=true := by
  intro agree
  have fail : ∀ i : Fin 4, onF (atOne (witness i))=false := by decide
  have noOuter : outer≠true := fun ho => Bool.false_ne_true ((fail 0).symm.trans
    ((agree _).mp (Or.inl ho)))
  have noForce (i : Fin 4) : force i≠true := fun hi => Bool.false_ne_true ((fail i).symm.trans
    ((agree _).mp (Or.inr ⟨i, Or.inl hi, privateLeaf i⟩)))
  have none : ∀ i : Fin 4, atOne 0 (center i)=false := by decide
  have pos : onF (atOne 0)=true := by decide
  rcases (agree _).mpr pos with h|⟨i,hi,_⟩
  · exact noOuter h
  · rcases hi with h|h
    · exact noForce i h
    · exact Bool.false_ne_true ((none i).symm.trans h)

end PhaseTwo.Star2504
