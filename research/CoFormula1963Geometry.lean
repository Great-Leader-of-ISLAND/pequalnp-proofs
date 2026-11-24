import Mathlib

namespace CoFormula1963Geometry

abbrev V := Fin 13

def D : Finset V := {0,1,3,9}

def inc (p l : V) : Prop := p-l ∈ D
instance (p l : V) : Decidable (inc p l) := by unfold inc; infer_instance

def clear (Q : Finset V) (l : V) : Prop := ∀ p ∈ Q, ¬ inc p l
instance (Q : Finset V) (l : V) : Decidable (clear Q l) := by unfold clear; infer_instance

def isQuad (Q : Finset V) : Prop := Q.card = 4 ∧ ∀ l : V, (Q.filter fun p => inc p l).card ≤ 2
instance (Q : Finset V) : Decidable (isQuad Q) := by unfold isQuad; infer_instance

/-- The three official hypotheses on generic negatives of L-meta-1681,
    with the cyclic incidence presented by subtraction. -/
def generic (Q : Finset V) : Prop :=
  (∀ v : V, v ∉ Q → ∃ l : V, clear Q l ∧ inc v l) ∧
  (¬ ∃ l : V, ∀ p ∈ Q, inc p l) ∧
  ¬ ∃ v : V, ∀ l : V, clear Q l → inc v l
instance (Q : Finset V) : Decidable (generic Q) := by unfold generic; infer_instance

theorem inc_add : ∀ p l : V, inc p l ↔ ∃ d ∈ D, p = l+d := by decide +kernel

/-- The least numerical four-bitset representative of each of the eighteen
    cyclic shift orbits from the official PG(2,3) projective plane. -/
def base : Fin 18 → Finset V := ![
  {0,2,3,4},{0,1,2,5},{0,1,2,6},{0,2,3,6},{0,1,4,6},{0,2,4,6},
  {0,2,5,6},{0,3,5,6},{0,1,2,7},{0,2,3,7},{0,1,6,7},{0,3,6,7},
  {0,1,4,8},{0,3,4,8},{0,3,5,8},{0,3,6,8},{0,4,6,8},{0,2,5,9}]

def quad (r : Fin 18) (s : V) : Finset V := (base r).image (fun p => p+s)

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- All 234 labeled columns meet the exact four-point and generic conditions.
    Completeness among all quad sets is not required for the lower bound. -/
theorem samples : ∀ r : Fin 18, ∀ s : V, isQuad (quad r s) ∧ generic (quad r s) := by
  intro r
  fin_cases r <;> decide +kernel

/-- One cyclic orbit alone already separates all 117 nonincident point-line
    pairs: mark the point and the line simultaneously in a negative. -/
theorem cooccur : ∀ p l : V, ¬ inc p l → ∃ s : V, p ∈ quad 0 s ∧ clear (quad 0 s) l := by
  intro p
  fin_cases p <;> decide +kernel

theorem no_four : ∀ p l a b : V, inc p l → inc p a → inc b l →
    a ≠ l → b ≠ p → ¬ inc b a := by
  intro p
  fin_cases p <;> decide +kernel

theorem crossed (p l a b : V) (e : inc p l) (f : inc p a) (g : inc b l)
    (fa : a ≠ l) (gb : b ≠ p) :
    ∃ s : V, clear (quad 0 s) a ∧ b ∈ quad 0 s := by
  obtain ⟨s,hb,ha⟩ := cooccur b a (no_four p l a b e f g fa gb)
  exact ⟨s,ha,hb⟩

#print axioms samples
#print axioms crossed
end CoFormula1963Geometry
