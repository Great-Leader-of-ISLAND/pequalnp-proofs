import PEqualNP.CoPortFaces4482
namespace CoPortDemands4482
open CoPortFaces4482

def dominates {R I : Type*} (wire : I → R → Bool) (a b : R) :=
  ∀ i, wire i a=true → wire i b=true
def monotoneFrom {R I : Type*} (wire : I → R → Bool) (z : R → Bool) :=
  ∀ a b, dominates wire a b → z a=true → z b=true

/-- The upward closure of required positive input words succeeds precisely
when no required negative word lies above a required positive one. -/
theorem interpolate {R I : Type*} (wire : I → R → Bool) (P N : Set R)
    (ok : ∀ p∈P, ∀ n∈N, ¬dominates wire p n) :
    ∃ z : R → Bool, monotoneFrom wire z ∧ (∀ p∈P,z p=true) ∧ ∀ n∈N,z n=false := by
  classical
  let z := fun r : R => decide (∃ p∈P, dominates wire p r)
  refine ⟨z,?_,?_,?_⟩
  · intro a b hab hit
    obtain ⟨p,m,word⟩ := of_decide_eq_true hit
    exact decide_eq_true ⟨p,m,fun i e => hab i (word i e)⟩
  · intro p m
    exact decide_eq_true ⟨p,m,fun _ e => e⟩
  · intro n m
    apply Bool.eq_false_iff.mpr
    intro hit
    obtain ⟨p,v,h⟩ := of_decide_eq_true hit
    exact ok p v n m h

structure Demand (R : Type*) where
  corner : Corner → R
  kind : Kind

def matches {R : Type*} (z : R → Bool) (d : Demand R) :=
  ∀ i, z (d.corner i)=value d.kind i

def clash {R I : Type*} (wire : I → R → Bool) (d e : Demand R) :=
  ∃ i j : Corner, value d.kind i=true ∧ value e.kind j=false ∧
    dominates wire (d.corner i) (e.corner j)

theorem incompatible {R I : Type*} {wire : I → R → Bool} {p n : Demand R}
    (h : clash wire p n) {z : R → Bool} (mono : monotoneFrom wire z)
    (yes : matches z p) (no : matches z n) : False := by
  obtain ⟨i,j,t,f,order⟩ := h
  have hit := mono _ _ order ((yes i).trans t)
  rw [no j,f] at hit
  contradiction

/-- Distinct incompatible local face requirements need distinct output wires.
The witness of incompatibility may be oriented in either direction. -/
theorem clique_price {R I : Type*} (wire : I → R → Bool) {m k : Nat}
    (D : Fin m → Demand R) (out : Fin k → R → Bool)
    (mono : ∀ j, monotoneFrom wire (out j)) (hits : ∀ t, ∃ j, matches (out j) (D t))
    (clique : ∀ t u, t≠u → clash wire (D t) (D u) ∨ clash wire (D u) (D t)) :
    m≤k := by
  classical
  choose who witnessed using hits
  have inj : Function.Injective who := by
    intro t u eq
    by_contra n
    have h := witnessed t
    rw [eq] at h
    rcases clique t u n with f|f
    · exact incompatible f (mono _) h (witnessed u)
    · exact incompatible f (mono _) (witnessed u) h
  simpa using Fintype.card_le_of_injective _ inj

end CoPortDemands4482
