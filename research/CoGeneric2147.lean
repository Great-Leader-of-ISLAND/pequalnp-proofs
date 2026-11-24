import Mathlib
import PEqualNP.Defs
namespace CoGeneric2147

abbrev V := Fin 13
def offsets : Finset V := {0,1,3,9}
def inc (p l : V) : Prop := ∃ d ∈ offsets, p=l+d
instance (p l : V) : Decidable (inc p l) := by unfold inc; infer_instance
def line (l : V) : Finset V := Finset.univ.filter (fun p => inc p l)
def pencil (p : V) : Finset V := Finset.univ.filter (fun l => inc p l)
def missing (S : Finset V) : Finset V := Finset.univ.filter (fun l => Disjoint S (line l))
def dualMissing (T : Finset V) : Finset V := Finset.univ.filter (fun p => Disjoint T (pencil p))
def arc (B : V → Finset V) (S : Finset V) : Prop :=
  ∀ i j, j∈B i → ¬(B i).erase j ⊆ S

theorem line_meets : ∀ i j : V, ∃ v : V, v∈line i ∧ v∈line j := by decide +kernel
theorem dual_meets : ∀ i j : V, ∃ v : V, v∈pencil i ∧ v∈pencil j := by decide +kernel

theorem missing_membership (S : Finset V) (l : V) :
    l∈missing S ↔ ∀ x∈S, ¬inc x l := by simp [missing,Finset.disjoint_left,line]
theorem dual_membership (T : Finset V) (p : V) :
    p∈dualMissing T ↔ ∀ l∈T, ¬inc p l := by simp [dualMissing,Finset.disjoint_left,pencil]

/-- Once three of the four points of one line have been selected,
every line avoiding those three is in one pencil. -/
theorem avoiding_erase (B : V → Finset V) (cross : ∀ i j, ∃ v, v∈B i ∧ v∈B j)
    {S T : Finset V} (ind : ∀ t∈T, Disjoint S (B t)) {i j : V}
    (cover : (B i).erase j ⊆ S) : ∀ t∈T, j∈B t := by
  intro t ht
  obtain ⟨v,hi,hv⟩ := cross i t
  by_cases e : v=j
  · exact e ▸ hv
  · exact (Finset.disjoint_left.mp (ind t ht) (cover (Finset.mem_erase.mpr ⟨e,hi⟩)) hv).elim

theorem closed_arcs {S T : Finset V} (ind : ∀ x∈S, ∀ t∈T, ¬inc x t)
    (points : ¬ ∃ t, ∀ x∈S, inc x t) (lines : ¬ ∃ x, ∀ t∈T, inc x t) :
    arc line S ∧ arc pencil T := by
  constructor
  · intro i j _ contained
    have sep (t) (ht : t∈T) : Disjoint S (line t) := by
      apply Finset.disjoint_left.mpr
      intro x hx h
      exact ind x hx t ht ((Finset.mem_filter.mp h).2)
    have group := avoiding_erase line line_meets sep contained
    exact lines ⟨j,fun t ht => (Finset.mem_filter.mp (group t ht)).2⟩
  · intro i j _ contained
    have sep (x) (hx : x∈S) : Disjoint T (pencil x) := by
      apply Finset.disjoint_left.mpr
      intro t ht h
      exact ind x hx t ht ((Finset.mem_filter.mp h).2)
    have group := avoiding_erase pencil dual_meets sep contained
    exact points ⟨j,fun x hx => (Finset.mem_filter.mp (group x hx)).2⟩

theorem closure {S T : Finset V} (ind : ∀ x∈S, ∀ t∈T, ¬inc x t)
    (notLine : ¬∃ t, ∀ x∈S, inc x t)
    (notPencil : ¬∃ x, ∀ t∈missing S, inc x t) :
    ∃ U, S⊆U ∧ T⊆missing U ∧
      (∀ x∉U, ∃ l∈missing U, inc x l) ∧
      (¬∃ t, ∀ x∈U, inc x t) ∧ (¬∃ x, ∀ t∈missing U, inc x t) := by
  classical
  let U := dualMissing (missing S)
  have sub : S⊆U := fun x hx => (dual_membership _ x).mpr
    (fun t ht => (missing_membership S t).mp ht x hx)
  have fixed : missing U=missing S := by
    ext t
    constructor
    · intro ht
      exact (missing_membership _ _).mpr (fun x hx => (missing_membership U t).mp ht x (sub hx))
    · intro ht
      exact (missing_membership _ _).mpr (fun x hx => (dual_membership _ _).mp hx t ht)
  refine ⟨U,sub,?_,?_,?_,?_⟩
  · rw [fixed]
    exact fun t ht => (missing_membership _ _).mpr (fun x hx => ind x hx t ht)
  · intro x hx
    rw [fixed]
    by_contra! h
    exact hx ((dual_membership _ _).mpr h)
  · exact fun ⟨t,ht⟩ => notLine ⟨t,fun x hx => ht x (sub hx)⟩
  · rwa [fixed]
#print axioms CoGeneric2147.closed_arcs
#print axioms CoGeneric2147.closure
end CoGeneric2147
