import PEqualNP.CoSafeBlock3456
import PEqualNP.CoSafePhysical3456

namespace CoSafePhysical3456

open CoAO3143Restriction CoCompile3456 CoSafePort3456 CoSafeFormula3456
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def active {ι α : Type*} {n} (bank : ι → Wire (Rows n)) (row : α → Rows n)
    (x : α) : Set ι := {i | bank i (row x) = true}

theorem compiled_block {ι α : Type*} [Fintype ι] {n} (bank : ι → Wire (Rows n))
    (row : α → Rows n) (sing : Fin n → α) (atOne : ∀ v, row (sing v) = one v)
    (mark : ι → Prop) (t : CoSafeFormula3456.Tree ι) {gs : List Gate}
    (well : good n gs) (dryBank : dry n gs) (paid : ∀ i, bank i ∈ symbolic n gs)
    (raw : ∀ v i, i ∈ active bank row (sing v) → ¬ mark i → ∀ y,
       i ∈ active bank row y → active bank row (sing v) ⊆ active bank row y)
    (chain : ∀ v i j, i ∈ active bank row (sing v) → j ∈ active bank row (sing v) →
      mark i → mark j →
        ImpliesPort (active bank row) i j ∨ ImpliesPort (active bank row) j i) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ dry n D.gates ∧
      D.size ≤ gs.length + gates t ∧ ∀ x, circuitFun n D (row x) = true ↔
        holds (fun i => bank i (row x) = true) t := by
  obtain ⟨u,budget,same,cleaned⟩ :=
    normalize_block (active bank row) sing mark raw chain t
  have cleared : ∀ v : Fin n, clean (fun i => bank i (one v) = true) u := by
    intro v
    simpa [active,atOne v] using cleaned v
  obtain ⟨D,dm,dr,dd,ds,de⟩ := physical_formula bank u well dryBank paid cleared
  refine ⟨D,dm,dr,dd,by omega,?_⟩
  intro x
  rw [de]
  exact (value_iff bank u (row x)).trans (same x)

end CoSafePhysical3456
