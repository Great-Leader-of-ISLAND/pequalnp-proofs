import PEqualNP.Defs
import Mathlib

namespace CoRaw1888
open PEqualNP.CircuitLowerBounds
abbrev Vertex := Fin 10
abbrev Row := Fin 1024
def raw (r : Row) (i : Vertex) := r.val.testBit i.val
def target (x : Vertex → Bool) := (x 0 && x 1) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def seed (x : Vertex → Bool) := x 0 || x 2
def bank (σ : Vertex→Vertex) (x : Vertex→Bool) := List.ofFn (x ∘ σ) ++ [seed x]
def low : Vertex → Row := ![20, 1, 9, 4, 1, 1, 2, 4, 8, 16]
def high : Vertex → Row := ![21, 3, 13, 12, 17, 33, 66, 132, 264, 528]
private theorem changed : ∀ i : Vertex, target (raw (low i))=false ∧ target (raw (high i))=true ∧
    seed (raw (low i))=seed (raw (high i)) ∧ ∀ j : Vertex,j≠i → raw (low i) j=raw (high i) j := by decide +kernel

/-- For this particular supplied OR, even an otherwise unrestricted circuit
still requires every raw coordinate in its reindexed input bank. -/
theorem surjective (D : Circuit) (σ : Vertex→Vertex)
    (computes : ∀ x : Vertex→Bool,D.eval (bank σ x)=target x) : Function.Surjective σ := by
  classical
  intro i
  by_contra missing
  obtain ⟨off,on,held,known⟩ := changed i
  have eq : raw (low i) ∘ σ=raw (high i) ∘ σ := by
    funext j
    exact known (σ j) (fun e => missing ⟨j,e⟩)
  have same : bank σ (raw (low i))=bank σ (raw (high i)) := by
    simp only [bank,held,eq]
  have lo := computes (raw (low i))
  have hi := computes (raw (high i))
  exact Bool.false_ne_true (off.symm.trans (lo.symm.trans ((congrArg D.eval same).trans (hi.trans on))))

theorem bijective (D : Circuit) (σ : Vertex→Vertex)
    (computes : ∀ x : Vertex→Bool,D.eval (bank σ x)=target x) : Function.Bijective σ :=
  ⟨(Finite.injective_iff_surjective).2 (surjective D σ computes),surjective D σ computes⟩

#print axioms CoRaw1888.bijective
end CoRaw1888
