import PEqualNP.CoNine3024Cotree
import PEqualNP.CoNine3024Rows

namespace CoNine3024CotreeCells
open CoAO3143Restriction CoThetaNine CoNine3024 CoNine3024Rows CoNine3024Cotree

def Only (ws : List Atom) (c : Fin 320) (a : Atom) : Prop :=
  ∀ w∈ws, (separator w).getLsbD c.val=true → w.full=a.full

private theorem forced (p : Fin 11) {ws : List Atom} {S : Finset (Wire Input)}
    (good : ∀ w∈ws, Good p w) (cover : ∀ w∈S,∃ u∈ws,value u=w)
    {c : Fin 320} (allow : used p c) {a : Atom} (own : Only ws c a) :
    Forced S (prow p c) (nrow p c) (value a) := by
  intro w hw sepw
  obtain ⟨u,hu,rfl⟩ := cover w hw
  obtain ⟨on,off⟩ := sepw
  have pl := (good u hu).pos c allow
  have nl := (good u hu).neg c allow
  have one : (separator u).getLsbD c.val=true := by
    simp only [separator,BitVec.getLsbD_and,BitVec.getLsbD_not,c.isLt,decide_true,
      ↓reduceIte,pl,nl,on,off]
    <;> rfl
  have eq := own u hu one
  funext r
  exact congrArg (fun t : Truth => t.getLsbD r.val) eq

/-- Packed four-cell interface for the existing nine-input search. A finite
checker need only supply two shared row-index equalities and four unique
separator witnesses; duplicate atoms of equal full truth are harmless. -/
theorem shared_cell_pair (p : Fin 11) {ws : List Atom} {k S} (run : Cone ans k S)
    (tight : S.card=k+1) (good : ∀ w∈ws,Good p w) (cover : ∀ w∈S,∃ u∈ws,value u=w)
    {c₁ c₂ c₃ c₄ : Fin 320} (h₁ : used p c₁) (h₂ : used p c₂)
    (h₃ : used p c₃) (h₄ : used p c₄)
    (sameP : prow p c₂=prow p c₁) (sameN : nrow p c₄=nrow p c₃)
    {a b : Atom} (a₁ : Only ws c₁ a) (b₁ : Only ws c₂ b)
    (a₂ : Only ws c₃ a) (b₂ : Only ws c₄ b) : a.full=b.full := by
  apply full_inj
  have label {c : Fin 320} (hc : used p c) : sep (prow p c) (nrow p c) ans := target_rows p c hc
  exact forced_pair run tight (label h₁) (by simpa only [sameP] using label h₂)
    (label h₃) (by simpa only [sameN] using label h₄)
    (forced p good cover h₁ a₁) (by simpa only [sameP] using forced p good cover h₂ b₁)
    (forced p good cover h₃ a₂) (by simpa only [sameN] using forced p good cover h₄ b₂)

#print axioms shared_cell_pair
end CoNine3024CotreeCells
