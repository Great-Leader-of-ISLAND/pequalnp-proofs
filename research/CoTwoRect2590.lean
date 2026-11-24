import PEqualNP.Defs

namespace CoTwoRect2590

universe u

def raw {C : Type u} (r : Fin 2 → Fin 3 → Bool) (c : Fin 2 → C → Bool)
    (leaf : Fin 2) (i : Fin 3) (col : C) : Bool :=
  r leaf i && c leaf col

def marked {C : Type u} (r : Fin 2 → Fin 3 → Bool) (c : Fin 2 → C → Bool)
    (i : Fin 3) (col : C) : Bool :=
  raw r c 0 i col || raw r c 1 i col

-- The six row bits have 64 profiles. The two column bits concern only the
-- reference column. No arbitrary column or function is enumerated.
private theorem reference_profiles :
    ∀ a₀ b₀ a₁ b₁ a₂ b₂ x y : Bool,
    ((a₀ && x) || (b₀ && y))=true →
    ((a₁ && x) || (b₁ && y))=true →
    ((a₂ && x) || (b₂ && y))=true →
    ((a₀ && x)=true → (b₀ && y)=false) →
    ((a₁ && x)=true → (b₁ && y)=false) →
    ((a₂ && x)=true → (b₂ && y)=false) →
    ((a₀=a₁ ∧ b₀=b₁) ∨ (a₀=a₂ ∧ b₀=b₂) ∨ (a₁=a₂ ∧ b₁=b₂)) := by
  decide +kernel

-- Disjointness on the reference column already suffices.
theorem equal_row_profiles {C : Type u} (r : Fin 2 → Fin 3 → Bool)
    (c : Fin 2 → C → Bool) (ref : C) (cover : ∀ i,marked r c i ref=true)
    (apart : ∀ i,raw r c 0 i ref=true → raw r c 1 i ref=false) :
    ∃ i j : Fin 3, i≠j ∧ r 0 i=r 0 j ∧ r 1 i=r 1 j := by
  have h := reference_profiles (r 0 0) (r 1 0) (r 0 1) (r 1 1) (r 0 2) (r 1 2)
    (c 0 ref) (c 1 ref) (cover 0) (cover 1) (cover 2) (apart 0) (apart 1) (apart 2)
  rcases h with a | b | d
  · exact ⟨0,1,by decide,a⟩
  · exact ⟨0,2,by decide,b⟩
  · exact ⟨1,2,by decide,d⟩

-- The same two distinct rows work simultaneously on every column.
theorem two_rectangles {C : Type u} (r : Fin 2 → Fin 3 → Bool)
    (c : Fin 2 → C → Bool) (ref : C) (cover : ∀ i,marked r c i ref=true)
    (apart : ∀ i col,raw r c 0 i col=true → raw r c 1 i col=false) :
    ∃ i j : Fin 3, i≠j ∧ ∀ col,marked r c i col=marked r c j col := by
  obtain ⟨i,j,ne,h₀,h₁⟩ := equal_row_profiles r c ref cover (fun t => apart t ref)
  refine ⟨i,j,ne,?_⟩
  intro col
  simp only [marked,raw,h₀,h₁]

-- A single rectangle covering all rows at a reference column has identical
-- membership across every row, at every other column as well.
theorem one_rectangle {C : Type u} (r : Fin 3 → Bool) (c : C → Bool) (ref : C)
    (cover : ∀ i,(r i && c ref)=true) :
    ∀ (i j : Fin 3) (col : C),(r i && c col)=(r j && c col) := by
  have on (i : Fin 3) : r i=true := by
    have h := cover i
    simp only [Bool.and_eq_true] at h
    exact h.1
  intro i j col
  rw [on i,on j]

end CoTwoRect2590
