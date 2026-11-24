import Mathlib

namespace PEqualNP.Research.PetersenDimacs

-- A signed variable uses true for a positive literal. As in the DIMACS
-- writer, the distinguished true variable may occur with either sign.
abbrev SignedVar := ℕ × Bool

def literalValue (v : ℕ → Bool) (l : SignedVar) : Bool :=
  if l.2 then v l.1 else !(v l.1)

def clauseTrue (v : ℕ → Bool) (c : List SignedVar) : Prop :=
  ∃ l ∈ c, literalValue v l = true

def eraseConstant (t : ℕ) (c : List SignedVar) : Option (List SignedVar) :=
  if (t, true) ∈ c then none else some (c.filter fun l => decide (l ≠ (t, false)))

private theorem filter_false_literal (v : ℕ → Bool) (t : ℕ) (ht : v t = true)
    (c : List SignedVar) :
    clauseTrue v (c.filter fun l => decide (l ≠ (t, false))) ↔ clauseTrue v c := by
  constructor
  · rintro ⟨l,hl,hv⟩
    exact ⟨l, (List.mem_filter.mp hl).1, hv⟩
  · rintro ⟨l,hl,hv⟩
    have hne : l ≠ (t,false) := by
      rintro rfl
      simp [literalValue, ht] at hv
    exact ⟨l, List.mem_filter.mpr ⟨hl, by simp [hne]⟩, hv⟩

-- The Python method add skips positive-true clauses and removes negative-true
-- literals from the remaining clauses. This accounts also for empty clauses.
theorem eraseConstant_correct (v : ℕ → Bool) (t : ℕ) (ht : v t = true)
    (cs : List (List SignedVar)) :
    (∀ c ∈ cs.filterMap (eraseConstant t), clauseTrue v c) ↔
      (∀ c ∈ cs, clauseTrue v c) := by
  constructor
  · intro h c hc
    by_cases hpos : (t,true) ∈ c
    · exact ⟨(t,true), hpos, by simp [literalValue, ht]⟩
    · apply (filter_false_literal v t ht c).mp
      apply h
      exact List.mem_filterMap.mpr ⟨c, hc, by simp [eraseConstant, hpos]⟩
  · intro h c hc
    obtain ⟨u,hu,huc⟩ := List.mem_filterMap.mp hc
    by_cases hpos : (t,true) ∈ u
    · simp [eraseConstant, hpos] at huc
    · simp only [eraseConstant, hpos, if_false, Option.some.injEq] at huc
      rw [← huc]
      exact (filter_false_literal v t ht u).mpr (h u hu)

def renameLit (f : ℕ → ℕ) (l : SignedVar) : SignedVar := (f l.1, l.2)

theorem rename_clause (f : ℕ → ℕ) (v : ℕ → Bool) (c : List SignedVar) :
    clauseTrue v (c.map (renameLit f)) ↔ clauseTrue (v ∘ f) c := by
  constructor
  · rintro ⟨l,hl,hv⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hl
    exact ⟨a,ha,hv⟩
  · rintro ⟨l,hl,hv⟩
    exact ⟨renameLit f l, List.mem_map.mpr ⟨l,hl,rfl⟩, hv⟩

-- A computable left inverse transports the whole Boolean assignment. On
-- unused labels, its value can be arbitrary.
theorem rename_model (f back : ℕ → ℕ) (hback : Function.LeftInverse back f)
    (v : ℕ → Bool) (cs : List (List SignedVar)) (h : ∀ c ∈ cs, clauseTrue v c) :
    ∃ w : ℕ → Bool, (∀ i, w (f i) = v i) ∧
      ∀ c ∈ cs.map (List.map (renameLit f)), clauseTrue w c := by
  let w : ℕ → Bool := fun i => v (back i)
  have hw (i : ℕ) : w (f i) = v i := congrArg v (hback i)
  refine ⟨w, hw, ?_⟩
  intro c hc
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
  apply (rename_clause f w a).mpr
  have he : w ∘ f = v := funext hw
  rw [he]
  exact h a ha

theorem injective_rename_model (f : ℕ → ℕ) (hf : Function.Injective f)
    (v : ℕ → Bool) (cs : List (List SignedVar)) (h : ∀ c ∈ cs, clauseTrue v c) :
    ∃ w : ℕ → Bool, (∀ i, w (f i) = v i) ∧
      ∀ c ∈ cs.map (List.map (renameLit f)), clauseTrue w c :=
  rename_model f (Function.invFun f) (Function.leftInverse_invFun hf) v cs h

-- DIMACS uses the sign of a nonzero integer for polarity. Zero is a
-- delimiter, so the lemma requires each variable number to be positive.
def asInteger (l : SignedVar) : ℤ := if l.2 then (l.1 : ℤ) else -(l.1 : ℤ)

def integerValue (v : ℕ → Bool) (i : ℤ) : Bool :=
  if 0 < i then v i.natAbs else !(v i.natAbs)

theorem integer_literal (v : ℕ → Bool) (l : SignedVar) (hp : 0 < l.1) :
    integerValue v (asInteger l) = literalValue v l := by
  obtain ⟨i,b⟩ := l
  change 0 < i at hp
  have hi : (0 : ℤ) < (i : ℤ) := by exact_mod_cast hp
  have hn : ¬(0 : ℤ) < -(i : ℤ) := by omega
  cases b <;> simp [integerValue, asInteger, literalValue, hi, hn]

theorem integer_clause (v : ℕ → Bool) (c : List SignedVar) (hp : ∀ l ∈ c, 0 < l.1) :
    (∃ j ∈ c.map asInteger, integerValue v j = true) ↔ clauseTrue v c := by
  constructor
  · rintro ⟨j,hj,hv⟩
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hj
    exact ⟨l, hl, (integer_literal v l (hp l hl)) ▸ hv⟩
  · rintro ⟨l,hl,hv⟩
    exact ⟨asInteger l, List.mem_map.mpr ⟨l,hl,rfl⟩,
      (integer_literal v l (hp l hl)).symm ▸ hv⟩

end PEqualNP.Research.PetersenDimacs
