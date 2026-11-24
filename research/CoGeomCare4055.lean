import PEqualNP.CoSensitivity4055

namespace CoGeomCare4055
open CoSensitivity4055

variable {I : Type} [Fintype I] [DecidableEq I]
abbrev Row (I : Type) := Finset I × Finset I
abbrev Evaluator (I : Type) := Row I → Bool

def Mono (w : Evaluator I) : Prop :=
  ∀ a b : Row I, a.1 ⊆ b.1 → a.2 ⊆ b.2 → w a = true → w b = true

def sample (N : I → Finset I) (i : Option I) (w : Evaluator I) : Word I :=
  match i with
  | none =>
    fun j => match j with
    | none => w (∅, Finset.univ)
    | some p => w ({p},∅)
  | some p =>
    fun j => match j with
    | none => w ({p},Finset.univ \ N p)
    | some l => w (∅,{l})

def lines (w : Evaluator I) : Finset I := Finset.univ.filter (fun l => w (∅,{l}) = true)

private theorem some_data (N : I → Finset I) (p : I) (w : Evaluator I) (hw : Mono w)
    (h : 2 ≤ (changes (sample N (some p) w)).card) :
    2 ≤ (lines w).card ∧ lines w ⊆ N p := by
  cases b : w ({p}, Finset.univ \ N p) with
  | true => simp [changes,sample,b] at h
  | false =>
    constructor
    · have same : changes (sample N (some p) w) = lines w := by
        ext l
        simp [changes,sample,b,lines]
      rw [← same]
      exact h
    · intro l hl
      by_contra outside
      have yes := (Finset.mem_filter.mp hl).2
      have small : ({l} : Finset I) ⊆ Finset.univ \ N p := by
        intro x hx
        obtain rfl := Finset.mem_singleton.mp hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,outside⟩
      have bad := hw (∅,{l}) ({p},Finset.univ \ N p) (Finset.empty_subset _) small yes
      rw [b] at bad
      exact Bool.noConfusion bad

private theorem none_data (N : I → Finset I) (w : Evaluator I) (hw : Mono w)
    (h : 2 ≤ (changes (sample N none w)).card) : lines w = ∅ := by
  cases b : w (∅, Finset.univ) with
  | true => simp [changes,sample,b] at h
  | false =>
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    have yes := (Finset.mem_filter.mp hl).2
    have bad := hw (∅,{l}) (∅,Finset.univ) (Finset.empty_subset _) (Finset.subset_univ _) yes
    rw [b] at bad
    exact Bool.noConfusion bad

/-- Each monotone physical wire can have at least two true singleton probes
at at most one of the point-negative or all-line-negative tags. -/
theorem exclusive (N : I → Finset I) (hN : ∀ p q, p ≠ q → (N p ∩ N q).card ≤ 1)
    (w : Evaluator I) (hw : Mono w) (i j : Option I)
    (hi : 2 ≤ (changes (sample N i w)).card)
    (hj : 2 ≤ (changes (sample N j w)).card) : i=j := by
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some q =>
      have h := (some_data N q w hw hj).1
      rw [none_data N w hw hi] at h
      simp at h
  | some p =>
    cases j with
    | none =>
      have h := (some_data N p w hw hi).1
      rw [none_data N w hw hj] at h
      simp at h
    | some q =>
      by_cases e : p=q
      · rw [e]
      · obtain ⟨card,hp⟩ := some_data N p w hw hi
        obtain ⟨_,hq⟩ := some_data N q w hw hj
        have sub : lines w ⊆ N p ∩ N q := fun l hl => Finset.mem_inter.mpr ⟨hp hl,hq hl⟩
        have bound := (Finset.card_le_card sub).trans (hN p q e)
        omega

end CoGeomCare4055
