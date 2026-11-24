import PEqualNP.CoSensitivity4055

namespace CoCare4055
open CoSensitivity4055 CoMerge4055

variable {U I : Type} [Fintype U] [DecidableEq U]
def count : List Rule → List (Word U) → Nat
  | [], _ => 0
  | r::rs, ws => (if 2 ≤ (changes (step ws r)).card then 1 else 0) + count rs (signal ws r)

private theorem reaches (rs : List Rule) {T : Finset (Finset U)} {n : Nat} {ws : List (Word U)}
    (tiny : ∀ u : Finset U, u.card ≤ 1 → u ∈ T) (cover : Covered T ws) (bound : Budget T n) :
    ∃ R : Finset (Finset U), ∅ ∈ R ∧ Covered R (rs.foldl signal ws) ∧ Budget R (n+count rs ws) := by
  induction rs generalizing T n ws with
  | nil => exact ⟨T,tiny _ (by simp),cover,by simpa [count] using bound⟩
  | cons r rs ih =>
    let z := changes (step ws r)
    by_cases big : 2 ≤ z.card
    · have empty := tiny ∅ (by simp)
      obtain ⟨a,ha,pa⟩ := meet_small empty cover r.1
      obtain ⟨b,hb,pb⟩ := meet_small empty cover r.2
      have sub : z ⊆ a ∪ b := (split_rule ws r).trans (Finset.union_subset_union pa pb)
      have tiny' : ∀ u : Finset U, u.card ≤ 1 → u ∈ insert z T :=
        fun u hu => Finset.mem_insert_of_mem (tiny u hu)
      have cover' : Covered (insert z T) (signal ws r) := by
        intro w hw
        rcases List.mem_append.mp hw with hw|hw
        · exact Finset.mem_insert_of_mem (cover w hw)
        · obtain rfl := List.mem_singleton.mp hw
          exact Finset.mem_insert_self _ _
      obtain ⟨R,e,c,h⟩ := ih tiny' cover' (CoMerge4055.add bound ha hb sub)
      exact ⟨R,e,c,by simpa only [count,show 2 ≤ (changes (step ws r)).card from big,
        if_true,Nat.add_assoc] using h⟩
    · have cover' : Covered T (signal ws r) := by
        intro w hw
        rcases List.mem_append.mp hw with hw|hw
        · exact cover _ hw
        · obtain rfl := List.mem_singleton.mp hw
          exact tiny _ (by change z.card ≤ 1; omega)
      obtain ⟨R,e,c,h⟩ := ih tiny cover' bound
      exact ⟨R,e,c,by simpa only [count,show ¬ 2 ≤ (changes (step ws r)).card from big,
        if_false,Nat.zero_add] using h⟩

theorem charged_cost (rs : List Rule) (out : Finset Nat) (ws : List (Word U))
    (raw : ∀ w∈ws, (changes w).card ≤ 1) :
    (changes (conjunction (rs.foldl signal ws) out)).card ≤ count rs ws + 1 := by
  classical
  let T := Finset.univ.filter (fun s : Finset U => s.card ≤ 1)
  have tiny (u : Finset U) (hu : u.card ≤ 1) : u ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩
  have cap : Budget T 0 := CoMerge4055.initial (by intro a ha; exact (Finset.mem_filter.mp ha).2)
  obtain ⟨R,e,c,h⟩ := reaches rs tiny (fun w hw => tiny _ (raw w hw)) cap
  obtain ⟨a,ha,sub⟩ := meet_small e c out
  exact (Finset.card_le_card sub).trans (by simpa using CoMerge4055.single h ha)

variable [DecidableEq I]
def Separated (J : Finset I) : List Rule → (I → List (Word U)) → Prop
  | [], _ => True
  | r::rs, B =>
    (∀ i ∈ J, ∀ j ∈ J, 2 ≤ (changes (step (B i) r)).card →
      2 ≤ (changes (step (B j) r)).card → i=j) ∧
    Separated J rs (fun i => signal (B i) r)

/-- Multiple independent row families sharing the *same* physical rule list; charged_cost
allows every arm to be an arbitrary conjunction, with different responsible pins per tag. -/
theorem total (J : Finset I) (rs : List Rule) (B : I → List (Word U))
    (outputs : I → Finset Nat) (d : I → Nat) (sep : Separated J rs B)
    (raw : ∀ i∈J, ∀ w∈B i, (changes w).card ≤ 1)
    (out : ∀ i∈J, d i ≤ (changes (conjunction (rs.foldl signal (B i)) (outputs i))).card) :
    (∑ i ∈ J, (d i - 1)) ≤ rs.length := by
  classical
  have charges (gs : List Rule) (Y : I → List (Word U)) (s : Separated J gs Y) :
      (∑ i ∈ J, count gs (Y i)) ≤ gs.length := by
    induction gs generalizing Y with
    | nil => simp [count]
    | cons r gs ih =>
      obtain ⟨unique,tail⟩ := s
      let b := fun i => 2 ≤ (changes (step (Y i) r)).card
      have once : (∑ i ∈ J, (if b i then 1 else 0 : Nat)) ≤ 1 := by
        by_cases existsHeavy : ∃ i ∈ J,b i
        · obtain ⟨p,hp,bp⟩ := existsHeavy
          calc
            _ = ∑ i ∈ J, (if i=p then 1 else 0 : Nat) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases bi : b i
              · have e := unique i hi p hp bi bp
                rw [if_pos bi, if_pos e]
              · have ne : i ≠ p := fun e => bi (e ▸ bp)
                simp [bi,ne]
            _ ≤ 1 := by simp [hp]
        · have z : (∑ i ∈ J, (if b i then 1 else 0 : Nat)) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have no : ¬ b i := fun bi => existsHeavy ⟨i,hi,bi⟩
            simp [no]
          omega
      have rest := ih (fun i => signal (Y i) r) tail
      simp only [count, List.length_cons, Finset.sum_add_distrib]
      change (∑ i ∈ J, (if b i then 1 else 0 : Nat)) + (∑ i ∈ J, count gs (signal (Y i) r)) ≤ _
      omega
  apply le_trans _ (charges rs B sep)
  apply Finset.sum_le_sum
  intro i hi
  have v := charged_cost rs (outputs i) (B i) (raw i hi)
  have h := out i hi
  omega

end CoCare4055
