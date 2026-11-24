import PEqualNP.CoMerge4055

namespace CoSensitivity4055
open CoMerge4055
variable {I : Type} [Fintype I] [DecidableEq I]
abbrev Word (I : Type) := Option I → Bool
abbrev Rule := Finset Nat × Finset Nat

def zero : Word I := fun _ => false
def changes (w : Word I) : Finset I :=
  if w none then ∅ else Finset.univ.filter fun i => w (some i)=true

def conjunction (ws : List (Word I)) (pins : Finset Nat) : Word I :=
  fun x => decide (∀ j∈pins,(ws.getD j zero) x=true)
def step (ws : List (Word I)) (r : Rule) : Word I :=
  fun x => conjunction ws r.1 x || conjunction ws r.2 x
def signal (ws : List (Word I)) (r : Rule) := ws++[step ws r]

def Covered (T : Finset (Finset I)) (ws : List (Word I)) := ∀ w∈ws,changes w∈T

private theorem read_cov {T : Finset (Finset I)} {ws : List (Word I)} (empty : ∅∈T)
    (cover : Covered T ws) (j : Nat) : changes (ws.getD j zero) ∈ T := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[j]? with
  | none => simpa [changes,zero] using empty
  | some w => exact cover w (List.mem_of_getElem? e)

theorem meet_small {T : Finset (Finset I)} {ws : List (Word I)} (empty : ∅∈T)
    (cover : Covered T ws) (s : Finset Nat) : ∃ a∈T,changes (conjunction ws s)⊆a := by
  by_cases h : ∀ j∈s,(ws.getD j zero) none=true
  · have yes : conjunction ws s none=true := decide_eq_true h
    exact ⟨∅,empty,by simp only [changes,yes,↓reduceIte,Finset.Subset.refl]⟩
  · push_neg at h
    obtain ⟨j,hj,h0⟩ := h
    have off : (ws.getD j zero) none=false := by simpa using h0
    refine ⟨_,read_cov empty cover j,?_⟩
    have no : ¬∀ i∈s,(ws.getD i zero) none=true := fun yes => Bool.noConfusion ((yes j hj).symm.trans off)
    intro i hi
    simp only [changes,conjunction,decide_eq_false no,Bool.false_eq_true,↓reduceIte,Finset.mem_filter,
      Finset.mem_univ,true_and,decide_eq_true_eq] at hi
    simp only [changes,off,Bool.false_eq_true,↓reduceIte,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hi j hj

theorem split_rule (ws : List (Word I)) (r : Rule) :
    changes (step ws r) ⊆ changes (conjunction ws r.1) ∪ changes (conjunction ws r.2) := by
  intro i hi
  cases a : conjunction ws r.1 none <;> cases b : conjunction ws r.2 none <;>
    simp_all [changes,step,Bool.or_eq_true]

theorem reaches (rs : List Rule) {T : Finset (Finset I)} {n : Nat} {ws : List (Word I)}
    (empty : ∅∈T) (cover : Covered T ws) (bound : Budget T n) :
    ∃ U : Finset (Finset I), ∅∈U ∧ Covered U (rs.foldl signal ws) ∧ Budget U (n+rs.length) := by
  induction rs generalizing T n ws with
  | nil => exact ⟨T,empty,cover,by simpa using bound⟩
  | cons r rs ih =>
    obtain ⟨a,ha,pa⟩ := meet_small empty cover r.1
    obtain ⟨b,hb,pb⟩ := meet_small empty cover r.2
    let z := changes (step ws r)
    have sub : z ⊆ a∪b := (split_rule ws r).trans (Finset.union_subset_union pa pb)
    have cov : Covered (insert z T) (signal ws r) := by
      intro w hw
      rcases List.mem_append.mp hw with hw|hw
      · exact Finset.mem_insert_of_mem (cover w hw)
      · obtain rfl := List.mem_singleton.mp hw
        exact Finset.mem_insert_self _ _
    obtain ⟨U,hU,done,cap⟩ := ih (Finset.mem_insert_of_mem empty) cov (add bound ha hb sub)
    exact ⟨U,hU,done,by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using cap⟩

theorem cost (rs : List Rule) (output : Finset Nat) (ws : List (Word I))
    (raw : ∀ w∈ws,(changes w).card≤1) :
    (changes (conjunction (rs.foldl signal ws) output)).card ≤ rs.length+1 := by
  classical
  let T := insert (∅ : Finset I) (ws.map changes).toFinset
  have h : Budget T 0 := initial (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · simp
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact raw w hw)
  have cv : Covered T ws := fun w hw => Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map.mpr ⟨w,hw,rfl⟩))
  obtain ⟨U,em,c,b⟩ := reaches rs (Finset.mem_insert_self _ _) cv h
  obtain ⟨a,ha,sub⟩ := meet_small em c output
  exact (Finset.card_le_card sub).trans (by simpa using single b ha)

#print axioms cost
end CoSensitivity4055
