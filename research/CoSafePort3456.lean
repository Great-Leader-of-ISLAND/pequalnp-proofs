import Mathlib

namespace CoSafePort3456

variable {ι α : Type*}

/-- The port values on a physical row may be correlated. -/
def Safe (h : Set ι → Prop) (ports : α → Set ι) (b : ι) : Prop :=
  ∀ x, b ∈ ports x → h (ports x)

theorem restore (h : Set ι → Prop) (ports : α → Set ι)
    (mono : ∀ {A B : Set ι}, A ⊆ B → h A → h B)
    (T : Set ι) (hs : ∀ b ∈ T, Safe h ports b) (x : α) :
    h (ports x) ↔ (ports x ∩ T).Nonempty ∨ h (ports x \ T) := by
  classical
  constructor
  · intro hp
    by_cases hh : (ports x ∩ T).Nonempty
    · exact Or.inl hh
    · apply Or.inr
      have eq : ports x \ T = ports x := by
        ext b
        constructor
        · exact fun hb => hb.1
        · intro hb
          exact ⟨hb, fun ht => hh ⟨b, hb, ht⟩⟩
      rwa [eq]
  · rintro (⟨b, hx, ht⟩ | old)
    · exact hs b ht x hx
    · exact mono (A := ports x \ T) (B := ports x) (fun _ hb => hb.1) old

/-- Clearing every safe port extinguishes a row if at most one active
    uncertified port remains. Its sole survivor would otherwise itself be safe. -/
theorem cleared (h : Set ι → Prop) (ports : α → Set ι)
    (mono : ∀ {A B : Set ι}, A ⊆ B → h A → h B) (zero : ¬ h ∅)
    (x : α) (sparse : (ports x \ {b | Safe h ports b}).Subsingleton) :
    ¬ h (ports x \ {b | Safe h ports b}) := by
  classical
  let R := ports x \ {b | Safe h ports b}
  intro hit
  by_cases ex : R.Nonempty
  · obtain ⟨b,hb⟩ := ex
    have useful : Safe h ports b := by
      intro y hy
      apply mono (A := R) _ hit
      intro a ha
      have ab : a = b := sparse ha hb
      simpa only [ab] using hy
    exact hb.2 useful
  · have eq : R = ∅ := by
      ext b
      exact ⟨fun hb => (ex ⟨b,hb⟩).elim, fun hb => False.elim hb⟩
    exact zero (eq ▸ (show h R from hit))

def ImpliesPort (ports : α → Set ι) (a b : ι) : Prop :=
  ∀ y, a ∈ ports y → b ∈ ports y

theorem strongest (ports : α → Set ι) (T : Finset ι) :
    T.Nonempty → (∀ a ∈ T, ∀ b ∈ T,
      ImpliesPort ports a b ∨ ImpliesPort ports b a) →
    ∃ a ∈ T, ∀ b ∈ T, ImpliesPort ports a b := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro _ cmp
    by_cases hs : s.Nonempty
    · have liftmem : ∀ x ∈ s, x ∈ insert a s :=
        fun x hx => Finset.mem_insert_of_mem hx
      obtain ⟨b,hb,first⟩ := ih hs (fun u hu v hv =>
        cmp u (liftmem u hu) v (liftmem v hv))
      rcases cmp a (Finset.mem_insert_self _ _) b (liftmem b hb) with ab | ba
      · refine ⟨a,Finset.mem_insert_self _ _,?_⟩
        intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact fun _ h => h
        · exact fun y hy => first c hc y (ab y hy)
      · refine ⟨b,liftmem b hb,?_⟩
        intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact ba
        · exact first c hc
    · refine ⟨a,Finset.mem_insert_self _ _,?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact fun _ h => h
      · exact (hs ⟨c,hc⟩).elim

/-- The row type may be any chosen care set. Only unresolved, active port
    values need to be comparable under implication on these rows. -/
theorem cleared_chain [Fintype ι] (h : Set ι → Prop) (ports : α → Set ι)
    (mono : ∀ {A B : Set ι}, A ⊆ B → h A → h B) (zero : ¬ h ∅)
    (x : α) (cmp : ∀ a ∈ ports x \ {b | Safe h ports b},
      ∀ b ∈ ports x \ {c | Safe h ports c},
        ImpliesPort ports a b ∨ ImpliesPort ports b a) :
    ¬ h (ports x \ {b | Safe h ports b}) := by
  classical
  let R := ports x \ {b | Safe h ports b}
  let T : Finset ι := Finset.univ.filter (fun a => a ∈ R)
  have spec (a : ι) : a ∈ T ↔ a ∈ R := by simp [T]
  intro hit
  by_cases ex : R.Nonempty
  · obtain ⟨b,hb⟩ := ex
    obtain ⟨a,ha,first⟩ := strongest ports T ⟨b,(spec b).2 hb⟩
      (fun i hi j hj => cmp i ((spec i).1 hi) j ((spec j).1 hj))
    have good : Safe h ports a := by
      intro y hy
      apply mono (A := R) _ hit
      intro i hi
      exact first i ((spec i).2 hi) y hy
    exact ((spec a).1 ha).2 good
  · have eq : R = ∅ := by
      ext b
      exact ⟨fun hb => (ex ⟨b,hb⟩).elim, fun hb => False.elim hb⟩
    exact zero (eq ▸ (show h R from hit))

end CoSafePort3456
