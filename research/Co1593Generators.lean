import PEqualNP.Co1593EmptyBudget

namespace Co1593EmptyBudget

open Finset

variable {W : Type*} [DecidableEq W]

def finish : List (Step W) → Finset W → Finset W
  | [],s => s
  | g::gs,s => finish gs (before g s)

def generators (e : W→Bool) : List (Step W) → Finset W → List (Step W)
  | [],_ => []
  | g::gs,s => if birth e g s=1 then g::generators e gs (before g s)
               else generators e gs (before g s)

theorem generator_count (e : W→Bool) (gs : List (Step W)) (s : Finset W) :
    (generators e gs s).length = births e gs s := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    by_cases actual : g.out∈s ∧ e g.out=true ∧ e g.left=false ∧ e g.right=false
    · simp [generators,births,birth,actual,ih,Nat.add_comm]
    · simp [generators,births,birth,actual,ih]

theorem member_data (e : W→Bool) (gs : List (Step W)) (s : Finset W)
    (g : Step W) (h : g∈generators e gs s) :
    g∈gs ∧ e g.out=true ∧ e g.left=false ∧ e g.right=false := by
  induction gs generalizing s with
  | nil => simp [generators] at h
  | cons a gs ih =>
    by_cases paid : birth e a s=1
    · simp only [generators,paid,if_true,List.mem_cons] at h
      rcases h with rfl|old
      · have pos : g.out∈s ∧ e g.out=true ∧ e g.left=false ∧ e g.right=false := by
          by_contra no
          simp [birth,no] at paid
        exact ⟨List.mem_cons_self,pos.2⟩
      · obtain ⟨inside,rest⟩ := ih (before a s) old
        exact ⟨List.mem_cons_of_mem _ inside,rest⟩
    · have old : g∈generators e gs (before a s) := by simpa [generators,paid] using h
      obtain ⟨inside,rest⟩ := ih _ old
      exact ⟨List.mem_cons_of_mem _ inside,rest⟩

def op (isAnd a b : Bool) := if isAnd then a && b else a || b

def novel (pair sx sy : W→Bool) (w : W) : Prop := pair w=true ∧ sx w=false ∧ sy w=false

def crosses (sx sy : W→Bool) (g : Step W) : Prop :=
  (sx g.left=true ∧ sy g.right=true) ∨ (sy g.left=true ∧ sx g.right=true)

private theorem gate_table : ∀ k p q a b c d : Bool,
    op k p q=true → op k a b=false → op k c d=false →
    (p=true ∧ a=false ∧ c=false) ∨ (q=true ∧ b=false ∧ d=false) ∨
    k=true ∧ ((a=true ∧ d=true) ∨ (c=true ∧ b=true)) := by decide

theorem produces {e pair sx sy : W→Bool} {isAnd : Step W→Bool}
    (nonemptyX : ∀ w,sx w=true → e w=false)
    (nonemptyY : ∀ w,sy w=true → e w=false)
    (gs : List (Step W)) (s : Finset W)
    (sem : ∀ g∈gs, ∀ b∈[pair,sx,sy], b g.out=op (isAnd g) (b g.left) (b g.right))
    (safe : ∀ g∈gs,isAnd g=true → e g.out=true)
    (tracked : ∃ w∈s,novel pair sx sy w) :
    (∃ g∈generators e gs s,crosses sx sy g) ∨ (∃ w∈finish gs s,novel pair sx sy w) := by
  induction gs generalizing s with
  | nil => exact Or.inr tracked
  | cons g gs ih =>
    have sh := sem g List.mem_cons_self
    have sg := safe g List.mem_cons_self
    have tail := ih (before g s) (fun v hv => sem v (List.mem_cons_of_mem _ hv))
      (fun v hv => safe v (List.mem_cons_of_mem _ hv))
    have forward (pass : ∃ w∈before g s,novel pair sx sy w) :
        (∃ v∈generators e (g::gs) s,crosses sx sy v) ∨
        ∃ w∈finish (g::gs) s,novel pair sx sy w := by
      rcases tail pass with ⟨v,hv,hc⟩|hx
      · refine Or.inl ⟨v,?_,hc⟩
        unfold generators
        split <;> simp_all
      · exact Or.inr hx
    obtain ⟨w,hw,nw⟩ := tracked
    by_cases same : w=g.out
    · subst w
      have pick := gate_table (isAnd g) (pair g.left) (pair g.right)
        (sx g.left) (sx g.right) (sy g.left) (sy g.right)
        (by rw [←sh pair (by simp)]; exact nw.1)
        (by rw [←sh sx (by simp)]; exact nw.2.1)
        (by rw [←sh sy (by simp)]; exact nw.2.2)
      rcases pick with nl|nr|⟨andGate,cr⟩
      · exact forward ⟨g.left,by simp [before,hw],nl⟩
      · exact forward ⟨g.right,by simp [before,hw],nr⟩
      · have live : birth e g s=1 := by
          rcases cr with ⟨a,b⟩|⟨a,b⟩
          · simp [birth,hw,sg andGate,nonemptyX _ a,nonemptyY _ b]
          · simp [birth,hw,sg andGate,nonemptyY _ a,nonemptyX _ b]
        exact Or.inl ⟨g,by simp [generators,live],cr⟩
    · apply forward
      refine ⟨w,?_,nw⟩
      by_cases hit : g.out∈s
      · exact (by simp [before,hit,same,hw])
      · simpa [before,hit] using hw

end Co1593EmptyBudget
