import PEqualNP.Co1593ProductStars
import PEqualNP.Co1593Generators

namespace Co1593NestedTrace

open Finset Co1593EmptyBudget Co1593StarCounting

variable {W V : Type*} [DecidableEq W] [DecidableEq V]

def empty (T : W→Scope V) (w : W) : Bool := decide (T w=∅)

def lowerGate (T : W→Scope V) (isAnd : Step W→Bool) (g : Step W) : Bool :=
  !isAnd g && !empty T g.left && !empty T g.right

def lowerProgram (T : W→Scope V) (isAnd : Step W→Bool) : List (Step W) → List (Join V)
  | [] => []
  | g::gs => if lowerGate T isAnd g then ⟨T g.left,T g.right⟩::lowerProgram T isAnd gs
             else lowerProgram T isAnd gs

inductive Trace (I : Finset W) (T : W→Scope V) (isAnd : Step W→Bool) :
    List (Step W) → Finset W → Prop where
  | start : Trace I T isAnd [] I
  | add {gs B} (pre : Trace I T isAnd gs B) (g : Step W)
      (left : g.left∈B) (right : g.right∈B) (fresh : g.out∉B)
      (scope : T g.out=if isAnd g then ∅ else T g.left∪T g.right) :
      Trace I T isAnd (g::gs) (insert g.out B)

theorem local_scope {I : Finset W} {T : W→Scope V} {isAnd : Step W→Bool}
    {gs B} (tr : Trace I T isAnd gs B) :
    ∀ g∈gs,T g.out=if isAnd g then ∅ else T g.left∪T g.right := by
  induction tr with
  | start => simp
  | add pre g l r new h ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl|old
    · exact h
    · exact ih _ old

theorem all_wires {I : Finset W} {T : W→Scope V} {isAnd : Step W→Bool}
    {gs B} (tr : Trace I T isAnd gs B) :
    ∀ g∈gs,g.left∈B ∧ g.right∈B := by
  induction tr with
  | start => simp
  | add pre g l r new h ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl|old
    · exact ⟨Finset.mem_insert_of_mem l,Finset.mem_insert_of_mem r⟩
    · exact ⟨Finset.mem_insert_of_mem (ih _ old).1,Finset.mem_insert_of_mem (ih _ old).2⟩

theorem back_inputs {I : Finset W} {T : W→Scope V} {isAnd : Step W→Bool}
    {gs B} (tr : Trace I T isAnd gs B) (s : Finset W) (valid : s⊆B) : finish gs s⊆I := by
  induction tr generalizing s with
  | start => exact valid
  | @add gs B pre g l r new h ih =>
    apply ih (before g s)
    by_cases hit : g.out∈s
    · rw [before,if_pos hit]
      refine Finset.insert_subset l (Finset.insert_subset r ?_)
      intro w hw
      exact (Finset.mem_insert.mp (valid (Finset.mem_of_mem_erase hw))).resolve_left
        (Finset.ne_of_mem_erase hw)
    · rw [before,if_neg hit]
      intro w hw
      exact (Finset.mem_insert.mp (valid hw)).resolve_left (fun e => hit (e ▸ hw))

theorem lower_builds {I : Finset W} {T : W→Scope V} {isAnd : Step W→Bool}
    {gs B} (tr : Trace I T isAnd gs B) :
    ∃ M, Build (insert ∅ (I.image T)) (lowerProgram T isAnd gs) M ∧
      ∅∈M ∧ ∀ w∈B,T w∈M := by
  induction tr with
  | start => exact ⟨_,Build.start,Finset.mem_insert_self _ _,
      fun w hw => Finset.mem_insert_of_mem (Finset.mem_image_of_mem T hw)⟩
  | @add gs B pre g l r new sc ih =>
    obtain ⟨M,prog,zero,known⟩ := ih
    by_cases paid : lowerGate T isAnd g=true
    · let j : Join V := ⟨T g.left,T g.right⟩
      have k : isAnd g=false := by cases hk : isAnd g <;> simp_all [lowerGate]
      have eq : T g.out=j.out := by simpa [k,j,Join.out] using sc
      refine ⟨insert j.out M,by simpa [lowerProgram,paid,j] using
        (Build.add prog j (known _ l) (known _ r)),Finset.mem_insert_of_mem zero,?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl|old
      · rw [eq]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (known _ old)
    · refine ⟨M,by simpa [lowerProgram,paid] using prog,zero,?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl|old
      · by_cases k : isAnd g=true
        · simpa [sc,k] using zero
        · have emptySide : T g.left=∅ ∨ T g.right=∅ := by
            by_contra! both
            have neL := Finset.nonempty_iff_ne_empty.mp both.1
            have neR := Finset.nonempty_iff_ne_empty.mp both.2
            simp [lowerGate,empty,k,neL,neR] at paid
          rcases emptySide with z|z
          · simpa [sc,k,z] using known _ r
          · simpa [sc,k,z] using known _ l
      · exact known _ old

theorem spending (T : W→Scope V) (isAnd : Step W→Bool) (gs : List (Step W)) (s : Finset W) :
    (∀ g∈gs,isAnd g=false → empty T g.left=false → empty T g.right=false → empty T g.out=false) →
    (lowerProgram T isAnd gs).length + births (empty T) gs s +
      (gs.map (other (empty T))).sum ≤ gs.length := by
  induction gs generalizing s with
  | nil => simp [lowerProgram,births]
  | cons g gs ih =>
    intro good
    have head := good g List.mem_cons_self
    have h := ih (before g s) (fun v hv => good v (List.mem_cons_of_mem _ hv))
    cases a : isAnd g <;> cases l : empty T g.left <;> cases r : empty T g.right <;>
      cases z : empty T g.out <;> by_cases seen : g.out∈s <;>
      simp [lowerProgram,lowerGate,births,birth,other,a,l,r,z,seen] at * <;> omega

end Co1593NestedTrace
