import Mathlib.Data.Finset.Union
import Mathlib.Tactic

namespace CoDelete4055

abbrev Rule := Finset Nat × Finset Nat
abbrev Wire (X : Type) := X → Bool
def off {X : Type} : Wire X := fun _ => false
def meet {X : Type} (bank : List (Wire X)) (s : Finset Nat) : Wire X :=
  fun x => decide (∀ i ∈ s, (bank.getD i off) x = true)
def add {X : Type} (bank : List (Wire X)) (g : Rule) : List (Wire X) :=
  bank ++ [fun x => meet bank g.1 x || meet bank g.2 x]
def bounds (n : Nat) (s : Finset Nat) : Prop := ∀ i ∈ s, i < n
def legal : Nat → List Rule → Prop
  | _, [] => True
  | n, g :: gs => bounds n g.1 ∧ bounds n g.2 ∧ legal (n+1) gs
def skips (v : Nat) : List Rule → Nat
  | [] => 0
  | g :: gs => (if v ∈ g.1 ∨ v ∈ g.2 then 1 else 0) + skips v gs

variable {X : Type}
private def Rep (Y : List (Wire X)) (w : Wire X) : Prop :=
  ∃ s, bounds Y.length s ∧ meet Y s = w
private def Sim (A Y : List (Wire X)) : Prop := ∀ w ∈ off :: A, Rep Y w

private theorem get_mem (A : List (Wire X)) (i : Nat) : A.getD i off ∈ off :: A := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : A[i]? with
  | none => simp
  | some w => exact List.mem_cons_of_mem _ (List.mem_of_getElem? e)

private theorem lift_meet {A Y : List (Wire X)} (sim : Sim A Y) (s : Finset Nat) :
    Rep Y (meet A s) := by
  classical
  have all (i : Nat) := sim _ (get_mem A i)
  choose r rb rv using all
  refine ⟨s.biUnion r, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, _, hij⟩ := Finset.mem_biUnion.mp hj
    exact rb i j hij
  · funext x
    apply Bool.eq_iff_iff.mpr
    simp only [meet, decide_eq_true_eq, Finset.mem_biUnion]
    constructor
    · intro h i hi
      rw [← rv i]
      exact decide_eq_true (fun j hj => h j ⟨i, hi, hj⟩)
    · intro h j hj
      obtain ⟨i, hi, hij⟩ := hj
      have hit := h i hi
      rw [← rv i] at hit
      exact (of_decide_eq_true hit) j hij

private theorem getD_before {α : Type} (xs ys : List α) (i : Nat) (d : α) (hi : i < xs.length) :
    (xs ++ ys).getD i d = xs.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem widen {Y : List (Wire X)} {w : Wire X} (hw : Rep Y w) (z : Wire X) :
    Rep (Y ++ [z]) w := by
  obtain ⟨s, hs, e⟩ := hw
  refine ⟨s, fun i hi => by have := hs i hi; simp only [List.length_append,List.length_singleton]; omega, ?_⟩
  rw [← e]
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [meet, decide_eq_true_eq]
  constructor <;> intro h i hi
  · simpa only [getD_before _ _ _ _ (hs i hi)] using h i hi
  · simpa only [getD_before _ _ _ _ (hs i hi)] using h i hi

private theorem last_rep (Y : List (Wire X)) (w : Wire X) : Rep (Y ++ [w]) w := by
  refine ⟨{Y.length}, ?_, ?_⟩
  · intro i hi
    have e := Finset.mem_singleton.mp hi
    subst i
    simp
  · funext x
    simp [meet]

private theorem extend {A Y : List (Wire X)} (sim : Sim A Y) {w : Wire X}
    (r : Rep Y w) : Sim (A ++ [w]) Y := by
  intro t ht
  rcases List.mem_cons.mp ht with h | h
  · exact sim _ (List.mem_cons.mpr (Or.inl h))
  · rcases List.mem_append.mp h with h | h
    · exact sim _ (List.mem_cons_of_mem _ h)
    · simp only [List.mem_singleton] at h
      subst t
      exact r

private theorem meet_dead {A : List (Wire X)} {v : Nat} (hv : A.getD v off = off)
    {s : Finset Nat} (h : v ∈ s) : meet A s = off := by
  funext x
  have no : ¬ (∀ i ∈ s, (A.getD i off) x = true) := by
    intro yes
    have bad := yes v h
    rw [hv] at bad
    exact Bool.noConfusion bad
  exact decide_eq_false no

private theorem tail_compile (v : Nat) (gs : List Rule) (t : Finset Nat)
    {A Y : List (Wire X)} (sim : Sim A Y) (hv : v < A.length) (hz : A.getD v off = off) :
    ∃ (rs : List Rule) (u : Finset Nat),
      rs.length + skips v gs = gs.length ∧ legal Y.length rs ∧
      bounds (Y.length + rs.length) u ∧ meet (rs.foldl add Y) u = meet (gs.foldl add A) t := by
  induction gs generalizing A Y with
  | nil =>
    obtain ⟨u, hu, eu⟩ := lift_meet sim t
    exact ⟨[], u, by simp [skips], trivial, by simpa using hu, eu⟩
  | cons g gs ih =>
    let w : Wire X := fun x => meet A g.1 x || meet A g.2 x
    have hv' : v < (add A g).length := by simp [add]; omega
    have hz' : (add A g).getD v off = off := (getD_before _ _ _ _ hv).trans hz
    by_cases dead : v ∈ g.1 ∨ v ∈ g.2
    · have rep : Rep Y w := by
        rcases dead with h | h
        · have e : w = meet A g.2 := by funext x; simp [w, meet_dead hz h, off]
          rw [e]
          exact lift_meet sim _
        · have e : w = meet A g.1 := by funext x; simp [w, meet_dead hz h, off]
          rw [e]
          exact lift_meet sim _
      have s' : Sim (add A g) Y := extend sim rep
      obtain ⟨rs, u, count, ok, bu, eu⟩ := ih s' hv' hz'
      refine ⟨rs, u, ?_, ok, bu, eu⟩
      simp only [skips, if_pos dead, List.length_cons]
      omega
    · obtain ⟨a, ba, ea⟩ := lift_meet sim g.1
      obtain ⟨b, bb, eb⟩ := lift_meet sim g.2
      let r : Rule := (a,b)
      have eY : add Y r = Y ++ [w] := by simp [add, r, w, ea, eb]
      have sim' : Sim (add A g) (add Y r) := by
        rw [eY]
        apply extend (fun f hf => widen (sim f hf) w)
        exact last_rep Y w
      obtain ⟨rs, u, count, ok, bu, eu⟩ := ih sim' hv' hz'
      refine ⟨r :: rs, u, ?_, ⟨ba, bb, ?_⟩, ?_, eu⟩
      · simp only [skips, if_neg dead, Nat.zero_add, List.length_cons]
        omega
      · simpa [add] using ok
      · simpa [add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bu

private theorem addr {Y : List (Wire X)} {w : Wire X} (h : w ∈ Y) :
    ∃ i, i < Y.length ∧ Y.getD i off = w := by
  induction Y with
  | nil => simp at h
  | cons a Y ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨i, hi, e⟩ := ih hm
      exact ⟨i+1, by simpa using hi, by simpa using e⟩

/-- On an arbitrary family of input rows where position v is zero, every distinct rule
that reads v in either conjunction arm can be removed. Gates and the final conjunction
of the new circuit have only backward references, including when the original did not. -/
theorem delete_readers (v : Nat) (gs : List Rule) (t : Finset Nat) (Y : List (Wire X))
    (hv : v < Y.length) (hz : Y.getD v off = off) :
    ∃ (rs : List Rule) (u : Finset Nat),
      rs.length + skips v gs = gs.length ∧ legal Y.length rs ∧
      bounds (Y.length + rs.length) u ∧ meet (rs.foldl add Y) u = meet (gs.foldl add Y) t := by
  apply tail_compile v gs t (A := Y) (Y := Y) _ hv hz
  intro w hw
  have find : ∃ i, i < Y.length ∧ Y.getD i off = w := by
    rcases List.mem_cons.mp hw with e | h
    · exact ⟨v,hv,hz.trans e.symm⟩
    · exact addr h
  obtain ⟨i, hi, e⟩ := find
  refine ⟨{i}, ?_, ?_⟩
  · intro j hj
    exact (Finset.mem_singleton.mp hj) ▸ hi
  · funext x
    apply Bool.eq_iff_iff.mpr
    simp only [meet, decide_eq_true_eq, Finset.mem_singleton, forall_eq, e]

end CoDelete4055
