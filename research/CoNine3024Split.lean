import PEqualNP.CoNine3024Data

namespace CoNine3024

def empty : State := ⟨[],0⟩

def indexed (g : Geometry) (k : Nat) (s : State) (i : Nat) : State :=
  (children g k s).getD i empty

/-- The gate choices of this state may each be checked separately. The number
    of children and the stopped-output test are verified in the kernel. -/
theorem exclude_children (g : Geometry) (k : Nat) (s : State) (n : Nat)
    (stop : live g s=false) (length : (children g k s).length ≤ n)
    (all : ∀ i : Fin n, search g k (indexed g k s i.val)=false) : search g (k+1) s=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [search,stop,Bool.false_or,Bool.and_eq_true] at h
  obtain ⟨w,mem,yes⟩ := List.any_eq_true.mp h.2
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp mem
  have no := all ⟨i,by omega⟩
  have ix : indexed g k s i=w := by
    simp only [indexed,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    exact eq
  change search g k (indexed g k s i)=false at no
  rw [ix] at no
  exact Bool.false_ne_true (no.symm.trans yes)

/-- Choose either orientation of two distinct active operands. -/
theorem pair_or {a b : Atom} {ws : List Atom} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) :
    (a,b)∈pairs ws ∨ (b,a)∈pairs ws := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    by_cases ax : a=x
    · subst a
      have bt : b∈xs := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨b,bt,rfl⟩))
    · by_cases bx : b=x
      · subst b
        have at' : a∈xs := (List.mem_cons.mp ha).resolve_left ax
        exact Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨a,at',rfl⟩))
      · rcases ih ((List.mem_cons.mp ha).resolve_left ax) ((List.mem_cons.mp hb).resolve_left bx) with ab|ba
        · exact Or.inl (List.mem_append_right _ ab)
        · exact Or.inr (List.mem_append_right _ ba)

end CoNine3024
