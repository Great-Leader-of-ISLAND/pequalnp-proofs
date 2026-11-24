import PEqualNP.CoNine3024Perm

namespace CoNine3024.Memo

structure Table where
  count : Nat
  state : Nat → State
  slot : State → Nat

def valid (g : Geometry) (k : Nat) (t : Table) : Prop := ∀i<t.count,search g k (t.state i)=false

def matched (t : Table) (s : State) : Bool :=
  let i := t.slot s
  decide (i<t.count) && s.spent==(t.state i).spent && s.wires.isPerm (t.state i).wires

theorem matched_false {g k t s} (proven : valid g k t) (h : matched t s=true) : search g k s=false := by
  unfold matched at h
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.isPerm_iff] at h
  apply Bool.eq_false_iff.mpr
  intro yes
  have contradiction := Reorder.search_forward g k ⟨h.1.2,h.2⟩ yes
  exact Bool.false_ne_true ((proven _ h.1.1).symm.trans contradiction)

def node (g : Geometry) (k : Nat) (table : Table) (s : State) : Bool :=
  !(live g s) && (!(safe s) || (children g k s).all fun q =>
    if k=0 then !(live g q) else matched table q)

theorem node_false {g k t s} (proved : valid g k t) (h : node g k t s=true) : search g (k+1) s=false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  simp only [node,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  simp only [search,Bool.or_eq_true,Bool.and_eq_true] at yes
  rcases yes with done|⟨budget,m⟩
  · exact Bool.false_ne_true (h.1.symm.trans done)
  rcases h.2 with unaffordable|checked
  · exact Bool.false_ne_true (unaffordable.symm.trans budget)
  obtain ⟨q,hq,endgame⟩ := List.any_eq_true.mp m
  have seen := List.all_eq_true.mp checked q hq
  by_cases z : k=0
  · subst k
    change live g q=true at endgame
    simpa [endgame] using seen
  · have ch : matched t q=true := by simpa [z] using seen
    exact Bool.false_ne_true ((matched_false proved ch).symm.trans endgame)

def allAt (f : Nat → Bool) (lo : Nat) : Nat → Bool
  | 0 => true
  | n+1 => f (lo+n) && allAt f lo n

theorem allAt_mem {f : Nat→Bool} {start n} (h : allAt f start n=true)
    (i : Nat) (lo : start ≤ i) (hi : i < start+n) : f i=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [allAt,Bool.and_eq_true] at h
    by_cases e : i=start+n
    · simpa [e] using h.1
    · exact ih h.2 (by omega)

theorem allAt_join {f : Nat→Bool} {s a b} (h1 : allAt f s a=true) (h2 : allAt f (s+a) b=true) :
    allAt f s (a+b)=true := by
  induction b with
  | zero => simpa using h1
  | succ b ih =>
    simp only [allAt,Bool.and_eq_true] at h2
    simp only [Nat.add_succ,allAt,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h2.1,ih h2.2⟩

theorem layer {g k next curr} (old : valid g k next)
    (checked : allAt (fun i => node g k next (curr.state i)) 0 curr.count=true) : valid g (k+1) curr := by
  intro i hi
  exact node_false old (allAt_mem checked i (by omega) (by simpa using hi))

end CoNine3024.Memo
