import PEqualNP.Co4358Syntax

namespace CoNum4358

def Marked.ordered (r : Marked) : Marked :=
  if r.1.b < r.1.a then (⟨r.1.isOr,r.1.b,r.1.a⟩,(r.2.2,r.2.1)) else r

theorem ordered_le (r : Marked) : (Marked.ordered r).1.a ≤ (Marked.ordered r).1.b := by
  unfold Marked.ordered
  split <;> simp only <;> omega

theorem ordered_lt (r : Marked) (diff : r.1.a ≠ r.1.b) :
    (Marked.ordered r).1.a < (Marked.ordered r).1.b := by
  unfold Marked.ordered
  split <;> simp only <;> omega

theorem ordered_allowed {p q : Nat} {r : Marked} (h : Allowed p q r) :
    Allowed p q (Marked.ordered r) := by
  unfold Marked.ordered
  split
  · exact ⟨h.2,h.1⟩
  · exact h

private theorem op_comm (k a b : Bool) : op k a b = op k b a := by
  cases k <;> cases a <;> cases b <;> rfl

theorem ordered_gate (r : Marked) (w : List Bool) :
    (Marked.ordered r).1.val w=r.1.val w := by
  unfold Marked.ordered
  split
  · exact op_comm _ _ _
  · rfl

theorem ordered_mark (r : Marked) (w : List Bool) :
    Marked.val (Marked.ordered r) w=Marked.val r w := by
  unfold Marked.ordered
  split
  · exact op_comm _ _ _
  · rfl

theorem ordered_reader (r : Marked) : (Marked.ordered r).1.reads2=r.1.reads2 := by
  unfold Marked.ordered
  split
  · obtain ⟨⟨k,a,b⟩,m⟩ := r
    by_cases ea : a=2 <;> by_cases eb : b=2 <;>
      simp_all [Gate.reads2,List.contains_iff_mem]
  · rfl

theorem ordered_ordinary (ps : List Marked) (w : List Bool) :
    ordinary ((ps.map Marked.ordered).map Prod.fst) w=ordinary (ps.map Prod.fst) w := by
  induction ps generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.map_cons,ordinary,List.foldl_cons,ordered_gate] using ih (w++[x.1.val w])

theorem ordered_raised (ps : List Marked) (w : List Bool) :
    raised (ps.map Marked.ordered) w=raised ps w := by
  induction ps generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.map_cons,raised,List.foldl_cons,ordered_mark] using ih (w++[Marked.val x w])

theorem ordered_count (ps : List Marked) :
    (((ps.map Marked.ordered).map Prod.fst).filter Gate.reads2).length =
    ((ps.map Prod.fst).filter Gate.reads2).length := by
  induction ps with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.filter_cons,ordered_reader]
    split <;> simp [ih]

end CoNum4358
