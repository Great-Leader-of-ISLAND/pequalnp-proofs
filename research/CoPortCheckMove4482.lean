import PEqualNP.CoPortFrontier4482

namespace CoPortFrontier4482
open CoPortRoots4482 CoPortTrace4482 CoPortCut4482 CoPortEdgeRows4482 CoBitBlock4482

abbrev Entry := W × Mark
def authentic (xs : List Entry) := ∀ e∈xs,e.2=mark e.1
def words (xs : List Entry) := xs.map Prod.fst
def obs (xs : List Entry) := xs.map Prod.snd

theorem annotation {xs : List Entry} (h : authentic xs) :
    obs xs=(words xs).map mark := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have tail := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    change a.2 :: obs xs=mark a.1 :: (words xs).map mark
    rw [ha,tail]

def make (d : Bool) (a b : Entry) : Entry :=
  (join d a.1 b.1,if d then (a.2.1 ||| b.2.1,a.2.2 ||| b.2.2)
    else (a.2.1 &&& b.2.1,a.2.2 &&& b.2.2))

def removeEntry (xs : List Entry) (w : W) (d : Bool) :=
  if d then xs.filter fun e => e.1!=w else xs

def move (xs : List Entry) (d : Bool) (a b : Entry) (da db : Bool) :=
  make d a b :: removeEntry (removeEntry xs a.1 da) b.1 db

theorem value_remove (xs : List Entry) (w : W) (d : Bool) :
    words (removeEntry xs w d)=eraseIf (words xs) w d := by
  cases d
  · rfl
  · induction xs with
    | nil => rfl
    | cons t ts ih =>
      cases h : t.1!=w <;> simp_all [words,removeEntry,eraseIf,List.filter_cons]

theorem value_move (xs : List Entry) (d : Bool) (a b : Entry) (da db : Bool) :
    words (move xs d a b da db)=successor (words xs) d a.1 b.1 da db := by
  change (join d a.1 b.1)::words (removeEntry (removeEntry xs a.1 da) b.1 db)=_
  rw [value_remove,value_remove]
  rfl

theorem authentic_remove {xs : List Entry} (h : authentic xs) (w : W) (d : Bool) :
    authentic (removeEntry xs w d) := by
  cases d
  · exact h
  · intro t m
    exact h t (List.mem_filter.mp m).1

theorem authentic_move {xs : List Entry} (h : authentic xs) (d : Bool) {a b : Entry}
    (ha : a∈xs) (hb : b∈xs) (da db : Bool) : authentic (move xs d a b da db) := by
  intro e he
  rcases List.mem_cons.mp he with eq|old
  · subst e
    change (if d then _ else _)=mark (join d a.1 b.1)
    rw [mark_gate,←h a ha,←h b hb]
  · exact authentic_remove (authentic_remove h a.1 da) b.1 db e old

def admitted (ys : List Entry) := cov (obs ys)==BitVec.allOnes 258

theorem may_move {xs : List Entry} {k : Nat} (auth : authentic xs)
    (room : 6<(words xs).toFinset.card) (p : Reach (k+1) (words xs)) :
    ∃ a∈xs, ∃ b∈xs,∃ d da db : Bool,
      a.1≠b.1 ∧ join d a.1 b.1∉words xs ∧ admitted (move xs d a b da db)=true ∧
      Reach k (words (move xs d a b da db)) := by
  obtain ⟨u,hu,v,hv,d,da,db,ne,fresh,child⟩ := children room p
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hu
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hv
  rw [←value_move xs d a b da db] at child
  refine ⟨a,ha,b,hb,d,da,db,ne,fresh,?_,child⟩
  exact beq_iff_eq.mpr ((congrArg cov (annotation (authentic_move auth d ha hb da db))).trans (covered child))

#print axioms may_move
end CoPortFrontier4482
