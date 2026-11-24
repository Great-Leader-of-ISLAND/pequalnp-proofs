import PEqualNP.CoBitBlock4482
namespace CoBlockIntervals4482
open CoBitBlock4482

/-- The bit at j of inc says whether this current wire belongs to candidate
block j. All candidate blocks are checked in parallel. -/
structure Col (k : Nat) where
  data : Mark
  inc : BitVec k

def lane {k} (d : Col k) (e f : Row) : BitVec k :=
  let A := bit d.data.1 e
  let B := bit d.data.2 e
  let C := bit d.data.1 f
  let D := bit d.data.2 f
  (if A != B || C != D then d.inc else BitVec.allOnes k) &&&
    (if A && !D then ~~~d.inc else BitVec.allOnes k)

def interval {k} (e f : Row) : List (Col k) → BitVec k
  | [] => BitVec.allOnes k
  | h::t => lane h e f &&& interval e f t

def cover {k} (cols : List (Col k)) : List (Row×Row) → BitVec k
  | [] => 0
  | h::t => interval h.1 h.2 cols ||| cover cols t

private theorem lane_bit {k} (x : Col k) (e f : Row) (j : Fin k) :
    (lane x e f).getLsbD j.val = (
      (!(bit x.data.1 e != bit x.data.2 e || bit x.data.1 f != bit x.data.2 f) ||
        x.inc.getLsbD j.val) &&
      (!(bit x.data.1 e && !(bit x.data.2 f)) || !(x.inc.getLsbD j.val))) := by
  unfold lane
  cases a : (bit x.data.1 e != bit x.data.2 e || bit x.data.1 f != bit x.data.2 f) <;>
    cases b : (bit x.data.1 e && !bit x.data.2 f) <;>
    simp only [a,b,ite_true,ite_false,Bool.false_eq_true,BitVec.getLsbD_and,
      BitVec.getLsbD_not,BitVec.getLsbD_allOnes,j.isLt,decide_true,Bool.true_and] <;>
    cases x.inc.getLsbD j.val <;> rfl

private theorem local_sound {a b c d x : Bool}
    (ok : ((!(a != b || c != d) || x) && (!(a && !d) || !x))=true) :
    (x=false → a=b ∧ c=d) ∧ (x=true → a=true → d=true) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> simp_all

theorem interval_sound {k} (e f : Row) (cols : List (Col k)) (j : Fin k)
    (hit : (interval e f cols).getLsbD j.val = true) : ∀ w∈cols,
      (w.inc.getLsbD j.val=false → bit w.data.1 e=bit w.data.2 e ∧
        bit w.data.1 f=bit w.data.2 f) ∧
      (w.inc.getLsbD j.val=true → bit w.data.1 e=true → bit w.data.2 f=true) := by
  induction cols with
  | nil => simp
  | cons a xs ih =>
    simp only [interval,BitVec.getLsbD_and,Bool.and_eq_true] at hit
    intro w hw
    rcases List.mem_cons.mp hw with rfl|m
    · exact local_sound (by rw [←lane_bit]; exact hit.1)
    · exact ih hit.2 w m

theorem cover_witness {k} (cols : List (Col k)) (pairs : List (Row×Row)) (j : Fin k)
    (hit : (cover cols pairs).getLsbD j.val=true) :
    ∃ e f : Row, ∀ w∈cols,
      (w.inc.getLsbD j.val=false → bit w.data.1 e=bit w.data.2 e ∧
        bit w.data.1 f=bit w.data.2 f) ∧
      (w.inc.getLsbD j.val=true → bit w.data.1 e=true → bit w.data.2 f=true) := by
  induction pairs with
  | nil => simp [cover] at hit
  | cons a t ih =>
    simp only [cover,BitVec.getLsbD_or,Bool.or_eq_true] at hit
    rcases hit with v|v
    · exact ⟨a.1,a.2,interval_sound _ _ _ _ v⟩
    · exact ih v

/-- A verified mask inclusion kills every slot required by the combinatorial
pigeonhole condition, without trusting the producer's interval choices. -/
theorem required_witness {k} (cols : List (Col k)) (pairs : List (Row×Row)) (must : BitVec k)
    (verified : must &&& cover cols pairs = must) (j : Fin k) (demand : must.getLsbD j.val=true) :
    ∃e f : Row, ∀w∈cols,
      (w.inc.getLsbD j.val=false → bit w.data.1 e=bit w.data.2 e ∧
        bit w.data.1 f=bit w.data.2 f) ∧
      (w.inc.getLsbD j.val=true → bit w.data.1 e=true → bit w.data.2 f=true) := by
  have eq := congrArg (fun s : BitVec k => s.getLsbD j.val) verified
  simp only [BitVec.getLsbD_and,demand,Bool.true_and] at eq
  exact cover_witness _ _ j eq

#print axioms required_witness
end CoBlockIntervals4482
