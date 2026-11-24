import PEqualNP.CoFormula1963Mass
import PEqualNP.CoFormula1963Frequency
import PEqualNP.CoFormula1963Packed

namespace CoFormula1963Flags
open CoFormula1963Geometry CoFormula1963Protocol CoFormula1963Private CoFormula1963Link
open CoFormula1963Area CoFormula1963Packed
abbrev Col := CoFormula1963Link.Y

def delta : Fin 4 → V := ![0,1,3,9]
theorem point_inc : ∀ p : V, ∀ i : Fin 4, inc p (p-delta i) := by decide +kernel
theorem line_inc : ∀ l : V, ∀ i : Fin 4, inc (l+delta i) l := by decide +kernel

def flag (v : X) (i : Fin 4) : E := match v with
  | .inl p => ⟨(p,p-delta i),point_inc p i⟩
  | .inr l => ⟨(l+delta i,l),line_inc l i⟩

def opposite (v : X) (i : Fin 4) : X := match v with
  | .inl p => .inr (p-delta i)
  | .inr l => .inl (l+delta i)

theorem pos_ends (v : X) (i : Fin 4) (u : X) (h : pos (flag v i) u = true) :
    u = v ∨ u = opposite v i := by
  cases v <;> cases u <;> simp_all [pos,flag,opposite] <;> exact of_decide_eq_true h

def pack (f : Fin 4 → Bool) :=
  CoFormula1963Frequency.four (f 0) (f 1) (f 2) (f 3)

theorem bit_table : ∀ a b c d : Bool, ∀ i : Fin 4,
    (CoFormula1963Frequency.four a b c d).testBit i = ![a,b,c,d] i := by decide +kernel

theorem bit_pack (f : Fin 4 → Bool) (i : Fin 4) : (pack f).testBit i = f i := by
  unfold pack
  rw [bit_table]
  fin_cases i <;> rfl

theorem pack_lt (f : Fin 4 → Bool) : pack f < 16 := by
  have bounds : ∀ a b c d : Bool, CoFormula1963Frequency.four a b c d < 16 := by decide +kernel
  exact bounds _ _ _ _

def mask (v : X) (r : Rect X E Col) : ℕ := pack (fun i => decide (flag v i ∈ r.rows))
def mandatory (v : X) (y : Col) : ℕ := pack (fun i => neg y (opposite v i))
def active (y : Col) (r : Rect X E Col) := decide (y∈r.cols)
def bucket (t : Expr X) (v : X) := (rs t).filter (fun r => r.label = v)
def masks (t : Expr X) (v : X) := (bucket t v).map (mask v)
def used (t : Expr X) (v : X) (y : Col) := unionAt (mask v) (active y) (bucket t v)

theorem cells (v : X) (y : Col) (rr : List (Rect X E Col)) (i : Fin 4) :
    cnt (mask v) (active y) rr i = multiplicity (flag v i) y rr := by
  induction rr with
  | nil => rfl
  | cons r rr ih =>
    change (if active y r && (mask v r).testBit i then 1 else 0) +
        cnt (mask v) (active y) rr i = hits (flag v i) y r + multiplicity (flag v i) y rr
    rw [ih]
    by_cases p : flag v i∈r.rows <;> by_cases q : y∈r.cols <;>
      simp [active,mask,bit_pack,hits,p,q]

theorem filter_le (v : X) (y : Col) (e : E) (rr : List (Rect X E Col)) :
    multiplicity e y (rr.filter (fun r => r.label = v)) ≤ multiplicity e y rr := by
  induction rr with
  | nil => rfl
  | cons r rr ih =>
    by_cases z : r.label=v
    · simpa [CoFormula1963Protocol.multiplicity,z] using Nat.add_le_add_left ih (hits e y r)
    · calc
        _ = multiplicity e y (rr.filter (fun w => w.label=v)) := by simp [z]
        _ ≤ multiplicity e y rr := ih
        _ ≤ _ := by change _ ≤ hits e y r + multiplicity e y rr; omega

theorem selection (t : Expr X) (v : X) (y : Col) : Selection (masks t v) (used t v y) := by
  apply from_cells (mask v) (active y) (bucket t v) (fun _ _ => pack_lt _)
  intro i
  rw [cells]
  exact (filter_le v y (flag v i) (rs t)).trans (by rw [exact_cell])

theorem mandatory_le (t : Expr X) (accept : ∀ e : E, t.eval (pos e) = true)
    (reject : ∀ y : Col, t.eval (neg y) = false) (v : X) (y : Col) (i : Fin 4)
    (forced : (mandatory v y).testBit i = true) : (used t v y).testBit i = true := by
  have on : neg y (opposite v i) = true := by simpa [mandatory,bit_pack] using forced
  obtain ⟨r,mem,rr,cc⟩ := present (flag v i) y (rs t) (by rw [exact_cell]; decide)
  obtain ⟨p,n⟩ := partition_sound pos neg t Finset.univ Finset.univ
    (fun x _ => accept x) (fun x _ => reject x) r mem (flag v i) rr y cc
  have label : r.label=v := by
    rcases pos_ends v i _ p with correct | oppositeLabel
    · exact correct
    · rw [oppositeLabel,on] at n
      contradiction
  apply (test_count (mask v) (active y) (bucket t v) i).mpr
  rw [cells]
  exact CoFormula1963Link.positive (flag v i) y (bucket t v) r
    (List.mem_filter.mpr ⟨mem,by simpa [label]⟩) ⟨rr,cc⟩

theorem bit_inclusion : ∀ u m : Fin 16, (∀ i : Fin 4, m.val.testBit i = true →
    u.val.testBit i = true) → u.val &&& m.val = m.val := by decide +kernel

theorem forced_subset (t : Expr X) (accept : ∀ e : E, t.eval (pos e) = true)
    (reject : ∀ y : Col, t.eval (neg y) = false) (v : X) (y : Col) :
    used t v y &&& mandatory v y = mandatory v y :=
  bit_inclusion ⟨used t v y,union_small _ _ _ (fun _ _ => pack_lt _)⟩
    ⟨mandatory v y,pack_lt _⟩ (mandatory_le t accept reject v y)

#print axioms selection
#print axioms forced_subset
end CoFormula1963Flags
