import PEqualNP.CoBlockSlots4482
namespace CoAnchorMask4482
open CoBlockSlots4482

/-- Presence in at least one and at least two selected coordinate columns. -/
def levels {k : Nat} : List (BitVec k) → BitVec k × BitVec k
  | [] => (0,0)
  | a::xs =>
    let rest := levels xs
    (a ||| rest.1,(a &&& rest.1) ||| rest.2)

private theorem first {k : Nat} (cols : List (BitVec k)) (j : Fin k)
    (x : BitVec k) (m : x∈cols) (v : x.getLsbD j.val=true) :
    (levels cols).1.getLsbD j.val=true := by
  induction cols with
  | nil => simp at m
  | cons a xs ih =>
    simp only [levels,BitVec.getLsbD_or,Bool.or_eq_true]
    rcases List.mem_cons.mp m with e|e
    · exact Or.inl (e ▸ v)
    · exact Or.inr (ih e)

private theorem second {A : Type} {k : Nat} (cols : List A) (val : A→BitVec k) (j : Fin k)
    (a b : A) (ab : a≠b) (ma : a∈cols) (mb : b∈cols)
    (pa : (val a).getLsbD j.val=true) (pb : (val b).getLsbD j.val=true) :
    (levels (cols.map val)).2.getLsbD j.val=true := by
  induction cols with
  | nil => simp at ma
  | cons h t ih =>
    simp only [List.map_cons,levels,BitVec.getLsbD_or,BitVec.getLsbD_and,
      Bool.or_eq_true,Bool.and_eq_true]
    rcases List.mem_cons.mp ma with ah|tailA
    · subst h
      have tail := (List.mem_cons.mp mb).resolve_left (Ne.symm ab)
      exact Or.inl ⟨pa,first _ j _ (List.mem_map.mpr ⟨b,tail,rfl⟩) pb⟩
    rcases List.mem_cons.mp mb with bh|tailB
    · exact Or.inl ⟨bh ▸ pb,first _ j _ (List.mem_map.mpr ⟨a,tailA,rfl⟩) pa⟩
    · exact Or.inr (ih tailA tailB)

def mask {n : Nat} (width : BitVec (2^n)) (inc : Fin n → BitVec (2^n))
    (anchors : List (Fin n)) : BitVec (2^n) := width &&& (levels (anchors.map inc)).2

/-- A width mask can be shared by all states of the same width. Each
seven-coordinate anchor set produces its entire required block mask using
only seven word operations of each kind. -/
theorem needed {n : Nat} (width : BitVec (2^n)) (inc : Fin n → BitVec (2^n))
    (anchors : List (Fin n)) (digits : ∀i (j : Fin (2^n)), (inc i).getLsbD j.val=j.val.testBit i.val)
    (j : Fin (2^n)) (allowed : width.getLsbD j.val=true)
    (two : 2≤((members j)∩anchors.toFinset).card) :
    (mask width inc anchors).getLsbD j.val=true := by
  obtain ⟨a,ma,b,mb,ab⟩ := Finset.one_lt_card.mp two
  obtain ⟨av,aa⟩ := Finset.mem_inter.mp ma
  obtain ⟨bv,bb⟩ := Finset.mem_inter.mp mb
  have digit (x : Fin n) (m : x∈members j) : (inc x).getLsbD j.val=true := by
    rw [digits]
    exact (Finset.mem_filter.mp m).2
  have ge := second anchors inc j a b ab (List.mem_toFinset.mp aa) (List.mem_toFinset.mp bb)
    (digit a av) (digit b bv)
  simp [mask,BitVec.getLsbD_and,allowed,ge]

#print axioms needed
end CoAnchorMask4482
