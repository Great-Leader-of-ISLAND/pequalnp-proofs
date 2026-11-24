import PEqualNP.CoTightBlocks4482
namespace CoBitBlock4482

abbrev Bits := BitVec 258
abbrev Row := Fin 258
abbrev Mark := Bits × Bits  -- positive, negative endpoint columns
def bit (x : Bits) (i : Row) := x.getLsbD i.val
def avoid (z : Mark) (e : Bits) : Bits := e &&& ~~~(z.1 ^^^ z.2)
def exclusive (others : List Mark) : Bits := others.foldr avoid (BitVec.allOnes 258)

/-- Search for positive/negative endpoints that are comparable on every
column of the proposed block. Endpoint masks shrink by 258-bit operations. -/
def bad : List Mark → Bits → Bits → Bool
  | [],p,n => p != 0 && n != 0
  | w::ws,p,n => if p=0 ∨ n=0 then false else
      bad ws (p &&& ~~~w.1) n || bad ws (p &&& w.1) (n &&& w.2)

def invalid (inside outside : List Mark) :=
  let es := exclusive outside
  bad inside es es

private theorem has_bit {w : Bits} (ne : w ≠ 0) : ∃ i : Row, bit w i=true := by
  by_contra no
  apply ne
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases e : w.getLsbD i with
  | false => simp
  | true => exact (no ⟨⟨i,hi⟩,e⟩).elim

private theorem bit_and (a b : Bits) (i : Row) : bit (a &&& b) i = (bit a i && bit b i) := by
  simp only [bit,BitVec.getLsbD_and]

private theorem bit_not (a : Bits) (i : Row) : bit (~~~a) i = !(bit a i) := by
  simp only [bit,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]

private theorem bit_xor (a b : Bits) (i : Row) : bit (a ^^^ b) i = (Bool.xor (bit a i) (bit b i)) := by
  simp only [bit,BitVec.getLsbD_xor]

theorem bad_witness (ws : List Mark) (p n : Bits) (h : bad ws p n=true) :
    ∃ i j : Row, bit p i=true ∧ bit n j=true ∧
      ∀ w∈ws, bit w.1 i=true → bit w.2 j=true := by
  induction ws generalizing p n with
  | nil =>
    simp only [bad,Bool.and_eq_true,bne_iff_ne] at h
    obtain ⟨i,pi⟩ := has_bit h.1
    obtain ⟨j,nj⟩ := has_bit h.2
    exact ⟨i,j,pi,nj,by simp⟩
  | cons w ws ih =>
    by_cases stop : p=0 ∨ n=0
    · simp only [bad,if_pos stop,Bool.false_eq_true] at h
    simp only [bad,if_neg stop,Bool.or_eq_true] at h
    rcases h with l|r
    · obtain ⟨i,j,pi,nj,inside⟩ := ih _ _ l
      rw [bit_and,bit_not,Bool.and_eq_true] at pi
      refine ⟨i,j,pi.1,nj,?_⟩
      intro a m t
      rcases List.mem_cons.mp m with rfl|m
      · simp [t] at pi
      · exact inside a m t
    · obtain ⟨i,j,pi,nj,inside⟩ := ih _ _ r
      rw [bit_and,Bool.and_eq_true] at pi nj
      refine ⟨i,j,pi.1,nj.1,?_⟩
      intro a m t
      rcases List.mem_cons.mp m with rfl|m
      · exact nj.2
      · exact inside a m t

theorem outside_equal (others : List Mark) (i : Row) (h : bit (exclusive others) i=true) :
    ∀ w∈others, bit w.1 i = bit w.2 i := by
  induction others with
  | nil => simp
  | cons a others ih =>
    change bit (avoid a (exclusive others)) i=true at h
    rw [avoid,bit_and,bit_not,bit_xor,Bool.and_eq_true] at h
    intro w m
    rcases List.mem_cons.mp m with eq|m
    · subst w
      cases l : bit a.1 i <;> cases r : bit a.2 i <;> simp_all
    · exact ih h.1 w m

theorem invalid_witness (inside outside : List Mark) (h : invalid inside outside=true) :
    ∃ i j : Row, (∀ w∈outside, bit w.1 i=bit w.2 i ∧ bit w.1 j=bit w.2 j) ∧
      ∀ w∈inside, bit w.1 i=true → bit w.2 j=true := by
  obtain ⟨i,j,pi,nj,order⟩ := bad_witness _ _ _ h
  exact ⟨i,j,fun w m => ⟨outside_equal outside i pi w m,outside_equal outside j nj w m⟩,order⟩

#print axioms invalid_witness
end CoBitBlock4482
