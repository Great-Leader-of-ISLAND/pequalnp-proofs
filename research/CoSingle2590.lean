import PEqualNP.CoTwo2590

namespace CoSingle2590
open CoTwo2590

def row (n : Nat) : Row := ⟨n%1024,Nat.mod_lt _ (by decide)⟩
def drop (v : Fin 10) (s : Row) : Row := row (s.val &&& (1023-2^v.val))
def add (v : Fin 10) (s : Row) : Row := row (s.val ||| 2^v.val)
def below (s t : Row) := s.val &&& t.val=s.val
def maximalRows : Fin 15 → Row := ![50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
def exception : Fin 10 → Fin 2 → Fin 15 := ![![5,14],![9,12],![3,14],![5,12],![3,9],![3,12],![3,5],![5,9],![9,14],![12,14]]
def witness : Fin 10 → Fin 15 → Row := ![![50,84,104,116,138,0,208,276,386,402,522,548,554,770,0],![52,69,104,116,137,201,208,276,385,0,521,548,0,769,773],![50,73,104,0,138,201,208,274,385,402,521,546,554,770,0],![50,69,100,116,146,0,208,276,385,402,517,548,0,770,773],![42,69,104,0,138,201,193,261,385,0,521,548,554,770,773],![146,69,73,0,138,201,208,276,385,402,521,517,0,770,773],![50,261,42,0,138,0,146,276,385,402,521,548,554,770,773],![50,69,104,116,42,0,84,276,261,0,521,548,554,770,773],![50,69,104,116,138,201,208,52,137,0,521,548,554,522,0],![50,69,104,116,138,201,208,276,385,402,73,52,0,274,0]]
def neighbor : Fin 10 → Fin 3 → Fin 10 := ![![1,4,5],![0,2,6],![1,3,7],![2,4,8],![0,3,9],![0,7,8],![1,8,9],![2,5,9],![3,5,6],![4,6,7]]
def single (v : Fin 10) := row (2^v.val)

set_option maxRecDepth 8192 in
theorem rows : ∀ (v : Fin 10) (j : Fin 15), j≠exception v 0 → j≠exception v 1 →
    let r := witness v j
    below (drop v (maximalRows j)) r ∧ drop v (add v r)=drop v r ∧ F r=false ∧ F (add v r)=true ∧ x v (add v r)=true := by
  unfold below
  decide +kernel

theorem distinct : ∀ v : Fin 10,exception v 0≠exception v 1 := by decide +kernel

/-- If the one OR-reader of v has another operand b independent of v, there
are at most these two maximal independent assignments on which b is high. -/
theorem single_or (v : Fin 10) (b : Row → Bool) (tail : Row → Bool → Bool)
    (other : ∀ s,b s=b (drop v s)) (mono : ∀ s t,below s t → b s=true → b t=true)
    (fact : ∀ s,F s=tail (drop v s) (x v s || b s)) (j : Fin 15)
    (onRow : b (maximalRows j)=true) : j=exception v 0 ∨ j=exception v 1 := by
  by_contra! neither
  obtain ⟨incl,without,lo,hi,bit⟩ := rows v j neither.1 neither.2
  have on : b (witness v j)=true := mono _ _ incl ((other _).symm.trans onRow)
  have neg := fact (witness v j)
  have yes := fact (add v (witness v j))
  rw [lo,on,Bool.or_true] at neg
  rw [hi,bit,Bool.true_or,without] at yes
  exact Bool.false_ne_true (neg.trans yes.symm)

theorem singleRows : ∀ (v : Fin 10) (j : Fin 3),
    let r := single (neighbor v j)
    drop v r=r ∧ drop v (add v r)=r ∧ F r=false ∧ F (add v r)=true ∧ x v r=false := by
  decide +kernel

/-- All three singleton neighbors must activate the other AND operand. -/
theorem single_and (v : Fin 10) (b : Row → Bool) (tail : Row → Bool → Bool)
    (other : ∀ s,b s=b (drop v s)) (fact : ∀ s,F s=tail (drop v s) (x v s && b s))
    (j : Fin 3) : b (single (neighbor v j))=true := by
  obtain ⟨sr,ar,lo,hi,bit⟩ := singleRows v j
  cases e : b (single (neighbor v j)) with
  | true => rfl
  | false =>
    have atYes := other (add v (single (neighbor v j)))
    rw [ar,e] at atYes
    have a := fact (single (neighbor v j))
    have z := fact (add v (single (neighbor v j)))
    rw [lo,sr,bit,Bool.false_and] at a
    rw [hi,ar,atYes,Bool.and_false] at z
    exact (Bool.false_ne_true (a.trans z.symm)).elim

end CoSingle2590
