import PEqualNP.CoPlaneRank972

namespace CoPortRank4139
open CoPlaneRank972 (represents occupied)

def data2 (a b : Fin 8) : List ℕ := [a.val,b.val]

def available3 (ms : List ℕ) : ℕ := ([6,5,3].filter (represents ms)).length

def localTest (a b : Fin 8) : Bool :=
  let ms := data2 a b
  !(represents ms 7) || decide (available3 ms < occupied ms)

theorem rank_table : ∀ a b : Fin 8, localTest a b = true := by decide +kernel

theorem two_slot_bound (a b : Fin 8) (loss : ℕ)
    (base : represents (data2 a b) 7 = true)
    (seen : loss ≤ available3 (data2 a b)) :
    loss + 1 ≤ occupied (data2 a b) := by
  have h := rank_table a b
  simp only [localTest,base,Bool.not_true,Bool.false_or,decide_eq_true_eq] at h
  omega

#print axioms two_slot_bound
end CoPortRank4139
