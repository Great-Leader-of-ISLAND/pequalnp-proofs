import Mathlib

namespace CoPlaneRank972

-- The four bit positions are the incident positive rows at one vertex.
def represents : List ℕ → ℕ → Bool
  | [], t => t == 0
  | a :: others, t =>
    represents others t || ((a &&& t) == a && represents others (t ^^^ a))

def three (a b c : Fin 16) : List ℕ := [a.val,b.val,c.val]

def available (ms : List ℕ) : ℕ := ([14,13,11,7].filter (represents ms)).length

def occupied (ms : List ℕ) : ℕ := (ms.filter (· != 0)).length

def rankTest (a b c : Fin 16) : Bool :=
  let ms := three a b c
  !(represents ms 15) || decide (available ms < occupied ms)

set_option maxHeartbeats 16000000 in
theorem local_rank : ∀ a b c : Fin 16, rankTest a b c = true := by decide +kernel

theorem loss_vs_slots (a b c : Fin 16) (loss : ℕ)
    (base : represents (three a b c) 15 = true)
    (seen : loss ≤ available (three a b c)) :
    loss + 1 ≤ occupied (three a b c) := by
  have h := local_rank a b c
  simp only [rankTest, base, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
  omega

end CoPlaneRank972
