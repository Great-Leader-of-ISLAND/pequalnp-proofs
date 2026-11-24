import Mathlib

namespace CoPeelingBounds

def den (q N k : ℝ) : ℝ := k^2-(q+2)*k+N

/-- Algebraic form of the moment estimate after the incidence double count. -/
theorem projected_moment (q N K b : ℝ) (hN : N=q^2+q+1)
    (cs : ((q+1)*K-N)^2 ≤ (N-b)*den q N K) :
    b*den q N K ≤ q*(N-K)*K := by
  calc
    b*den q N K ≤ N*den q N K-((q+1)*K-N)^2 := by nlinarith only [cs]
    _ = q*(N-K)*K := by rw [hN]; unfold den; ring

/-- The same constant works for larger surviving sets; no division is necessary. -/
theorem uniform_den (q N k K : ℝ) (order : k≤K) (product : N≤k*K) :
    K*den q N k ≤ k*den q N K := by
  have prod := mul_nonneg (sub_nonneg.mpr order) (sub_nonneg.mpr product)
  unfold den
  nlinarith only [prod]

def pointCount (q : ℕ) := q^2+q+1
def retained (q : ℕ) := q*(Nat.sqrt q+3)
def removed (q : ℕ) := pointCount q-retained q
def natDen (q : ℕ) := retained q ^ 2 + pointCount q - (q+2)*retained q
def thin (q : ℕ) := q * removed q * retained q / natDen q
def circuitLB (q : ℕ) := 2*pointCount q+removed q-1-thin q

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem small_arithmetic : ∀ i : Fin 88, let q := i.val+201
    0 < removed q ∧ removed q < pointCount q ∧ pointCount q ≤ retained q ^ 2 ∧
    pointCount q < (q+1)*retained q ∧ (q+2)*retained q < retained q^2+pointCount q ∧
    q*pointCount q ≤ 100*circuitLB q := by decide +kernel

theorem interval (q size : ℕ) (h201 : 201≤q) (h288 : q≤288)
    (h : circuitLB q ≤ size) : q*pointCount q ≤ 100*size := by
  let i : Fin 88 := ⟨q-201,by omega⟩
  have arithmetic := small_arithmetic i
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ (q-201+201)*pointCount (q-201+201) ≤
    100*circuitLB (q-201+201) at arithmetic
  have num := arithmetic.2.2.2.2.2
  rw [Nat.sub_add_cancel h201] at num
  omega

/-- Final arithmetic for q=289, under the two stopping alternatives in the note. -/
theorem final289 (s : ℕ)
    (endCases : 2*83811+79318-1-4720 ≤ s ∨ 4*(83811-4720)-2*5431 ≤ s) :
    289*83811 ≤ 100*s := by omega

end CoPeelingBounds
