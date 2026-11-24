import Mathlib

namespace CoSingleUse4482

abbrev Input := Fin 9 → Bool

def graph (x : Input) : Bool :=
  ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun t =>
    x (Fin.ofNat 9 (t / 10)) && x (Fin.ofNat 9 (t % 10))

def single (v : Fin 9) : Input := fun j => decide (j = v)
def insert (x : Fin 9) (a : Input) : Input := fun j => if j = x then true else a j

/-- Actual rows of the nine-vertex graph. The second point u can be v. -/
theorem square_free_witness : ∀ x v : Fin 9, x ≠ v → ∃ u : Fin 9,
    u ≠ x ∧ graph (insert u (single v)) = false ∧
      graph (insert x (insert u (single v))) = true := by decide +kernel

/-- If all influence of x on the answer passes through x OR y, a monotone y
    tests false on every other singleton. The decoder using the unaltered raw
    coordinates and the port may be arbitrary. -/
theorem only_or (x : Fin 9) (y : Input → Bool)
    (mono : ∀ a b : Input, (∀ j, a j = true → b j = true) → y a = true → y b = true)
    (through : ∀ a b : Input, (∀ j, j ≠ x → a j = b j) →
      (a x || y a) = (b x || y b) → graph a = graph b)
    (v : Fin 9) (ne : x ≠ v) : y (single v) = false := by
  cases h : y (single v) with
  | false => rfl
  | true =>
    obtain ⟨u, _, low, high⟩ := square_free_witness x v ne
    let a := insert u (single v)
    have ya : y a = true := by
      refine mono (single v) a ?_ h
      intro j hj
      by_cases eq : j = u <;> simp [a,insert,eq,hj]
    have same := through a (insert x a) (by
      intro j nj
      simp [insert,nj]) (by simp [insert,ya])
    change graph a = false at low
    change graph (insert x a) = true at high
    rw [low,high] at same
    contradiction

theorem single_false (v : Fin 9) : graph (single v) = false := by
  revert v
  decide +kernel

/-- A sole AND reader must test true on each neighbor singleton. A separate
    hypothesis identifies the partner as independent of x. -/
theorem only_and (x : Fin 9) (y : Input → Bool)
    (ignores : ∀ a : Input, y (insert x a) = y a)
    (through : ∀ a b : Input, (∀ j, j ≠ x → a j = b j) →
      (a x && y a) = (b x && y b) → graph a = graph b)
    (v : Fin 9) (edge : graph (insert x (single v)) = true) : y (single v) = true := by
  cases h : y (single v) with
  | true => rfl
  | false =>
    have same := through (single v) (insert x (single v)) (by
      intro j nj
      simp [insert,nj]) (by simp [ignores,h])
    rw [single_false,edge] at same
    contradiction

#print axioms square_free_witness
#print axioms only_or
#print axioms only_and
end CoSingleUse4482
