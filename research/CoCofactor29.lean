import Mathlib

namespace CoCofactor29
abbrev Row := Fin 9 → Bool
def bitRow (n : Nat) (i : Fin 9) : Bool := n.testBit i.val
def target (x : Row) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
def rows : List Nat := [3,6,12,13,17,24,33,42,50,66,69,104,116,132,133,
  138,160,200,201,208,261,264,265,276,288,320,321,385,402]
def below (x y : Row) : Bool :=
  (x 0 == y 0) && decide (∀ i, x i = true → y i = true)
def control (x : Row) (r : Nat) : Bool :=
  let y := bitRow r
  (target x == target y) && (if target x then below y x else below x y)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem cover : ∀ x : Row, rows.any (control x) = true := by decide +kernel

def preserves (f : Row → Bool) := ∀ x y, below x y=true → f x=true → f y=true
theorem complete (f : Row → Bool) (pos : preserves f)
    (agree : ∀ r∈rows, f (bitRow r)=target (bitRow r)) : f=target := by
  funext x
  obtain ⟨r,hr,ok⟩ := List.any_eq_true.mp (cover x)
  have eq := agree r hr
  cases t : target x <;> simp [control,t] at ok
  · cases hx : f x with
    | false => rfl
    | true => exact Bool.noConfusion ((pos x _ ok.2 hx).symm.trans (eq.trans ok.1))
  · exact pos _ x ok.2 (eq.trans ok.1)

theorem signed (m : Nat) (op : Fin m → Bool) (a b : Fin m → Nat × Bool) (out : Nat × Bool)
    (v : Row → Nat → Bool)
    (before : ∀ i, (a i).1<10+i.val ∧ (b i).1<10+i.val) (output : out.1<10+m)
    (perm : let ok := fun t : Nat × Bool => t.2=true → t.1=0 ∨ t.1=9
            ok out ∧ ∀ i, ok (a i) ∧ ok (b i))
    (vars : ∀ x (i : Fin 9), v x i.val=x i) (z : ∀ x, v x 9=false)
    (step : ∀ x i, v x (10+i.val) =
      (if op i then ((v x (a i).1 ^^ (a i).2) && (v x (b i).1 ^^ (b i).2))
       else ((v x (a i).1 ^^ (a i).2) || (v x (b i).1 ^^ (b i).2)))) :
    preserves (fun x => v x out.1 ^^ out.2) := by
  intro x y xy
  have slice := Bool.and_eq_true_iff.mp xy
  have fixed : x 0=y 0 := by simpa using slice.1
  have mono := of_decide_eq_true slice.2
  have lit (t : Nat × Bool) (ok : t.2=true → t.1=0 ∨ t.1=9)
      (h : v x t.1=true → v y t.1=true) :
      (v x t.1 ^^ t.2)=true → (v y t.1 ^^ t.2)=true := by
    cases s : t.2 with
    | false => simpa [s] using h
    | true =>
      rcases ok s with a|a
      · have x0 : v x 0=x 0 := vars x 0
        have y0 : v y 0=y 0 := vars y 0
        simpa [a,x0,y0,fixed] using (id : (y 0 ^^ true)=true → (y 0 ^^ true)=true)
      · simp [a,z]
  have walk (n : Nat) (hn : n ≤ m) : ∀ j<10+n, v x j=true → v y j=true := by
    induction n with
    | zero =>
      intro j hj
      by_cases h : j<9
      · let i : Fin 9 := ⟨j,h⟩
        change v x i.val=true → v y i.val=true
        rw [vars,vars]
        exact mono i
      · have eq : j=9 := by omega
        simp [eq,z]
    | succ n ih =>
      let i : Fin m := ⟨n,by omega⟩
      have old := ih (by omega)
      intro j hj
      by_cases eq : j=10+n
      · subst j
        change v x (10+i.val)=true → v y (10+i.val)=true
        rw [step,step]
        have l := lit (a i) (perm.2 i).1 (old _ (before i).1)
        have r := lit (b i) (perm.2 i).2 (old _ (before i).2)
        cases oi : op i <;> simp [oi] <;> grind
      · exact old _ (by omega)
  exact lit out perm.1 (walk m (le_refl _) _ output)
end CoCofactor29
