import PEqualNP.CoCofactor29
namespace CoCofactor29

def extreme (r : Nat) (x : Row) : Bool :=
  let y := bitRow r
  decide (x=y) || (if target y then !(below x y && target x) else !(below y x && !target x))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem extremal : rows.all (fun r => decide (∀ x : Row, extreme r x=true)) = true := by decide +kernel

theorem target_mono : preserves target := by
  intro x y h
  have m := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  have step (a b : Fin 9) : x a && x b=true → y a && y b=true := by
    simp only [Bool.and_eq_true]
    rintro ⟨p,q⟩
    exact ⟨m a p,m b q⟩
  simp only [target,Bool.or_eq_true]
  grind

def flipped (r : Nat) (x : Row) := if x=bitRow r then !(target x) else target x

theorem flip_preserves (r : Nat) (hr : r∈rows) : preserves (flipped r) := by
  have tests := of_decide_eq_true (List.all_eq_true.mp extremal r hr)
  intro x y h fromX
  by_cases xeq : x=bitRow r
  · subst x
    by_cases yeq : y=bitRow r
    · simpa [yeq] using fromX
    · have low : target (bitRow r)=false := by simpa [flipped] using fromX
      have clean := tests y
      cases hy : target y <;> simp_all [extreme,flipped]
  · have yes : target x=true := by simpa [flipped,xeq] using fromX
    by_cases yeq : y=bitRow r
    · subst y
      have z := target_mono x (bitRow r) h yes
      have clean := tests x
      simp [extreme,xeq,z,yes,h] at clean
    · simpa [flipped,yeq] using target_mono x y h yes

def determines (samples : Set Row) : Prop :=
  ∀ f, preserves f → (∀ x∈samples, f x=target x) → f=target

theorem every_test_needs (samples : Set Row) (complete : determines samples)
    (r : Nat) (hr : r∈rows) : bitRow r∈samples := by
  by_contra missing
  have same := complete (flipped r) (flip_preserves r hr) (by
    intro x hx
    have different : x≠bitRow r := fun e => missing (e ▸ hx)
    simp [flipped,different])
  have atRow := congrFun same (bitRow r)
  cases z : target (bitRow r) <;> simp [flipped,z] at atRow

theorem distinct : (rows.map bitRow).Nodup ∧ rows.length=29 := by decide +kernel

end CoCofactor29
