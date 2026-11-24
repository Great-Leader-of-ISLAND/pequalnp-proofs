import PEqualNP.CoAO3143Bridge

namespace CoAO3143

def initialForms (bank raw : List Sig) : Bool :=
  bank.sublists.all fun ws => unionSep false ws != top || ws==raw || ws==bank

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem initial0 : initialForms base0 outerVars = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem initial1 : initialForms base1 innerVars = true := by decide +kernel

theorem checked_from_two (bank raw : List Sig) (forms : initialForms bank raw = true)
    (one : search 12 0 raw = false) (both : search 12 0 bank = false) : checkedBank bank = true := by
  apply List.all_eq_true.mpr
  intro ws hw
  have h := List.all_eq_true.mp forms ws hw
  by_cases sep : unionSep false ws = top
  · have e : ws = raw ∨ ws = bank := by simpa [sep] using h
    rcases e with e | e
    · subst ws
      simp [rejectState,sep,one]
    · subst ws
      simp [rejectState,sep,both]
  · simp [rejectState,sep]

theorem ao_lower_of_four (a : search 12 0 outerVars=false) (b : search 12 0 base0=false)
    (c : search 12 0 innerVars=false) (d : search 12 0 base1=false)
    (p : Fin 8) (C : PEqualNP.CircuitLowerBounds.Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (noNot : ∀ g∈C.gates, g.op ≠ .not)
    (agree : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x ++ [!(x p),true,false]) = f8 x) : 13 ≤ C.size :=
  ao_lower_of_checks (checked_from_two _ _ initial0 a b) (checked_from_two _ _ initial1 c d) p C fan noNot agree

end CoAO3143
