import PEqualNP.CoFormula1963Complete
import PEqualNP.CoFormula1963Physical

namespace CoFormula1963Circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoFormula1963Geometry CoFormula1963Protocol CoFormula1963Link CoFormula1963Ledger

/-- Real physical output and all original gate reads use the official
    Circuit.eval/getD semantics. Inputs can repeat freely. Each internal
    output may occupy at most one gate operand position in the whole list. -/
theorem no_shared_64 (C : Circuit) (mono : Monotone2 C) (single : noShare 26 C.gates)
    (accept : ∀ e : E, C.eval (input (pos e)) = true)
    (reject : ∀ y : CoFormula1963Link.Y, C.eval (input (neg y)) = false) : 64 ≤ C.size := by
  let e : E := ⟨(0,0),by decide⟩
  let y : CoFormula1963Link.Y := (0,0)
  obtain ⟨t,cap,sem⟩ := exists_formula C mono single (pos e) (neg y) (accept e) (reject y)
  have low := CoFormula1963Complete.leaves65 t (fun f => (sem (pos f)).trans (accept f))
    (fun q => (sem (neg q)).trans (reject q))
  omega

#print axioms no_shared_64
end CoFormula1963Circuit
