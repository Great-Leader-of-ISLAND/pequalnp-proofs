import PEqualNP.CoAlarmWire1481
import PEqualNP.CoAlarmPhysical1481

namespace CoAlarmCost1481
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoFormula1963Geometry CoFormula1963Link CoFormula1963Protocol
open CoFormula1963Circuit CoFormula1963Ledger CoAlarmDerivative1481 CoAlarmWhole1481
open CoAlarmWire1481 (physical output_flag info)

theorem unshared_price (C : Circuit) (mono : Monotone2 C)
    (binary : ∀ g∈C.gates,∃ a b : Nat,g.inputs=[a,b]) (one : noShare 26 C.gates)
    (e : E) (yes : ∀ f : E,C.eval (input (pos f))=true)
    (no : ∀ y : Y,C.eval (input (neg y))=false)
    (p0 : C.eval (input (singleton (.inl e.val.1)))=false)
    (l0 : C.eval (input (singleton (.inr e.val.2)))=false)
    (dp : physical C (singleton (.inr e.val.2)) (.inl e.val.1)=false)
    (dl : physical C (singleton (.inl e.val.1)) (.inr e.val.2)=false) : 65 ≤ C.size := by
  let root := (run C.gates initial).getD C.output (.fixed false)
  have sem (x : X → Bool) : val x root=C.eval (input x) := value_of_output C mono x
  have cap : cost root ≤ C.size := by
    have bound := any_wire (run_costs C.gates) one C.output
    simpa only [cost_get,Circuit.size,root] using bound
  cases eq : root with
  | fixed b =>
    have u := (sem (pos e)).trans (yes e)
    have v := (sem (singleton (.inl e.val.1))).trans p0
    simp only [eq,val] at u v
    cases b <;> contradiction
  | tree t =>
    have lift (x : X → Bool) : t.eval x=C.eval (input x) := by simpa [eq,val] using sem x
    have jet (x : X → Bool) (v : X) : alarm x v t=physical C x v := by
      have z := output_flag C x v binary
      change (info x v root).2=physical C x v at z
      simpa [eq,info] using z
    have big := flat66 t (fun f => (lift _).trans (yes f)) (fun y => (lift _).trans (no y)) e
      ((lift _).trans p0) ((lift _).trans l0) ((jet _ _).trans dp) ((jet _ _).trans dl)
    rw [eq] at cap
    change t.leaves-1 ≤ C.size at cap
    omega

#print axioms unshared_price
end CoAlarmCost1481
