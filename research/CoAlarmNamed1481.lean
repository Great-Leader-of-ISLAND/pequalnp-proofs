import PEqualNP.CoAlarmRecurrence1481

namespace CoAlarmNamed1481
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoAlarmWire1481 CoAlarmRecurrence1481
open CoFormula1963Circuit

theorem witness_value (C : Circuit) (mono : Monotone2 C)
    (binary : ∀ g∈C.gates, ∃ a b : Nat,g.inputs=[a,b])
    (row : X → Bool) (v : X) (d : Nat → Bool)
    (raw : ∀ i < 26, d i = ((initial.map (info row v)).getD i (false,false)).2)
    (steps : ∀ (k : Nat) (hk : k<C.gates.length), ∃ a b : Nat,
      C.gates[k].inputs=[a,b] ∧ a<26+k ∧ b<26+k ∧
      d (26+k)=rule (andFlag C.gates[k].op)
        ((C.wires (input row)).getD a false) ((C.wires (input row)).getD b false) (d a) (d b))
    (out : C.output<26+C.gates.length) : d C.output=physical C row v := by
  let ws := initial.map (info row v)
  have size : ws.length=26 := by simp [ws,initial]
  have start : ∀ i<ws.length,d i=(ws.getD i (false,false)).2 := by simpa only [size] using raw
  have valid (k : Nat) (hk : k<C.gates.length) : ∃ a b : Nat,
      C.gates[k].inputs=[a,b] ∧ a<ws.length+k ∧ b<ws.length+k ∧
      d (ws.length+k)=rule (andFlag C.gates[k].op)
          (wire C.gates ws a).1 (wire C.gates ws b).1 (d a) (d b) := by
    obtain ⟨a,b,h,ha,hb,eq⟩ := steps k hk
    refine ⟨a,b,h,by simpa only [size] using ha,by simpa only [size] using hb,?_⟩
    rw [size,values C mono binary row v a,values C mono binary row v b]
    exact eq
  exact unique C.gates ws d start valid C.output (by simpa only [size] using out)

end CoAlarmNamed1481
