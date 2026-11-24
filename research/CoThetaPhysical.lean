import PEqualNP.Defs
import PEqualNP.CoThetaFreePins

namespace CoThetaPhysical
open CoThetaFreeCore PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gateForm (g : Gate) : PinForm :=
  match g.op, g.inputs with
  | .and, [] => .constant true
  | .or, [] => .constant false
  | .not, [] => .constant true
  | .and, [i] | .or, [i] => .copy i
  | .not, i::_ => .inv i
  | .and, i::j::_ => .binary false i j
  | .or, i::j::_ => .binary true i j
  | _, _ => .constant false

def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length≤2

private theorem read_word {ρ : Type} (w : List (ρ→Bool)) (i : Nat) (r : ρ) :
    ((w.map (fun f => f r)).getD i false) = w.getD i absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

private theorem read_option {ρ : Type} (o : Option (ρ→Bool)) (r : ρ) :
    (o.map (fun f => f r)).getD false = o.getD absentBit r := by cases o <;> rfl

theorem form_agrees {ρ : Type} (g : Gate) (hg : legal g) (w : List (ρ→Bool)) (r : ρ) :
    (gateForm g).value w r =
    g.op.eval (g.inputs.map fun i => (w.map (fun f => f r)).getD i false) := by
  obtain ⟨op,pins⟩ := g
  obtain ⟨hop,hlen⟩ := hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  change op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not at hop
  change pins.length≤2 at hlen
  rcases hop with rfl | rfl | rfl <;>
    cases pins with
    | nil => rfl
    | cons i xs =>
      cases xs with
      | nil => simp [gateForm,PinForm.value,GateOp.eval,base,read_word,read_option]
      | cons j t =>
        cases t with
        | nil => simp [gateForm,PinForm.value,GateOp.eval,base,read_word,read_option]
        | cons h t => simp at hlen

theorem map_execute {ρ : Type} (gs : List Gate) (w : List (ρ→Bool)) (r : ρ)
    (hg : ∀ g∈gs, legal g) :
    (execute (gs.map gateForm) w).map (fun f => f r) =
    gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)])
      (w.map (fun f => f r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,execute,List.foldl_cons]
    rw [ih _ (fun a ha => hg a (List.mem_cons_of_mem _ ha))]
    simp [form_agrees g (hg _ (by simp)) w r]

theorem circuit_rows {ρ : Type} (C : Circuit) (hf : FanInTwo C) (w : List (ρ→Bool)) (r : ρ) :
    (execute (C.gates.map gateForm) w).map (fun f => f r) = C.wires (w.map (fun f => f r)) :=
  map_execute C.gates w r hf

def boolCost (g : Gate) : Nat :=
  match g.op with
  | .and | .or => 1
  | _ => 0

theorem form_cost_le (g : Gate) : (gateForm g).binaryCost ≤ boolCost g := by
  obtain ⟨op,pins⟩ := g
  cases op <;> cases pins with
    | nil => simp [gateForm,boolCost,PinForm.binaryCost]
    | cons i t => cases t <;> simp [gateForm,boolCost,PinForm.binaryCost]

theorem cost_le_binary (gs : List Gate) :
    cost (gs.map gateForm) ≤ (gs.map boolCost).sum := by
  induction gs with
  | nil => simp [cost]
  | cons g gs ih =>
    simp only [List.map_cons,cost,List.sum_cons]
    exact Nat.add_le_add (form_cost_le g) ih

end CoThetaPhysical
