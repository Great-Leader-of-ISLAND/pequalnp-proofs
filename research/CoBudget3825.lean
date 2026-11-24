import PEqualNP.CoBudget3825Base

namespace PEqualNP.Outside.L_meta_2153_aux.CoBudget3825
open CoThetaNine CoThetaFreeCore CoThetaPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def origin : List (Input → Bool) := List.ofFn vtx
def bank : List (Input → Bool) := absentBit :: (fun _ => true) :: origin

private theorem row_read (ws : List (Input → Bool)) (j : ℕ) (r : Input) :
    (ws.map fun f => f r).getD j false = ws.getD j absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[j]? <;> rfl

theorem normalized_bank : ∀ f ∈ bank.map (norm (row 0)), f ∈ vertices := by
  rintro f hf
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hf
  rcases List.mem_cons.mp hv with rfl|hv
  · exact List.mem_cons_self
  rcases List.mem_cons.mp hv with rfl|hv
  · exact List.mem_cons_self
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  have zero : ∀ i : Fin 9, vtx i (row 0) = false := by decide
  have same : norm (row 0) (vtx i) = vtx i := by
    funext r
    simp [CoThetaFreeCore.norm,zero,phase]
  rw [same]
  exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem binary_budget (cert : SignedLower) (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ r : Input, C.eval (List.ofFn (fun i => vtx i r)) = ans r) :
    14 ≤ (C.gates.map boolCost).sum := by
  let fs := C.gates.map gateForm
  let out := (execute fs origin).getD C.output absentBit
  have word : out = ans := by
    funext r
    have ev := congrArg (fun w : List Bool => w.getD C.output false) (circuit_rows C fan origin r)
    change ((execute fs origin).map (fun f => f r)).getD C.output false = _ at ev
    rw [row_read] at ev
    change out r = C.eval (origin.map (fun f => f r)) at ev
    exact ev.trans (by simpa [origin,List.map_ofFn] using correct r)
  have cs (b : Bool) : (fun _ : Input => b) ∈ bank := by
    cases b
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨ys,pg,cov⟩ := pins_to_program fs origin bank bank 0 Ordinary.start cs
    (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  have mem : out ∈ ys := by
    cases e : (execute fs origin)[C.output]? with
    | none =>
      have eq : out = absentBit := by simp [out,List.getD_eq_getElem?_getD,e]
      exact (ans_not_zero (word.symm.trans eq)).elim
    | some w =>
      have eq : out = w := by simp [out,List.getD_eq_getElem?_getD,e]
      exact eq ▸ cov _ (List.mem_of_getElem? e)
  obtain ⟨vs,free,hits⟩ := simulate_all_wires (row 0) pg
  have zero : ans (row 0) = false := by decide
  have stable : norm (row 0) ans = ans := by funext r; simp [CoThetaFreeCore.norm,phase,zero]
  have hit := hits _ mem
  rw [word,stable] at hit
  obtain ⟨gs,len,reg,eq⟩ := trace_of_free free
  have sub := trace_subset gs normalized_bank
  have h := any_nine_lower cert (gs:=gs) ⟨sub.1 reg,sub.2 _ (eq ▸ hit)⟩
  have price := cost_le_binary C.gates
  change cost fs ≤ _ at price
  omega

theorem count_and_not (gs : List Gate) (fan : ∀ g∈gs, legal g) :
    (gs.map boolCost).sum + gs.countP (fun g => g.op.eval [false]) = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have rest := ih (fun u hu => fan u (List.mem_cons_of_mem g hu))
    have op := (fan g List.mem_cons_self).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    rcases op with h|h|h <;>
      simp [List.countP_cons,boolCost,h,GateOp.eval] at * <;> omega

theorem at_most_one_negation (cert : SignedLower) (C : Circuit)
    (fan : FanInTwo C) (size : C.size = 15)
    (correct : ∀ r : Input, C.eval (List.ofFn fun i => vtx i r) = ans r) :
    C.gates.countP (fun g => g.op.eval [false]) ≤ 1 := by
  have budget := binary_budget cert C fan correct
  have split := count_and_not C.gates fan
  change C.gates.length = 15 at size
  omega
end PEqualNP.Outside.L_meta_2153_aux.CoBudget3825
