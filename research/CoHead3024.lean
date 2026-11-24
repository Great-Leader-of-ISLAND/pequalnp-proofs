import PEqualNP.CoPaid3143
namespace CoHead3024
open CoThetaNine CoThetaFreeCore CoThetaPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def or02 : TraceGate Input := ⟨.disj,vtx 0,vtx 2⟩
def headPool := or02.value::vertices

def firstBank : List (Input→Bool) := List.ofFn vtx ++ [or02.value]
def secondNot (pins : List Nat) : Input→Bool := fun r =>
  GateOp.not.eval (pins.map fun i => firstBank.getD i absentBit r)
def rawBank (pins : List Nat) := firstBank ++ [secondNot pins]
def bank (pins : List Nat) := absentBit::(fun _ : Input => true)::rawBank pins

private theorem invNorm (f : Input→Bool) :
    norm (row 0) (fun r => !(f r)) = norm (row 0) f := by
  funext r
  cases a : f (row 0) <;> cases b : f r <;> simp [CoThetaFreeCore.norm,phase,a,b]

private theorem vertexNorm (i : Fin 9) : norm (row 0) (vtx i)∈vertices := by
  have z : ∀ j : Fin 9, vtx j (row 0)=false := by decide
  have eq : norm (row 0) (vtx i)=vtx i := by
    funext r
    simp [CoThetaFreeCore.norm,phase,z]
  rw [eq]
  exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

private theorem knownFirst (w : Input→Bool) (h : w∈firstBank) : norm (row 0) w∈headPool := by
  rcases List.mem_append.mp h with raw|inv
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp raw
    exact List.mem_cons_of_mem _ (vertexNorm i)
  · obtain rfl := List.mem_singleton.mp inv
    have z : or02.value (row 0)=false := by decide
    have e : norm (row 0) or02.value=or02.value := by funext r; simp [CoThetaFreeCore.norm,phase,z]
    exact e ▸ List.mem_cons_self

private theorem knownBank (pins : List Nat) :
    ∀ w∈(bank pins).map (norm (row 0)), w∈headPool := by
  intro w h
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
  rcases List.mem_cons.mp ht with rfl|ht
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  rcases List.mem_cons.mp ht with rfl|ht
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  rcases List.mem_append.mp ht with hold|hlast
  · exact knownFirst _ hold
  obtain rfl := List.mem_singleton.mp hlast
  cases pins with
  | nil => exact List.mem_cons_of_mem _ List.mem_cons_self
  | cons p ps =>
    change norm (row 0) (fun r => !(firstBank.getD p absentBit r))∈headPool
    rw [invNorm]
    cases e : firstBank[p]? with
    | none =>
      simp only [List.getD_eq_getElem?_getD,e,Option.getD_none]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    | some w =>
      simp only [List.getD_eq_getElem?_getD,e,Option.getD_some]
      exact knownFirst w (List.mem_of_getElem? e)

private theorem rows_read (w : List (Input→Bool)) (j : Nat) (r : Input) :
    (w.map (fun f => f r)).getD j false = w.getD j absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? <;> rfl

theorem raw_eq (pins : List Nat) (r : Input) :
    (rawBank pins).map (fun f => f r) =
      let z := List.ofFn (fun i => vtx i r) ++ [vtx 0 r || vtx 2 r]
      z ++ [GateOp.not.eval (pins.map fun i => z.getD i false)] := by
  have one : firstBank.map (fun f => f r) = List.ofFn (fun i => vtx i r) ++ [vtx 0 r || vtx 2 r] := by
    simp [firstBank,or02,TraceGate.value,applyKind,List.map_ofFn]
  change (firstBank++[secondNot pins]).map _=_
  rw [List.map_append,one]
  congr 1
  simp only [List.map_cons,List.map_nil,secondNot]
  rw [←one]
  simp only [rows_read]

theorem physical_trace (pins : List Nat) (D : Circuit) (fan : FanInTwo D)
    (correct : ∀ r : Input, let x := fun i => vtx i r
      let z := List.ofFn x ++ [x 0 || x 2]
      D.eval (z ++ [GateOp.not.eval (pins.map fun i => z.getD i false)])=ans r) :
    ∃ gs, gs.length = cost (D.gates.map gateForm) ∧ sufficient headPool ans gs := by
  let fs := D.gates.map gateForm
  let start := rawBank pins
  let result := (execute fs start).getD D.output absentBit
  have word : result=ans := by
    funext r
    have ev := congrArg (fun w : List Bool => w.getD D.output false) (circuit_rows D fan start r)
    change ((execute fs start).map (fun f => f r)).getD D.output false = _ at ev
    rw [rows_read] at ev
    change result r=D.eval ((rawBank pins).map (fun f => f r)) at ev
    rw [raw_eq] at ev
    exact ev.trans (correct r)
  have hm : result∈execute fs start := by
    cases e : (execute fs start)[D.output]? with
    | none =>
      have z : result=absentBit := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (ans_not_zero (word.symm.trans z)).elim
    | some w =>
      have eq : result=w := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (congrArg (fun v => v∈execute fs start) eq).mpr (List.mem_of_getElem? e)
  have cs (b : Bool) : (fun _ : Input => b)∈bank pins := by
    cases b
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨ws,program,coverage⟩ := pins_to_program fs start (bank pins) (bank pins) 0 Ordinary.start cs
    (fun w h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  obtain ⟨ys,free,sub⟩ := simulate_all_wires (row 0) program
  have ng : norm (row 0) ans=ans := by
    have z : ans (row 0)=false := by decide
    funext r
    simp [CoThetaFreeCore.norm,phase,z]
  have goal := sub _ (coverage _ hm)
  rw [word,ng] at goal
  obtain ⟨gs,len,reg,eq⟩ := trace_of_free free
  have use := trace_subset gs (knownBank pins)
  refine ⟨gs,?_,use.1 reg,use.2 _ (eq ▸ goal)⟩
  simpa [fs] using len

theorem exact_binary (lb : SignedLower) (pins : List Nat) (D : Circuit) (fan : FanInTwo D) (small : D.size ≤ 13)
    (correct : ∀ r : Input, let x := fun i => vtx i r
      let z := List.ofFn x ++ [x 0 || x 2]
      D.eval (z ++ [GateOp.not.eval (pins.map fun i => z.getD i false)])=ans r) :
    cost (D.gates.map gateForm)=13 ∧ D.size=13 ∧ ∀ g∈D.gates, g.op≠GateOp.not := by
  obtain ⟨gs,len,reg,out⟩ := physical_trace pins D fan correct
  have vert (i : Fin 9) : vtx i∈vertices := List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have h := any_nine_lower lb (gs:=or02::gs) ⟨⟨vert 0,vert 2,reg⟩,out⟩
  simp only [List.length_cons] at h
  have cap := pin_cost_length (D.gates.map gateForm)
  simp only [List.length_map] at cap
  change D.gates.length ≤ 13 at small
  refine ⟨by omega,by change D.gates.length=13; omega,?_⟩
  intro g hg ng
  have imp := CoPaid3143.cost_with_not D.gates ⟨g,hg,ng⟩
  omega
#print axioms CoHead3024.exact_binary
end CoHead3024
