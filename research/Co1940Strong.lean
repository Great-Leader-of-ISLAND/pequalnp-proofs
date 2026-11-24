import PEqualNP.CoThetaOriginal

namespace CoThetaNine
open CoThetaFreeCore

def SemanticSeven : Prop := ∀ {n ws}, Free vertices7 n ws → ans7∈ws → 11≤n

theorem residual_of_semantic (lower7 : SemanticSeven)
    (j : Fin 6) {gs : List (TraceGate Input)} (ok : sufficient vertices ans gs) :
    11≤remaining (sliceLift j) gs := by
  obtain ⟨ws,run,sub⟩ := restrict_trace (sliceLift j) gs ok.1
    (Free.start (raw:=vertices7)) List.mem_cons_self (slice_known j)
  have read := sub ans ok.2
  have ax : restrict (sliceLift j) ans=ans7 := funext (fun r => (slice7_values j r).1)
  rw [ax] at read
  simpa only [Nat.zero_add] using lower7 run read

theorem nine_of_semantic (lower7 : SemanticSeven)
    {gs : List (TraceGate Input)} (ok : sufficient vertices ans gs) : 14≤gs.length := by
  classical
  obtain ⟨ts,solves,fresh,le,_⟩ := simplify_trace gs ok
  cases ts with
  | nil => exact (nonempty_solution solves rfl).elim
  | cons g tail =>
    obtain ⟨j,readers⟩ := fresh_slice_head solves fresh
    have gain := three_saved j readers
    have cost := residual_of_semantic lower7 j solves
    have eq := accounted (sliceLift j) (g::tail)
    omega


theorem fixed_of_semantic (lower7 : SemanticSeven)
    {head : TraceGate Input} {gs : List (TraceGate Input)} (h : fixedHeadResult head gs) :
    14≤gs.length := by
  rcases h with ⟨n,zs,le,run,out⟩|⟨ts,le,solves,saves⟩
  · obtain ⟨s,len,reg,eq⟩ := trace_of_free run
    have h := nine_of_semantic lower7 (gs:=s) ⟨reg,eq ▸ out⟩
    omega
  · have lower := residual_of_semantic lower7 0 solves
    have total := accounted (sliceLift 0) (head::ts)
    change 4≤saved (sliceLift 0) (head::ts) at saves
    simp only [List.length_cons] at total
    omega

end CoThetaNine

namespace Co1940Physical
open CoThetaNine CoThetaFreeCore CoThetaPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def firstBank : List (Input→Bool) := List.ofFn vtx ++ [fun r => !(vtx 0 r)]
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

private theorem knownFirst (w : Input→Bool) (h : w∈firstBank) : norm (row 0) w∈vertices := by
  rcases List.mem_append.mp h with raw|inv
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp raw
    exact vertexNorm i
  · obtain rfl := List.mem_singleton.mp inv
    rw [invNorm]
    exact vertexNorm 0

private theorem knownBank (pins : List Nat) :
    ∀ w∈(bank pins).map (norm (row 0)), w∈vertices := by
  intro w h
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
  rcases List.mem_cons.mp ht with rfl|ht
  · exact List.mem_cons_self
  rcases List.mem_cons.mp ht with rfl|ht
  · exact List.mem_cons_self
  rcases List.mem_append.mp ht with hold|hlast
  · exact knownFirst _ hold
  obtain rfl := List.mem_singleton.mp hlast
  cases pins with
  | nil => exact List.mem_cons_self
  | cons p ps =>
    change norm (row 0) (fun r => !(firstBank.getD p absentBit r))∈vertices
    rw [invNorm]
    cases e : firstBank[p]? with
    | none =>
      simp only [List.getD_eq_getElem?_getD,e,Option.getD_none]
      exact List.mem_cons_self
    | some w =>
      simp only [List.getD_eq_getElem?_getD,e,Option.getD_some]
      exact knownFirst w (List.mem_of_getElem? e)

private theorem rows_read (w : List (Input→Bool)) (j : Nat) (r : Input) :
    (w.map (fun f => f r)).getD j false = w.getD j absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? <;> rfl

private theorem raw_eq (pins : List Nat) (r : Input) :
    (rawBank pins).map (fun f => f r) =
      let z := List.ofFn (fun i => vtx i r) ++ [!(vtx 0 r)]
      z ++ [GateOp.not.eval (pins.map fun i => z.getD i false)] := by
  have one : firstBank.map (fun f => f r) = List.ofFn (fun i => vtx i r) ++ [!(vtx 0 r)] := by
    simp [firstBank,List.map_ofFn]
  change (firstBank++[secondNot pins]).map _=_
  rw [List.map_append,one]
  congr 1
  simp only [List.map_cons,List.map_nil,secondNot]
  rw [←one]
  simp only [rows_read]

theorem physical_trace (pins : List Nat) (D : Circuit) (fan : FanInTwo D)
    (correct : ∀ r : Input, let x := fun i => vtx i r
      let z := List.ofFn x ++ [!(x 0)]
      D.eval (z ++ [GateOp.not.eval (pins.map fun i => z.getD i false)])=ans r) :
    ∃ gs, gs.length ≤ D.size ∧ sufficient vertices ans gs := by
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
  have h := pin_cost_length fs
  simp only [Nat.zero_add] at len
  rw [len]
  exact h.trans (by simp [fs,Circuit.size])

end Co1940Physical

theorem Co1940Physical.original_if (lower7 : CoThetaNine.SemanticSeven) : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  classical
  intro pins _ D fan len
  by_contra h
  push_neg at h
  obtain ⟨gs,le,ok⟩ := Co1940Physical.physical_trace pins D fan (fun r =>
    Classical.not_not.mp (h (fun i => CoThetaNine.vtx i r)))
  have b := CoThetaNine.nine_of_semantic lower7 ok
  omega
