import PEqualNP.CoThetaOr1677

namespace CoThetaOr1677
open CoAO3143Restriction CoThetaNine PEqualNP.CircuitLowerBounds

private theorem available {A : Type} {s bank : List (Wire A)}
    (keep : ∀ u∈s,u∈bank) (z : con false∈bank) (i : Nat) :
    s.getD i (con false)∈bank := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : s[i]? with
  | none => exact z
  | some u => exact keep u (List.mem_of_getElem? e)

private theorem decode {A : Type} (w pool : List (Wire A)) (g : Gate)
    (keep : ∀ u∈w,u∈pool) (cs : ∀ b : Bool,con b∈pool)
    (valid : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) :
    readGate w g ∈ pool ∨
      ∃ d a b,a∈pool ∧ b∈pool ∧ readGate w g=op d a b := by
  obtain ⟨t,is⟩ := g
  obtain ⟨ops,size⟩ := valid
  change is.length ≤ 2 at size
  change t=_ ∨ t=_ at ops
  cases is with
  | nil => rcases ops with rfl|rfl; exact Or.inl (cs true); exact Or.inl (cs false)
  | cons i is =>
    cases is with
    | nil =>
      left
      convert available keep (cs false) i using 1
      rcases ops with rfl|rfl <;> funext r <;> simp [readGate,GateOp.eval]
    | cons j rest =>
      cases rest with
      | cons _ _ => simp at size
      | nil =>
        right
        rcases ops with rfl|rfl
        · exact ⟨false,_,_,available keep (cs false) i,available keep (cs false) j,
            by funext r; simp [readGate,GateOp.eval,op]⟩
        · exact ⟨true,_,_,available keep (cs false) i,available keep (cs false) j,
            by funext r; simp [readGate,GateOp.eval,op]⟩

private theorem execute (gs : List Gate) {n : Nat} {w pool : List (Wire SmallInput)}
    (start : Build sources n pool) (keep : ∀ u∈w,u∈pool)
    (cs : ∀ b : Bool,con b∈pool)
    (valid : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) :
    ∃ m ys,Build sources m ys ∧ (m ≤ n+gs.length) ∧
      ∀ u∈circuitWires gs w,u∈ys := by
  induction gs generalizing n w pool with
  | nil => exact ⟨n,pool,start,by simp,keep⟩
  | cons g gs ih =>
    have rest := fun (h : Gate) (e : h∈gs) => valid h (List.mem_cons_of_mem _ e)
    rcases decode w pool g keep cs (valid g List.mem_cons_self) with known|⟨d,a,b,ha,hb,eq⟩
    · have cover : ∀ u∈w++[readGate w g],u∈pool := by
        intro u h
        rcases List.mem_append.mp h with old|new
        · exact keep u old
        · rw [List.mem_singleton.mp new]
          exact known
      obtain ⟨m,ys,prog,lim,last⟩ := ih start cover cs rest
      exact ⟨m,ys,prog,by simp only [List.length_cons]; omega,last⟩
    · let z := op d a b
      have cover : ∀ u∈w++[readGate w g],u∈z::pool := by
        intro u h
        rcases List.mem_append.mp h with old|new
        · exact List.mem_cons_of_mem _ (keep u old)
        · exact List.mem_cons.mpr (Or.inl ((List.mem_singleton.mp new).trans eq))
      have constants := fun b => List.mem_cons_of_mem z (cs b)
      obtain ⟨m,ys,prog,lim,last⟩ := ih (Build.gate start d a b ha hb) cover constants rest
      exact ⟨m,ys,prog,by simp only [List.length_cons]; omega,last⟩

def readWord (gs : List Gate) (addr : Nat) : Wire SmallInput :=
  fun r => (Circuit.eval ⟨gs,addr⟩ (List.ofFn (fun i : Fin 7 => raw7 i r)))

private theorem evaluation (gs : List Gate) (addr : Nat) :
    (circuitWires gs raw).getD addr (con false) = readWord gs addr := by
  funext r
  let ws := circuitWires gs raw
  have step := congrArg (fun w : List Bool => w.getD addr false) (circuit_rows gs raw r)
  have read : (ws.map (fun f => f r)).getD addr false = ws.getD addr (con false) r := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ws[addr]? <;> rfl
  change (ws.map (fun f => f r)).getD addr false = _ at step
  rw [read] at step
  have inputs : raw.map (fun f => f r) = List.ofFn (fun i : Fin 7 => raw7 i r) := by
    simp [raw,List.map_ofFn]
  rw [inputs] at step
  exact step

/-- The original coordinate list may contain permutations, repetitions and
constants after a restriction. The history uses these exact addresses. -/
theorem wires_price (gs : List Gate) (w : List (Wire SmallInput))
    (initial : ∀ u∈w,u∈sources)
    (valid : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2)
    (correct : ans7∈circuitWires gs w) (marked : seed45∈circuitWires gs w) :
    12 ≤ gs.length := by
  have cs (b : Bool) : con b∈sources := by cases b <;> simp [sources]
  obtain ⟨n,ys,prog,lim,sub⟩ := execute gs Build.start initial cs valid
  have price := paid_marked_or prog (sub _ correct) (sub _ marked)
  omega

/-- Every genuine seven-input circuit, including out-of-range reads, alias or
zero-arity gates and arbitrary output/supply addresses. The distinguished wire
is identified by its full 128-row Boolean function. -/
theorem raw_price (gs : List Gate) (out marked : Nat)
    (valid : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2)
    (correct : readWord gs out=ans7) (witness : readWord gs marked=seed45) :
    12 ≤ gs.length := by
  have initial : ∀ u∈raw,u∈sources := fun u h => List.mem_append_left _ h
  have constants (b : Bool) : con b∈sources := by cases b <;> simp [sources]
  obtain ⟨m,ys,prog,lim,cover⟩ := execute gs Build.start initial constants valid
  have find (i : Nat) : readWord gs i ∈ ys := by
    rw [←evaluation]
    apply available cover _ i
    have base : ∀ {n xs},Build sources n xs → ∀ u∈sources,u∈xs := by
      intro n xs build
      induction build with
      | start => exact fun _ h => h
      | gate _ _ _ _ _ _ ih => exact fun v hv => List.mem_cons_of_mem _ (ih v hv)
    exact base prog _ (constants false)
  have output := find out
  have seed := find marked
  rw [correct] at output
  rw [witness] at seed
  have lower := paid_marked_or prog output seed
  omega

#print axioms raw_price
end CoThetaOr1677
