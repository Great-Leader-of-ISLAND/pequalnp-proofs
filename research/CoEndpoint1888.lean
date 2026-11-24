import PEqualNP.CoPaid3143
import PEqualNP.CoRaw1888

namespace CoEndpoint1888
open CoRaw1888 CoThetaFreeCore CoThetaPhysical CoThetaNine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Full := Vertex → Bool
def coord (i : Vertex) : Full→Bool := fun x => x i
def roots : List (Full→Bool) := absentBit::seed::List.ofFn coord
def ep (b : Bool) : Vertex := if b then 2 else 0
def side (b : Bool) : Vertex → Option (Fin 9) :=
  if b then ![some 5,some 7,none,some 6,some 8,some 0,some 2,some 4,some 1,some 3]
  else ![none,some 6,some 8,some 5,some 7,some 4,some 1,some 3,some 0,some 2]
def lift (b : Bool) (r : Input) : Full := fun i => match side b i with | none => false | some j => vtx j r

theorem off (b : Bool) : restrict (lift b) (coord (ep b))=absentBit := by cases b <;> rfl

private theorem geometry : ∀ (b : Bool) (r : Input),
    target (lift b r)=ans r ∧ seed (lift b r)=vtx (if b then 5 else 8) r := by decide +kernel

private theorem raw_nine (i : Fin 9) : vtx i∈vertices := List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem known (b : Bool) : ∀ w∈roots, restrict (lift b) w∈vertices := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl|hw
  · exact List.mem_cons_self
  rcases List.mem_cons.mp hw with rfl|hw
  · have eqn : restrict (lift b) seed=vtx (if b then 5 else 8) := funext (fun r => (geometry b r).2)
    rw [eqn]
    exact raw_nine _
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  cases eqn : side b i with
  | none =>
    have e : restrict (lift b) (coord i)=absentBit := by funext r; simp [restrict,lift,coord,absentBit,eqn]
    exact e ▸ List.mem_cons_self
  | some j =>
    have e : restrict (lift b) (coord i)=vtx j := by funext r; simp [restrict,lift,coord,eqn]
    exact e ▸ raw_nine j

private def lo (b : Bool) : Full := raw (if b then 9 else 20)
private def hi (b : Bool) : Full := raw (if b then 13 else 21)
private theorem witnesses : ∀ b,
    seed (lo b)=seed (hi b) ∧ target (lo b)≠target (hi b) ∧ target (raw 24)≠coord (ep b) (raw 24) ∧
    ∀ i : Vertex,i≠ep b → coord i (lo b)=coord i (hi b) := by decide +kernel

theorem reader (b : Bool) {gs : List (TraceGate Full)} (ok : sufficient roots target gs) :
    ∃g∈gs,reads g (coord (ep b)) := by
  obtain ⟨both,mark,clear,other⟩ := witnesses b
  have source : agreeOutside (·=coord (ep b)) (lo b) (hi b) roots := by
    intro w hw skip
    rcases List.mem_cons.mp hw with rfl|hw
    · rfl
    rcases List.mem_cons.mp hw with rfl|hw
    · exact both
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact other i (fun same => skip (congrArg coord same))
  have no : target≠coord (ep b) := fun e => clear (congrFun e (raw 24))
  obtain ⟨g,hg,read,_⟩ := reader_witness (·=coord (ep b)) _ _ ok.1 source ok.2 no mark
  exact ⟨g,hg,read⟩

theorem at_least_one (b : Bool) {gs : List (TraceGate Full)} (ok : sufficient roots target gs) :
    1 ≤ saved (lift b) gs := by
  classical
  obtain ⟨g,hg,read⟩ := reader b ok
  have vanish : disappears (lift b) g := by
    rcases read with h|h
    · exact Or.inl (h ▸ off b)
    · exact Or.inr (h ▸ off b)
  have member : g∈vanishing (lift b) gs := by simp [vanishing,hg,vanish]
  rw [saved_eq_length]
  exact List.length_pos_of_mem member

theorem endpoint_budget (L : SignedLower) (b : Bool) {gs : List (TraceGate Full)} (ok : sufficient roots target gs) :
    14+saved (lift b) gs≤gs.length := by
  obtain ⟨ys,prog,hold⟩ := restrict_trace (lift b) gs ok.1 (Free.start (raw:=vertices)) List.mem_cons_self (known b)
  have result := hold target ok.2
  have answer : restrict (lift b) target=ans := funext (fun r => (geometry b r).1)
  rw [answer] at result
  obtain ⟨rs,len,reg,eq⟩ := trace_of_free prog
  have sol : sufficient vertices ans rs := ⟨reg,eq ▸ result⟩
  have price := any_nine_lower L sol
  have sum := accounted (lift b) gs
  omega

theorem tight_endpoints (L : SignedLower) {gs : List (TraceGate Full)} (ok : sufficient roots target gs)
    (small : gs.length≤15) : gs.length=15 ∧ ∀ b,saved (lift b) gs=1 := by
  have enough := endpoint_budget L false ok
  have lost := at_least_one false ok
  refine ⟨by omega,?_⟩
  intro b
  have lo := at_least_one b ok
  have hi := endpoint_budget L b ok
  omega

def ports (σ : Vertex→Vertex) : List (Full→Bool) := List.ofFn (fun i => coord (σ i)) ++ [CoRaw1888.seed]
def original (σ : Vertex→Vertex) := (fun _ : Full => false)::(fun _ : Full => true)::ports σ
private def blank : Full := fun _ => false

private theorem mapped (σ : Vertex→Vertex) (x : Full) : (ports σ).map (fun w => w x)=bank σ x := by
  simp [ports,CoRaw1888.bank,coord,List.map_ofFn,Function.comp_def]

private theorem initial (σ : Vertex→Vertex) : ∀w∈(original σ).map (norm blank),w∈roots := by
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  rcases List.mem_cons.mp hv with rfl|hv
  · exact List.mem_cons_self
  rcases List.mem_cons.mp hv with rfl|hv
  · exact List.mem_cons_self
  rcases List.mem_append.mp hv with hr|last
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    have e : norm blank (coord (σ i))=coord (σ i) := by funext x; rfl
    rw [e]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨σ i,rfl⟩))
  · obtain rfl := List.mem_singleton.mp last
    exact List.mem_cons_of_mem _ List.mem_cons_self

private theorem reads_at (ws : List (Full→Bool)) (i : Nat) (x : Full) :
    (ws.map (fun w => w x)).getD i false=ws.getD i absentBit x := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? <;> rfl

theorem signed_trace (D : Circuit) (σ : Vertex→Vertex) (legal : FanInTwo D)
    (correct : ∀x : Full,D.eval (bank σ x)=target x) :
    ∃ gs, gs.length=cost (D.gates.map gateForm) ∧ sufficient roots target gs := by
  let fs := D.gates.map gateForm
  let ws := ports σ
  let result := (execute fs ws).getD D.output absentBit
  have word : result=target := by
    funext x
    have ev := congrArg (fun v : List Bool => v.getD D.output false) (circuit_rows D legal ws x)
    change ((execute fs ws).map (fun w => w x)).getD D.output false=_ at ev
    rw [reads_at] at ev
    change result x=D.eval ((ports σ).map (fun f => f x)) at ev
    rw [mapped] at ev
    exact ev.trans (correct x)
  have here : result∈execute fs ws := by
    cases e : (execute fs ws)[D.output]? with
    | none =>
      have z : result=absentBit := by simp [result,List.getD_eq_getElem?_getD,e]
      have bad := congrFun (word.symm.trans z) (raw 24)
      exact (Bool.false_ne_true bad.symm).elim
    | some a =>
      have eq : result=a := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (congrArg (fun v => v∈execute fs ws) eq).mpr (List.mem_of_getElem? e)
  have cs (b : Bool) : (fun _ : Full => b)∈original σ := by
    cases b
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨us,prog,hold⟩ := pins_to_program fs ws (original σ) (original σ) 0 Ordinary.start cs
    (fun w hw => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
  obtain ⟨ys,free,sub⟩ := simulate_all_wires blank prog
  have out := sub _ (hold _ here)
  have nf : norm blank target=target := by funext x; rfl
  rw [word,nf] at out
  obtain ⟨gs,len,reg,e⟩ := trace_of_free free
  have inc := trace_subset gs (initial σ)
  exact ⟨gs,by simpa [fs] using len,inc.1 reg,inc.2 _ (e ▸ out)⟩

theorem fifteen_binary (L : SignedLower) (D : Circuit) (σ : Vertex→Vertex) (legal : FanInTwo D)
    (correct : ∀x : Full,D.eval (bank σ x)=target x) : 15≤cost (D.gates.map gateForm) := by
  obtain ⟨gs,len,ok⟩ := signed_trace D σ legal correct
  have lower := endpoint_budget L false ok
  have gain := at_least_one false ok
  omega

def negPrice (g : Gate) : Nat := match g.op with | .not => 1 | _ => 0

theorem gate_budget (gs : List Gate) : (gs.map negPrice).sum+(gs.map boolCost).sum≤gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have one : negPrice g+boolCost g≤1 := by obtain ⟨op,pins⟩ := g; cases op <;> simp [negPrice,boolCost]
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

theorem at_most_three_not (L : SignedLower) (D : Circuit) (σ : Vertex→Vertex) (legal : FanInTwo D)
    (small : D.size≤18) (correct : ∀x : Full,D.eval (bank σ x)=target x) : (D.gates.map negPrice).sum≤3 := by
  have price := fifteen_binary L D σ legal correct
  have bn := cost_le_binary D.gates
  have total := gate_budget D.gates
  change D.gates.length≤18 at small
  omega

theorem three_not_forces_tight (L : SignedLower) (D : Circuit) (σ : Vertex→Vertex) (legal : FanInTwo D)
    (small : D.size≤18) (correct : ∀x : Full,D.eval (bank σ x)=target x) (three : 3≤(D.gates.map negPrice).sum) :
    ∃gs, sufficient roots target gs ∧ gs.length=15 ∧ ∀b,saved (lift b) gs=1 := by
  obtain ⟨gs,sz,ok⟩ := signed_trace D σ legal correct
  have bn := cost_le_binary D.gates
  have total := gate_budget D.gates
  change D.gates.length≤18 at small
  exact ⟨gs,ok,tight_endpoints L ok (by omega)⟩

#print axioms CoEndpoint1888.fifteen_binary
#print axioms CoEndpoint1888.tight_endpoints
end CoEndpoint1888
