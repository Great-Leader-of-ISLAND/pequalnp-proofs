import PEqualNP.CoClean3024
import PEqualNP.CoConeOrder3024
import PEqualNP.CoPaid3143

namespace CoPhysical3174
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoThetaNine CoThetaFreeCore CoThetaPhysical CoAO3143Restriction

noncomputable section
local instance : DecidableEq (Input→Bool) := Classical.decEq _

def mate (b : Fin 3) : Fin 9 := ![2,3,8] b
def seed (b : Fin 3) : Input→Bool := fun r => vtx 1 r || vtx (mate b) r
def negative : Input→Bool := fun r => !(vtx 0 r)
def perm (flip : Bool) (i : Fin 9) : Fin 9 := if flip then ![0,5,8,3,4,1,7,6,2] i else i
def bank (b : Fin 3) (flip : Bool) : List (Input→Bool) :=
  List.ofFn (fun i => vtx (perm flip i)) ++ [negative,seed b]
def sources (b : Fin 3) (inv : Bool) : Finset (Input→Bool) :=
  ((List.ofFn vtx ++ [seed b]) ++ (if inv then [negative] else [])).toFinset

private theorem vertex_mem (i : Fin 9) : vtx i∈vertices := List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
private theorem vertex_normal (i : Fin 9) : norm (row 0) (vtx i)=vtx i := by
  have z : ∀j : Fin 9, vtx j (row 0)=false := by decide
  funext r
  simp [norm,phase,z]
private theorem negative_normal : norm (row 0) negative=vtx 0 :=
  (normalize_unary (row 0) (vtx 0)).trans (vertex_normal 0)
private theorem seed_normal (b : Fin 3) : norm (row 0) (seed b)=seed b := by
  have z : ∀j : Fin 3,seed j (row 0)=false := by decide
  funext r
  simp [norm,phase,z]
private theorem ans_normal : norm (row 0) ans=ans := by
  have z : ans (row 0)=false := by decide
  funext r
  simp [norm,phase,z]

private theorem bank_cases {b flip w} (h : w∈bank b flip) :
    (∃i : Fin 9,w=vtx i) ∨ w=negative ∨ w=seed b := by
  rcases List.mem_append.mp h with raw|endw
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp raw
    exact Or.inl ⟨perm flip i,rfl⟩
  · exact Or.inr (by simpa using endw)

private def physical (b : Fin 3) (flip : Bool) := absentBit::(fun _ : Input => true)::bank b flip
private def gate (b : Fin 3) : TraceGate Input := ⟨.disj,vtx 1,vtx (mate b)⟩

private theorem normalized_bank (b : Fin 3) (flip : Bool) :
    ∀ w∈(physical b flip).map (norm (row 0)),w∈(seed b)::vertices := by
  intro w hw
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
  rcases List.mem_cons.mp ha with rfl|ha
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  rcases List.mem_cons.mp ha with rfl|ha
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  rcases bank_cases ha with ⟨i,rfl⟩|rfl|rfl
  · rw [vertex_normal]
    exact List.mem_cons_of_mem _ (vertex_mem i)
  · rw [negative_normal]
    exact List.mem_cons_of_mem _ (vertex_mem 0)
  · rw [seed_normal]
    exact List.mem_cons_self

private theorem signed_lower (lower : SignedLower) (b : Fin 3) (flip : Bool) (C : Circuit)
    (fan : FanInTwo C) (correct : ∀r : Input,C.eval ((bank b flip).map fun w => w r)=ans r) :
    13≤cost (C.gates.map gateForm) := by
  let fs := C.gates.map gateForm
  let start := bank b flip
  let result := (execute fs start).getD C.output absentBit
  have word : result=ans := by
    funext r
    have eq := congrArg (fun v : List Bool => v.getD C.output false) (CoThetaPhysical.circuit_rows C fan start r)
    change ((execute fs start).map (fun w => w r)).getD C.output false=C.eval _ at eq
    have read : ((execute fs start).map (fun w => w r)).getD C.output false=result r := by
      simp only [result,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases (execute fs start)[C.output]? <;> rfl
    rw [read] at eq
    exact eq.trans (correct r)
  have hm : result∈execute fs start := by
    cases e : (execute fs start)[C.output]? with
    | none =>
      have z : result=absentBit := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (ans_not_zero (word.symm.trans z)).elim
    | some w =>
      have eq : result=w := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (congrArg (fun v => v∈execute fs start) eq).mpr (List.mem_of_getElem? e)
  have cs (q : Bool) : (fun _ : Input => q)∈physical b flip := by
    cases q
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨ws,pg,holds⟩ := pins_to_program fs start (physical b flip) (physical b flip) 0 Ordinary.start cs
    (fun w h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  obtain ⟨ys,free,sub⟩ := simulate_all_wires (row 0) pg
  have hit := sub _ (holds _ hm)
  rw [word,ans_normal] at hit
  obtain ⟨gs,len,reg,eq⟩ := trace_of_free free
  have changeSeed := trace_subset gs (normalized_bank b flip)
  have ok : sufficient vertices ans (gate b::gs) :=
    ⟨⟨vertex_mem 1,vertex_mem (mate b),changeSeed.1 reg⟩,changeSeed.2 _ (eq ▸ hit)⟩
  have bound := any_nine_lower lower ok
  simp only [List.length_cons] at bound
  have exactLength : gs.length=cost (C.gates.map gateForm) := by simpa [fs] using len
  omega

private theorem cone_program {k S} (c : Cone ans k S) {n ws} (pre : Free vertices n ws)
    (available : ∀a∈S,norm (row 0) a∈ws) :
    ∃ys,Free vertices (n+k) ys ∧ norm (row 0) ans∈ys := by
  induction c generalizing n ws with
  | stop => exact ⟨ws,by simpa using pre,available ans (by simp)⟩
  | @gate k U d a b _fresh _tail ih =>
    have ha := available a (Finset.mem_insert_self _ _)
    have hb := available b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    let tag := normalizedKind d (a (row 0)) (b (row 0))
    have step := Free.binary pre tag ha hb
    have same : norm (row 0) (op d a b) = (fun r => applyKind tag (norm (row 0) a r) (norm (row 0) b r)) :=
      normalize_binary (row 0) d a b
    obtain ⟨ys,done,hit⟩ := ih step (fun w hw => by
      rcases Finset.mem_insert.mp hw with rfl|old
      · rw [same]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (available w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old))))
    exact ⟨ys,by convert done using 1 <;> omega,hit⟩

private theorem seed_required (lower : SignedLower) (b : Fin 3) {k S} (cap : k≤13) (run : Cone ans k S)
    (src : ∀ w∈S,(∃i : Fin 9,w=vtx i) ∨ w=negative ∨ w=seed b) : seed b∈S := by
  by_contra missing
  have known (w) (hw : w∈S) : norm (row 0) w∈vertices := by
    rcases src w hw with ⟨i,rfl⟩|rfl|rfl
    · rw [vertex_normal]; exact vertex_mem i
    · rw [negative_normal]; exact vertex_mem 0
    · exact (missing hw).elim
  obtain ⟨ys,prog,hit⟩ := cone_program run Free.start known
  rw [ans_normal] at hit
  obtain ⟨gs,len,reg,eq⟩ := trace_of_free prog
  have price := any_nine_lower lower (show sufficient vertices ans gs from ⟨reg,eq ▸ hit⟩)
  omega

private def low (b : Fin 3) (i : Fin 9) : Input :=
  row (![![2,4,2,4,1,1,2,4,8],![2,9,2,18,1,1,2,4,8],![2,257,2,4,1,1,2,4,10]] b i)
private def high (b : Fin 3) (i : Fin 9) : Input := row ((low b i).val ||| (1 <<< i.val))
private theorem tests : ∀ (b : Fin 3) (i : Fin 9),
    ans (high b i)=true ∧ ans (low b i)=false ∧ seed b (high b i)=seed b (low b i) ∧
    (negative (high b i)=true → negative (low b i)=true) ∧
    ∀ j : Fin 9, j≠i → vtx j (high b i)=vtx j (low b i) := by decide +kernel

private theorem all_raw (b : Fin 3) {k S} (run : Cone ans k S)
    (src : ∀ w∈S,(∃i : Fin 9,w=vtx i) ∨ w=negative ∨ w=seed b) (i : Fin 9) : vtx i∈S := by
  by_contra missing
  obtain ⟨on,off,fixedSeed,neg,rest⟩ := tests b i
  have wrong := CoConeOrder3024.ordered run (high b i) (low b i) (fun w hw t => by
    rcases src w hw with ⟨j,rfl⟩|rfl|rfl
    · exact (rest j (fun e => missing (e ▸ hw))) ▸ t
    · exact neg t
    · exact fixedSeed ▸ t) on
  exact Bool.false_ne_true (off.symm.trans wrong)

theorem extract (lower : SignedLower) (b : Fin 3) (flip : Bool) (C : Circuit) (fan : FanInTwo C)
    (cap : C.size≤13) (correct : ∀r : Input,C.eval ((bank b flip).map fun w => w r)=ans r) :
    ∃ k ≤ 13, ∃ inv : Bool, CoClean3024.Clean ans k (sources b inv) := by
  have price := signed_lower lower b flip C fan correct
  have no (g) (hg : g∈C.gates) : g.op≠GateOp.not := by
    intro eq
    have too := CoPaid3143.cost_with_not C.gates ⟨g,hg,eq⟩
    change C.gates.length≤13 at cap
    omega
  let U := circuitWires C.gates (bank b flip)
  let out := U.getD C.output (con false)
  have truth : out=ans := by
    funext r
    have ev := congrArg (fun v : List Bool => v.getD C.output false)
      (CoAO3143Restriction.circuit_rows C.gates (bank b flip) r)
    change (U.map (fun w => w r)).getD C.output false=C.eval _ at ev
    have read : (U.map (fun w => w r)).getD C.output false=out r := by
      simp only [out,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases U[C.output]? <;> rfl
    exact (read.symm.trans ev).trans (correct r)
  have nc : ¬Constant ans := by
    rintro ⟨v,e⟩
    have a := congrFun e (row 0)
    have u := congrFun e (row 3)
    have z : ans (row 0)=false := by decide
    have t : ans (row 3)=true := by decide
    change ans _=v at a u
    exact Bool.false_ne_true (z.symm.trans (a.trans (u.symm.trans t)))
  have hit : ans∈U ∨ Constant ans := by
    cases e : U[C.output]? with
    | none => exact Or.inr ⟨false,truth.symm.trans (by simp [out,List.getD_eq_getElem?_getD,e])⟩
    | some w =>
      have f : out=w := by simp [out,List.getD_eq_getElem?_getD,e]
      exact Or.inl ((truth.symm.trans f).symm ▸ List.mem_of_getElem? e)
  have legal (g) (hg : g∈C.gates) : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
    obtain ⟨h,sz⟩ := fan g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    exact ⟨h.elim Or.inl (fun hh => Or.inr (hh.resolve_right (no g hg))),sz⟩
  obtain ⟨k,S,sz,clean,src⟩ := CoClean3024.extract ans C.gates (bank b flip) legal hit
  have klass (w) (hw : w∈S) := bank_cases ((src w hw).resolve_right (CoClean3024.inputs_vary clean nc w hw))
  let inv := decide (negative∈S)
  have raw := all_raw b (CoClean3024.toCone clean) klass
  have sd := seed_required lower b (sz.trans cap) (CoClean3024.toCone clean) klass
  have eq : S=sources b inv := by
    ext w
    simp only [sources,List.mem_toFinset,List.mem_append,List.mem_singleton,List.mem_ofFn]
    by_cases used : negative∈S
    · simp only [inv,decide_eq_true used,ite_true,List.mem_singleton]
      constructor
      · intro hw
        rcases klass w hw with ⟨i,rfl⟩|rfl|rfl
        · exact Or.inl (Or.inl ⟨i,rfl⟩)
        · exact Or.inr rfl
        · exact Or.inl (Or.inr rfl)
      · rintro ((⟨i,rfl⟩|rfl)|rfl) <;> first | exact raw _ | exact sd | exact used
    · simp only [inv,decide_eq_false used,Bool.false_eq_true,ite_false,List.not_mem_nil,or_false]
      constructor
      · intro hw
        rcases klass w hw with ⟨i,rfl⟩|rfl|rfl
        · exact Or.inl ⟨i,rfl⟩
        · exact (used hw).elim
        · exact Or.inr rfl
      · rintro (⟨i,rfl⟩|rfl) <;> first | exact raw _ | exact sd
  exact ⟨k,sz.trans cap,inv,eq ▸ clean⟩
#print axioms CoPhysical3174.extract
end
end CoPhysical3174
