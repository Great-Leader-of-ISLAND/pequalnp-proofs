import PEqualNP.Co4358Syntax
import PEqualNP.CoPaid3143

namespace CoNum4358
open PEqualNP.MetaComplexity CoThetaFreeCore CoThetaNine CoThetaPhysical

abbrev PhysGate := PEqualNP.CircuitLowerBounds.Gate
abbrev PhysCircuit := PEqualNP.CircuitLowerBounds.Circuit

def target (x : Fin 7 → Bool) : Bool :=
  ([1,12,4,15,26,35,46,36] : List Nat).any fun e =>
    x (Fin.ofNat 7 (e/10)) && x (Fin.ofNat 7 (e%10))

def ren : Fin 7 → Fin 7 := ![3,0,2,6,4,5,1]
def raw (i : Fin 7) (r : SmallInput) := raw7 (ren i) r
def input : List (SmallInput → Bool) := List.ofFn raw
def seed : List (SmallInput → Bool) := absentBit :: (fun _ => true) :: input

theorem input_known : ∀ a∈input,a∈seed := by
  intro a ha
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha)

theorem constants (b : Bool) : (fun _ : SmallInput => b)∈seed := by
  cases b
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem seed_norm : ∀ a∈seed,norm (0 : SmallInput) a∈vertices7 := by
  intro a h
  rcases List.mem_cons.mp h with rfl | h
  · exact List.mem_cons_self
  rcases List.mem_cons.mp h with rfl | h
  · exact List.mem_cons_self
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
  have hr : norm (0 : SmallInput) (raw i)=raw7 (ren i) := by
    funext r
    have z : raw7 (ren i) 0=false := by simp [raw7]
    simp [raw,CoThetaFreeCore.norm,CoThetaFreeCore.phase,z]
  rw [hr]
  exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨_,rfl⟩)

theorem normalized {n w} (h : Ordinary seed n w) :
    ∃ ys,Free vertices7 n ys ∧ ∀ a∈w,norm (0 : SmallInput) a∈ys := by
  induction h with
  | start => exact ⟨_,Free.start,seed_norm⟩
  | @inv n ws a pre ha ih =>
    obtain ⟨ys,hys,sub⟩ := ih
    refine ⟨ys,hys,?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | old
    · rw [normalize_unary]
      exact sub a ha
    · exact sub z old
  | @binary n ws a b pre join ha hb ih =>
    obtain ⟨ys,hys,sub⟩ := ih
    have step := Free.binary hys (normalizedKind join (a 0) (b 0)) (sub a ha) (sub b hb)
    refine ⟨_,step,?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | old
    · rw [normalize_binary]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub z old)

private theorem read_map {α : Type} (ws : List (α → Bool)) (i : Nat) (r : α) :
    (ws.map (fun f => f r)).getD i false = ws.getD i absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? <;> rfl

theorem sample_target : ∀ r : SmallInput,target (fun i => raw i r)=ans7 r := by
  decide +kernel

/-- Counts only effective binary gate forms. Input size and output are unrestricted. -/
theorem physical_price (lower : SignedLower) (C : PhysCircuit) (fan : FanInTwo C)
    (agrees : ∀ x : Fin 7 → Bool,C.eval (List.ofFn x)=target x) :
    11 ≤ cost (C.gates.map gateForm) := by
  let fs := C.gates.map gateForm
  let ws := execute fs input
  let out := ws.getD C.output absentBit
  have word : out=ans7 := by
    funext r
    have ev := congrArg (fun b : List Bool => b.getD C.output false) (circuit_rows C fan input r)
    change (ws.map (fun f => f r)).getD C.output false=C.eval (input.map (fun f => f r)) at ev
    rw [read_map] at ev
    have h0 : input.map (fun f => f r) = List.ofFn (fun i => raw i r) := by
      simp [input,List.map_ofFn]
    rw [h0] at ev
    exact ev.trans ((agrees _).trans (sample_target r))
  obtain ⟨ys,prog,known⟩ := pins_to_program fs input seed seed 0 Ordinary.start constants input_known
  have member : out∈ys := by
    cases ee : ws[C.output]? with
    | none =>
      have eq : out=absentBit := by simp [out,List.getD_eq_getElem?_getD,ee]
      have nx : ans7 (5 : SmallInput) ≠ absentBit (5 : SmallInput) := by decide +kernel
      exact (nx (congrFun (word.symm.trans eq) _)).elim
    | some a =>
      have eq : out=a := by simp [out,List.getD_eq_getElem?_getD,ee]
      rw [eq]
      exact known a (List.mem_of_getElem? ee)
  obtain ⟨zs,hzs,sub⟩ := normalized prog
  have n0 : norm (0 : SmallInput) ans7=ans7 := by
    have e : ans7 0=false := by decide +kernel
    funext r
    simp [CoThetaFreeCore.norm,CoThetaFreeCore.phase,e]
  have hi := sub out member
  rw [word,n0] at hi
  simpa [fs] using lower hzs hi

private theorem one_charge (gs : List PhysGate)
    (tight : gs.length ≤ cost (gs.map gateForm)) :
    ∀ g∈gs,(gateForm g).binaryCost=1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hlen := pin_cost_length (gs.map gateForm)
    have hgate : (gateForm g).binaryCost≤1 := by cases gateForm g <;> simp [PinForm.binaryCost]
    simp only [List.map_cons,List.length_cons,cost] at tight
    rw [List.length_map] at hlen
    intro x hx
    rcases List.mem_cons.mp hx with rfl | old
    · omega
    · exact ih (by omega) _ old

theorem all_binary (lower : SignedLower) (C : PhysCircuit) (fan : FanInTwo C)
    (size : C.size=11) (agrees : ∀ x : Fin 7 → Bool,C.eval (List.ofFn x)=target x) :
    ∀ g∈C.gates,∃ b : Gate,b.phys=g := by
  have price := physical_price lower C fan agrees
  change C.gates.length=11 at size
  have all := one_charge C.gates (by omega)
  intro g hg
  have charged := all g hg
  have len := (fan g hg).2
  obtain ⟨kind,pins⟩ := g
  change pins.length≤2 at len
  cases pins with
  | nil => cases kind <;> simp [gateForm,PinForm.binaryCost] at charged
  | cons a tail =>
    cases tail with
    | nil => cases kind <;> simp [gateForm,PinForm.binaryCost] at charged
    | cons b tail =>
      cases tail with
      | nil =>
        cases kind <;> simp [gateForm,PinForm.binaryCost] at charged
        · exact ⟨⟨false,a,b⟩,rfl⟩
        · exact ⟨⟨true,a,b⟩,rfl⟩
      | cons u us => simp at len

def Shape (s t : Nat) (g h : PhysGate) : Prop :=
  g.op=h.op ∧ List.Forall₂ (fun a b : Nat => b=a+1 ∨ b=0 ∧ (a=s ∨ a=t)) g.inputs h.inputs

private theorem pin_mark {s t a b : Nat} (h : b=a+1 ∨ b=0 ∧ (a=s ∨ a=t)) :
    ∃ m : Bool,(if m then 0 else a+1)=b ∧ (m=true → a=s ∨ a=t) := by
  rcases h with eq | ⟨eq,allowed⟩
  · exact ⟨false,eq.symm,by simp⟩
  · exact ⟨true,eq.symm,fun _ => allowed⟩

private theorem pair_mark {s t : Nat} (g : Gate) (h : PhysGate) (ok : Shape s t g.phys h) :
    ∃ m : Bool×Bool,g.lifted m=h ∧ Allowed s t (g,m) := by
  obtain ⟨kind,pins⟩ := h
  obtain ⟨hk,hp⟩ := ok
  change g.phys.op=kind at hk
  subst kind
  change List.Forall₂ _ [g.a,g.b] pins at hp
  cases hp with
  | cons ha htail =>
    cases htail with
    | cons hb hend =>
      cases hend
      obtain ⟨ma,ea,wa⟩ := pin_mark ha
      obtain ⟨mb,eb,wb⟩ := pin_mark hb
      exact ⟨(ma,mb),by simp [Gate.lifted,Gate.phys,ea,eb],wa,wb⟩

theorem decode_paired {s t : Nat} {gs hs : List PhysGate}
    (binary : ∀ g∈gs,∃ b : Gate,b.phys=g)
    (matchPins : List.Forall₂ (Shape s t) gs hs) :
    ∃ ps : List Marked,ps.map (fun p => p.1.phys)=gs ∧
      ps.map (fun p => p.1.lifted p.2)=hs ∧ ∀ p∈ps,Allowed s t p := by
  induction matchPins with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | @cons g h gs hs head tail ih =>
    obtain ⟨b,eq⟩ := binary g (by simp)
    obtain ⟨mark,hm,ha⟩ := pair_mark b h (by simpa only [eq] using head)
    obtain ⟨ps,p1,p2,p3⟩ := ih (fun x hx => binary x (List.mem_cons_of_mem _ hx))
    refine ⟨(b,mark)::ps,by simp [eq,p1],by simp [hm,p2],?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | old
    · exact ha
    · exact p3 _ old

private theorem physical_one (g : Gate) (ws : List Bool) :
    g.phys.op.eval (g.phys.inputs.map (fun i => ws.getD i false))=g.val ws := by
  obtain ⟨k,a,b⟩ := g
  cases k <;> simp [Gate.phys,Gate.val,op,PEqualNP.CircuitLowerBounds.GateOp.eval]

private theorem physical_lift (p : Marked) (ws : List Bool) :
    (p.1.lifted p.2).op.eval ((p.1.lifted p.2).inputs.map (fun i =>
      (true::ws).getD i false))=Marked.val p ws := by
  obtain ⟨⟨k,a,b⟩,ma,mb⟩ := p
  cases k <;> cases ma <;> cases mb <;>
    simp [Gate.lifted,Marked.val,op,PEqualNP.CircuitLowerBounds.GateOp.eval,
      List.getD_eq_getElem?_getD]

theorem ordinary_rows (ps : List Marked) (ws : List Bool) :
    (ps.map (fun p => p.1.phys)).foldl (fun w (g : PhysGate) =>
      w++[g.op.eval (g.inputs.map (fun i => w.getD i false))]) ws =
    ordinary (ps.map Prod.fst) ws := by
  induction ps generalizing ws with
  | nil => rfl
  | cons g tail ih =>
    simpa only [List.map_cons,List.foldl_cons,ordinary,physical_one] using
      ih (ws++[g.1.val ws])

theorem raised_rows (ps : List Marked) (ws : List Bool) :
    (ps.map (fun p => p.1.lifted p.2)).foldl (fun w (g : PhysGate) =>
      w++[g.op.eval (g.inputs.map (fun i => w.getD i false))]) (true::ws) =
    true::raised ps ws := by
  induction ps generalizing ws with
  | nil => rfl
  | cons g tail ih =>
    simpa only [List.map_cons,List.foldl_cons,raised,physical_lift,List.cons_append] using
      ih (ws++[Marked.val g ws])

theorem reader_count (ps : List Marked) :
    ((ps.map (fun p => p.1.phys)).filter (fun g =>
      g.op.eval [true,false] && g.inputs.contains 2)).length =
    ((ps.map Prod.fst).filter Gate.reads2).length := by
  induction ps with
  | nil => rfl
  | cons g tail ih =>
    have e : (g.1.phys.op.eval [true,false] && g.1.phys.inputs.contains 2) = g.1.reads2 := by
      obtain ⟨⟨k,a,b⟩,m⟩ := g
      cases k <;> rfl
    simp only [List.map_cons,List.filter_cons,e]
    split <;> simp only [List.length_cons,ih]

end CoNum4358
