import PEqualNP.CoThetaOriginal

namespace CoThetaNine
open CoThetaFreeCore CoThetaPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def tailInputs03 : List (Input→Bool) := List.ofFn vtx ++ [and03.value]
def seed03 : List (Input→Bool) := absentBit::(fun _ => true)::tailInputs03

theorem norm_inputs03 : ∀ f∈seed03.map (norm (row 0)), f∈and03.value::vertices := by
  intro f hf
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hf
  have hz : absentBit∈and03.value::vertices := List.mem_cons_of_mem _ List.mem_cons_self
  rcases List.mem_cons.mp ht with t0|ht
  · subst t
    exact hz
  rcases List.mem_cons.mp ht with t1|ht
  · subst t
    exact hz
  rcases List.mem_append.mp ht with hin|head
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp hin
    subst t
    have lo : ∀ j : Fin 9, vtx j (row 0)=false := by decide
    have eq : norm (row 0) (vtx i)=vtx i := by
      funext r
      simp [CoThetaFreeCore.norm,lo,phase]
    rw [eq]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  · obtain rfl := List.mem_singleton.mp head
    have lo : and03.value (row 0)=false := by decide
    have eq : norm (row 0) and03.value=and03.value := by
      funext r
      simp [CoThetaFreeCore.norm,lo,phase]
    exact eq ▸ List.mem_cons_self

theorem nonedge_trace (D : Circuit) (fan : FanInTwo D)
    (correct : ∀ r : Input, D.eval (List.ofFn (fun i => vtx i r) ++ [vtx 0 r && vtx 3 r])=ans r) :
    ∃ gs, gs.length ≤ cost (D.gates.map gateForm) ∧ sufficient vertices ans (and03::gs) := by
  let fs := D.gates.map gateForm
  let result := (execute fs tailInputs03).getD D.output absentBit
  have ep (r : Input) : tailInputs03.map (fun f => f r)=
      List.ofFn (fun i => vtx i r) ++ [vtx 0 r && vtx 3 r] := by
    simp [tailInputs03,List.map_ofFn,and03,TraceGate.value,applyKind]
  have correctWord : result=ans := by
    funext r
    have h := circuit_rows D fan tailInputs03 r
    have read := congrArg (fun ws : List Bool => ws.getD D.output false) h
    change ((execute fs tailInputs03).map (fun f => f r)).getD D.output false=_ at read
    have eq (w : List (Input→Bool)) (i : Nat) :
        (w.map (fun f => f r)).getD i false = w.getD i absentBit r := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
      cases w[i]? <;> rfl
    rw [eq,ep] at read
    exact read.trans (correct r)
  have present : result∈execute fs tailInputs03 := by
    cases e : (execute fs tailInputs03)[D.output]? with
    | none =>
      have no : result=absentBit := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (ans_not_zero (correctWord.symm.trans no)).elim
    | some w =>
      have eq : result=w := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (congrArg (fun v => v∈execute fs tailInputs03) eq).mpr (List.mem_of_getElem? e)
  have cs (b : Bool) : (fun _ : Input => b)∈seed03 := by
    cases b
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨ys,program,cover⟩ := pins_to_program fs tailInputs03 seed03 seed03 0 Ordinary.start cs
    (fun w h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  obtain ⟨zs,free,sub⟩ := simulate_all_wires (row 0) program
  have hnorm : norm (row 0) ans=ans := by
    have lo : ans (row 0)=false := by decide
    funext r
    simp [CoThetaFreeCore.norm,lo,phase]
  have goalIn := sub result (cover _ present)
  rw [correctWord,hnorm] at goalIn
  obtain ⟨gs,len,reg,eq⟩ := trace_of_free free
  have switch := trace_subset gs norm_inputs03
  have here : ans∈traceWires (and03.value::vertices) gs := switch.2 ans (eq ▸ goalIn)
  refine ⟨gs,?_,⟨⟨?_,?_,switch.1 reg⟩,here⟩⟩
  · simpa [fs] using le_of_eq len
  · exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨0,rfl⟩)
  · exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨3,rfl⟩)

theorem cost_with_not (gs : List Gate) (hasNOT : ∃ g∈gs, g.op = GateOp.not) :
    cost (gs.map gateForm) + 1 ≤ gs.length := by
  induction gs with
  | nil => simp at hasNOT
  | cons g gs ih =>
    obtain ⟨u,hu,op⟩ := hasNOT
    have rest := pin_cost_length (gs.map gateForm)
    simp only [List.length_map] at rest
    have small := form_cost_le g
    rcases List.mem_cons.mp hu with rfl|inside
    · rw [boolCost,op] at small
      simp only [List.map_cons,cost,List.length_cons]
      omega
    · have h := ih ⟨u,inside,op⟩
      have one : boolCost g≤1 := by cases e : g.op <;> simp [boolCost,e]
      simp only [List.map_cons,cost,List.length_cons]
      omega

end CoThetaNine

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1572_aux

-- The wire evaluation lemmas follow L-meta-1353.

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

abbrev AO (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma wires_mono {n : ℕ} (C : Circuit) (hAO : AO C) (x y : Fin n → Bool)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let p : Fin n := ⟨w, hw⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases h : w < n + C.size
    · let k := w - n
      have hk : k < C.gates.length := by dsimp [k]; unfold Circuit.size at h; omega
      have hwk : w = n + k := by dsimp [k]; omega
      rw [hwk]
      refine gate_mono C k hk (hAO _ (List.getElem_mem hk)).1 x y ?_
      intro r _ hr
      exact ih r (by omega)
    · rw [missing_value C x w (by omega)]
      simp

end PEqualNP.Outside.L_meta_1572_aux

namespace PEqualNP.Research.PetersenPrefix

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem preserved (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem atEnd (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

theorem firstValue {n : ℕ} (g : Gate) (tail : List Gate) (o : ℕ) (x : Fin n → Bool) :
    (Circuit.wires ⟨g :: tail,o⟩ (List.ofFn x)).getD n false =
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
  let w := List.ofFn x
  have hl : w.length = n := by simp [w]
  change (tail.foldl step (step w g)).getD n false = _
  rw [preserved tail (step w g) n (by simp [step, hl])]
  simpa only [step, w, List.length_ofFn] using atEnd (List.ofFn x) (g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false))

theorem emptyHead {n : ℕ} (o : ℕ) (x : Fin n → Bool) :
    (Circuit.wires ⟨[],o⟩ (List.ofFn x)).getD n false = false := by
  change (List.ofFn x).getD n false = false
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp : (List.ofFn x).length ≤ n)] <;> rfl

-- With the semantic head value known, the unmodified tail can be run directly
-- on the list of old inputs followed by that one bit. All wire indices agree.
theorem semanticTail {n : ℕ} (g : Gate) (tail : List Gate) (o : ℕ) (x : Fin n → Bool)
    (b : Bool) (head : (Circuit.wires ⟨g :: tail,o⟩ (List.ofFn x)).getD n false = b) :
    Circuit.eval ⟨g :: tail,o⟩ (List.ofFn x) =
      Circuit.eval ⟨tail,o⟩ (List.ofFn x ++ [b]) := by
  have h := (firstValue g tail o x).symm.trans head
  change (tail.foldl step (List.ofFn x ++ [g.op.eval (g.inputs.map fun i =>
    (List.ofFn x).getD i false)])).getD o false = _
  rw [h]
  rfl

theorem of_tail_bound {n k : ℕ} (h f : (Fin n → Bool) → Bool)
    (hnonzero : ∃ x, h x = true)
    (tailBound : ∀ D : Circuit, FanInTwo D →
      (∀ x, D.eval (List.ofFn x ++ [h x]) = f x) → k ≤ D.size) :
    ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD n false = h x) →
      circuitFun n C = f → k + 1 ≤ C.size := by
  intro C hfan hhead hfun
  obtain ⟨gs,o⟩ := C
  cases gs with
  | nil =>
    obtain ⟨x, hx⟩ := hnonzero
    have bad := hhead x
    rw [emptyHead, hx] at bad <;> cases bad
  | cons g tail =>
    let D : Circuit := ⟨tail,o⟩
    have hf : FanInTwo D := by
      intro gate hmem
      exact hfan gate (List.mem_cons_of_mem g hmem)
    have he : ∀ x, D.eval (List.ofFn x ++ [h x]) = f x := by
      intro x
      exact (semanticTail g tail o x (h x) (hhead x)).symm.trans (congrFun hfun x)
    have hs := tailBound D hf he
    change k ≤ tail.length at hs
    change k + 1 ≤ tail.length + 1
    exact Nat.add_le_add_right hs 1

-- A finite certificate may establish this counterexample-per-tail premise on
-- any fixed subset of assignments. It suffices for either nine-input shard.
theorem of_fourteen_gate_tests (h f : (Fin 9 → Bool) → Bool) (hnonzero : ∃ x, h x = true)
    (tests : ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
      ∃ x, D.eval (List.ofFn x ++ [h x]) ≠ f x) :
    ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = h x) →
      circuitFun 9 C = f → 16 ≤ C.size := by
  apply of_tail_bound (k := 15) h f hnonzero
  intro D hfan hall
  by_contra hn
  obtain ⟨x,hx⟩ := tests D hfan (by omega)
  exact hx (hall x)

theorem not_zero_witness : ∃ x : Fin 9 → Bool, !(x 0) = true := ⟨fun _ => false, rfl⟩

theorem and_zero_one_witness : ∃ x : Fin 9 → Bool, (x 0 && x 1) = true := ⟨fun _ => true, rfl⟩

end PEqualNP.Research.PetersenPrefix

namespace CoActual1669
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.PetersenPrefix
open PEqualNP.Outside.L_meta_1572_aux
abbrev Source := Fin 9 → Bool
def edge (x : Source) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
def head03 (x : Source) : Bool := x 0 && x 3
def tailF (D : Circuit) (x : Source) (b : Bool) := D.eval (List.ofFn x ++ [b])
def edgeGate : Gate := ⟨GateOp.and,[0,1]⟩

abbrev EdgeLower := ∀ C : Circuit, FanInTwo C →
  (∀ x : Source, (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 1)) →
  circuitFun 9 C=edge → 16≤C.size

private theorem realHead (D : Circuit) (x : Source) :
    (Circuit.wires ⟨edgeGate::D.gates,D.output⟩ (List.ofFn x)).getD 9 false = (x 0 && x 1) := by
  rw [firstValue]
  simp [edgeGate,GateOp.eval,List.getD_eq_getElem?_getD,List.getElem?_ofFn]

private theorem snocList (x : Source) (b : Bool) :
    List.ofFn (Fin.snoc x b : Fin 10 → Bool) = List.ofFn x ++ [b] := by
  rw [List.ofFn_succ']
  simp [Fin.snoc]

private theorem tail_mono (D : Circuit) (ao : AO D) (x y : Source) (a b : Bool)
    (le : ∀ i, x i = true → y i = true) (ab : a = true → b = true) :
    tailF D x a = true → tailF D y b = true := by
  have h : ∀ i, (Fin.snoc x a : Fin 10 → Bool) i = true → (Fin.snoc y b : Fin 10 → Bool) i = true := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using ab
    · simpa only [Fin.snoc_castSucc] using le j
  have g := wires_mono D ao (Fin.snoc x a) (Fin.snoc y b) h D.output
  change D.eval (List.ofFn (Fin.snoc x a : Fin 10 → Bool)) = true →
    D.eval (List.ofFn (Fin.snoc y b : Fin 10 → Bool)) = true at g
  simpa only [tailF,snocList] using g

def edges : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def pair (e : Fin 9 × Fin 9) (i : Fin 9) : Bool := decide (i=e.1 ∨ i=e.2)

private theorem edge_witness {x : Source} (hx : edge x=true) :
    ∃ y : Source, (∀ i, y i=true → x i=true) ∧ edge y=true ∧ head03 y=false := by
  have ex : edges.any (fun e => x e.1 && x e.2)=true := by
    simpa [edge,edges,Bool.or_assoc] using hx
  obtain ⟨p,hp,ht⟩ := List.any_eq_true.mp ex
  have concrete : ∀ e∈edges, edge (pair e)=true ∧ head03 (pair e)=false := by decide +kernel
  refine ⟨pair p,?_,concrete _ hp⟩
  intro i h
  have hb := Bool.and_eq_true_iff.mp ht
  rcases of_decide_eq_true h with eq|eq
  · simpa [eq] using hb.1
  · simpa [eq] using hb.2

private theorem monotone_bound (prior : EdgeLower) (D : Circuit) (fan : FanInTwo D) (ao : AO D)
    (correct : ∀ x, tailF D x (head03 x)=edge x) : 15 ≤ D.size := by
  have zeroSlot (x : Source) : tailF D x false=edge x := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      rw [←correct]
      exact tail_mono D ao x x false (head03 x) (fun _ => id) (by simp) h
    · intro h
      obtain ⟨y,le,yes,no⟩ := edge_witness h
      have atY := (correct y).trans yes
      rw [no] at atY
      exact tail_mono D ao y x false false le id atY
  have switched (x : Source) : tailF D x (x 0 && x 1)=edge x := by
    cases z : (x 0 && x 1) with
    | false => exact zeroSlot x
    | true =>
      have e : edge x=true := by simp [edge,z]
      rw [e]
      exact tail_mono D ao x x false true (fun _ => id) (by simp) ((zeroSlot x).trans e)
  let C : Circuit := ⟨edgeGate::D.gates,D.output⟩
  have legal : FanInTwo C := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · decide
    · exact fan _ hg
  have output : circuitFun 9 C=edge := by
    funext x
    exact (semanticTail edgeGate D.gates D.output x _ (realHead D x)).trans (switched x)
  have h := prior C legal (realHead D) output
  change 16 ≤ D.gates.length+1 at h
  change 15 ≤ D.gates.length
  omega

theorem original_given (prior : EdgeLower) (cert : CoThetaBits.certifiedSearch 10 CoThetaBits.raw=false) :
    ∀ C : Circuit, FanInTwo C →
    (∀ x : Source, (C.wires (List.ofFn x)).getD 9 false=head03 x) →
    circuitFun 9 C=edge → 16≤C.size := by
  apply of_tail_bound (k:=15) head03 edge ⟨fun _ => true,rfl⟩
  intro D fan correct
  by_cases neg : ∃ g∈D.gates, g.op=GateOp.not
  · obtain ⟨gs,le,solves⟩ := CoThetaNine.nonedge_trace D fan (fun r =>
      correct (fun i => CoThetaNine.vtx i r))
    have bound := CoThetaNine.fixed_head_lower cert (CoThetaNine.fixed_and03 gs solves)
    have save := CoThetaNine.cost_with_not D.gates neg
    change 15 ≤ D.gates.length
    omega
  · have ao : AO D := by
      intro g hg
      obtain ⟨op,count⟩ := fan g hg
      refine ⟨?_,count⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
      rcases op with a|b|c
      · exact Or.inl a
      · exact Or.inr b
      · exact (neg ⟨g,hg,c⟩).elim
    exact monotone_bound prior D fan ao correct
end CoActual1669
