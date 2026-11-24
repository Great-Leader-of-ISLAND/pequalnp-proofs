import PEqualNP.CoRaw1888

namespace CoTransfer1888
open CoRaw1888 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def nine (y : Fin 9→Bool) :=
  (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) ||
  (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) ||
  (y 6 && y 8) || (y 8 && y 5)

def wiring : Vertex→Vertex := ![9,7,5,8,6,4,2,0,3,1]
def nineRow (x : Vertex→Bool) : Fin 9→Bool := fun i => x (wiring i.castSucc)
def star (x : Vertex→Bool) := x 1 && (seed x || x 6)
private theorem distribute (a b c : Bool) : (a && (b || c))=((a && b)||(a && c)) := by cases a <;> cases b <;> cases c <;> rfl

theorem factor (x : Vertex→Bool) : target x=(star x || nine (nineRow x)) := by
  change _=((x 1 && ((x 0 || x 2) || x 6)) ||
    (((x 9 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 9) ||
     (x 9 && x 4) || (x 7 && x 2) || (x 5 && x 0) || (x 8 && x 3) || (x 4 && x 0) ||
     (x 2 && x 3) || (x 3 && x 4))))
  simp only [target,distribute]
  ac_rfl

def bump (i : Nat) := if i<9 then i else i+4

def move (g : Gate) : Gate := ⟨g.op,g.inputs.map bump⟩
def preA : Gate := ⟨.or,[10,4]⟩
def preB : Gate := ⟨.and,[9,11]⟩
def finGate (D : Circuit) : Gate := ⟨.or,[12,bump D.output]⟩
def assemble (D : Circuit) : Circuit :=
  ⟨([preA,preB] ++ D.gates.map move) ++ [finGate D],13+D.size⟩

theorem size (D : Circuit) : (assemble D).size=D.size+3 := by simp [assemble,Circuit.size] <;> omega

theorem legal (D : Circuit) (ok : FanInTwo D) : FanInTwo (assemble D) := by
  intro g hg
  change g∈([preA,preB] ++ D.gates.map move) ++ [finGate D] at hg
  rcases List.mem_append.mp hg with prev|last
  · rcases List.mem_append.mp prev with head|tail
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at head
      rcases head with rfl|rfl <;> simp [preA,preB]
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp tail
      simpa [move] using ok o ho
  · obtain rfl := List.mem_singleton.mp last
    simp [finGate]

private def step (ws : List Bool) (g : Gate) := ws++[g.op.eval (g.inputs.map fun i => ws.getD i false)]
private def insertions (x : Vertex→Bool) := [x 1,seed x,seed x || x 6,star x]

private theorem begin_run (x : Vertex→Bool) : [preA,preB].foldl step (bank wiring x)=List.ofFn (nineRow x)++insertions x := by
  have b : bank wiring x=[x 9,x 7,x 5,x 8,x 6,x 4,x 2,x 0,x 3,x 1,seed x] := rfl
  have r : List.ofFn (nineRow x)=[x 9,x 7,x 5,x 8,x 6,x 4,x 2,x 0,x 3] := rfl
  rw [b,r]
  simp [step,preA,preB,GateOp.eval,insertions,star,List.getD_eq_getElem?_getD]

private theorem read_shift (base extra tail : List Bool) (len : base.length=9) (added : extra.length=4) (i : Nat) :
    ((base++extra)++tail).getD (bump i) false=(base++tail).getD i false := by
  have both : (base++extra).length=13 := by simp [len,added]
  simp only [List.getD_eq_getElem?_getD]
  by_cases hi : i<9
  · have a : i<base.length := by omega
    have b : i<(base++extra).length := by omega
    simp only [bump,if_pos hi,List.getElem?_append_left a,List.getElem?_append_left b]
  · have a : base.length ≤ i := by omega
    have b : (base++extra).length ≤ i+4 := by omega
    simp only [bump,if_neg hi,List.getElem?_append_right a,List.getElem?_append_right b]
    rw [show i+4-(base++extra).length=i-base.length by omega]

private theorem simulation (gs : List Gate) (base extra : List Bool) (len : base.length=9) (added : extra.length=4) (tail : List Bool) :
    ∃ last,gs.foldl step (base++tail)=base++last ∧ (gs.map move).foldl step ((base++extra)++tail)=(base++extra)++last := by
  induction gs generalizing tail with
  | nil => exact ⟨tail,rfl,rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => (base++tail).getD i false)
    have pins : ((g.inputs.map bump).map (fun i => ((base++extra)++tail).getD i false)) =
        g.inputs.map (fun i => (base++tail).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => read_shift base extra tail len added i)
    obtain ⟨last,old,newer⟩ := ih (tail++[v])
    refine ⟨last,?_,?_⟩
    · simpa only [List.foldl_cons,step,List.append_assoc,v] using old
    · change (gs.map move).foldl step (((base++extra)++tail)++[g.op.eval ((g.inputs.map bump).map
          (fun i => ((base++extra)++tail).getD i false))])=(base++extra)++last
      rw [pins]
      simpa only [List.append_assoc,v] using newer

private theorem wire_len (gs : List Gate) (s : List Bool) : (gs.foldl step s).length=s.length+gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih => simp [step,ih] <;> omega

/-- The two extra operations precede the old DAG. Thus an old invalid read stays
    invalid even when it is the chosen output. The final OR is evaluated last. -/
theorem evaluate (D : Circuit) (x : Vertex→Bool) :
    (assemble D).eval (bank wiring x)=(star x || D.eval (List.ofFn (nineRow x))) := by
  let base := List.ofFn (nineRow x)
  let extra := insertions x
  have len : base.length=9 := by simp [base]
  have added : extra.length=4 := rfl
  obtain ⟨last,old,newer⟩ := simulation D.gates base extra len added []
  simp only [List.append_nil] at old newer
  have lt := wire_len D.gates base
  rw [old,List.length_append,len] at lt
  have lastLen : last.length=D.size := by simpa [Circuit.size] using lt
  let ws := (base++extra)++last
  have n : ws.length=13+D.size := by simp [ws,len,added,lastLen] <;> omega
  have cut : 12<(base++extra).length := by simp [len,added]
  have head : ws.getD 12 false=star x := by
    simp only [ws,List.getD_eq_getElem?_getD,List.getElem?_append_left cut,
      List.getElem?_append_right (show base.length≤12 by omega),len]
    rfl
  have out : ws.getD (bump D.output) false=D.eval base := by
    change _=(D.gates.foldl step base).getD D.output false
    rw [old]
    exact read_shift base extra last len added D.output
  change ((([preA,preB]++D.gates.map move)++[finGate D]).foldl step (bank wiring x)).getD (13+D.size) false=_
  rw [List.foldl_append,List.foldl_append,begin_run]
  change ([finGate D].foldl step ((D.gates.map move).foldl step (base++extra))).getD (13+D.size) false=_
  rw [newer]
  change (ws++[(finGate D).op.eval ((finGate D).inputs.map fun i => ws.getD i false)]).getD (13+D.size) false=_
  rw [←n]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (le_refl ws.length),Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
  change (ws.getD 12 false || (ws.getD (bump D.output) false || false))= (star x || D.eval base)
  rw [head,out,Bool.or_false]

def NoEighteen := ∀ (C : Circuit) (σ : Vertex→Vertex),FanInTwo C → C.size≤18 →
  ∃ x : Vertex→Bool,C.eval (bank σ x)≠target x

theorem counterexample_of_nine (D : Circuit) (ok : FanInTwo D) (small : D.size≤15)
    (nine_ok : ∀y : Fin 9→Bool,D.eval (List.ofFn y)=nine y) :
    FanInTwo (assemble D) ∧ (assemble D).size≤18 ∧ ∀x,(assemble D).eval (bank wiring x)=target x := by
  refine ⟨legal D ok,by rw [size]; omega,?_⟩
  intro x
  rw [evaluate,nine_ok,←factor]

theorem nine_sixteen_necessary (exclude : NoEighteen) (D : Circuit) (ok : FanInTwo D)
    (nine_ok : ∀y : Fin 9→Bool,D.eval (List.ofFn y)=nine y) : 16≤D.size := by
  by_contra! tooSmall
  obtain ⟨ok',cap,correct⟩ := counterexample_of_nine D ok (by omega) nine_ok
  obtain ⟨x,bad⟩ := exclude (assemble D) wiring ok' cap
  exact bad (correct x)

theorem implies_meta_670 (exclude : NoEighteen) : ¬ HasCircuitSize 9 nine 15 := by
  rintro ⟨D,ok,small,agrees⟩
  have lower := nine_sixteen_necessary exclude D ok agrees
  omega

theorem exact_1888_implies_670 (exclude :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  apply implies_meta_670
  intro C σ fan cap
  obtain ⟨x,bad⟩ := exclude C σ fan cap
  refine ⟨x,fun same => bad ?_⟩
  change C.eval (bank σ x)=_
  rw [same]
  unfold target
  ac_rfl

#print axioms CoTransfer1888.exact_1888_implies_670
#print axioms CoTransfer1888.implies_meta_670
end CoTransfer1888
