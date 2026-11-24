import PEqualNP.Outside.L_meta_1778

namespace PEqualNP.Research.FalseCode
open CircuitLowerBounds MetaComplexity PEqualNP.Outside.L_meta_1778

def pick (g : Gate) (w : List Bool) := (g.inputs.map fun i => w.getD i false).headD true
def countA (gs : List Gate) := (gs.filter fun g => g.op.eval []).length
def code : List Gate → List Bool → Nat
  | [],_ => 0
  | g::gs,w =>
    let rest := code gs (step w g)
    if g.op.eval [] then 2*rest + (pick g w).toNat else rest

theorem code_lt (gs : List Gate) (w : List Bool) : code gs w < 2 ^ countA gs := by
  induction gs generalizing w with
  | nil => decide
  | cons g gs ih =>
    have h := ih (step w g)
    by_cases a : g.op.eval [] = true
    · have len : countA (g::gs)=countA gs+1 := by simp [countA,a]
      rw [len,pow_succ]
      cases v : pick g w <;> simp [code,a,v] <;> omega
    · simpa [code,countA,a] using h

def related (x y z : List Bool) := ∀ i, x.getD i false=false → y.getD i false=false → z.getD i false=false

theorem gate_join (g : Gate) (h : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length≤2)
    (x y z : List Bool) (rel : related x y z) (pickOk : g.op.eval []=true → pick g x=pick g y) :
    g.op.eval (g.inputs.map fun i => x.getD i false)=false →
    g.op.eval (g.inputs.map fun i => y.getD i false)=false →
    g.op.eval (g.inputs.map fun i => z.getD i false)=false := by
  obtain ⟨op,small⟩ := h
  rcases gate_cases g.inputs small with empty | ⟨j,one⟩ | ⟨i,j,two⟩
  · rcases op with e|e <;> simp [e,empty,GateOp.eval]
  · rcases op with e|e <;> simpa [e,one,GateOp.eval] using rel j
  · rcases op with e|e
    · have same := pickOk (by simp [e,GateOp.eval])
      simp [pick,two] at same
      simp [two,e,GateOp.eval]
      cases xi : x.getD i false <;> cases yi : y.getD i false <;>
        simp_all [Bool.and_eq_false_iff] <;> grind [related]
    · simp [e,two,GateOp.eval]
      grind [related]

theorem join_wires (gs : List Gate) (x y z : List Bool)
    (legal : ∀ g∈gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length≤2)
    (xy : x.length=y.length) (xz : x.length=z.length)
    (rel : related x y z) (same : code gs x=code gs y) :
    related (wv gs x) (wv gs y) (wv gs z) := by
  induction gs generalizing x y z with
  | nil => exact rel
  | cons g gs ih =>
    have rest : code gs (step x g)=code gs (step y g) ∧
        (g.op.eval []=true → pick g x=pick g y) := by
      by_cases a : g.op.eval []=true
      · cases hx : pick g x <;> cases hy : pick g y <;> simp [code,a,hx,hy] at same ⊢ <;> omega
      · exact ⟨by simpa [code,a] using same,fun h => False.elim (a h)⟩
    apply ih (step x g) (step y g) (step z g) (fun q hq => legal q (List.mem_cons_of_mem _ hq))
      (by simp [step,xy]) (by simp [step,xz]) _ rest.1
    intro i
    simp only [step_getD,←xy,←xz]
    split
    · exact rel i
    · split
      · exact gate_join g (legal g (by simp)) x y z rel rest.2
      · simp

theorem collision {n} (C : Circuit) (hm : Monotone2 C) (x y : Fin n→Bool)
    (same : code C.gates (List.ofFn x) = code C.gates (List.ofFn y))
    (hx : circuitFun n C x=false) (hy : circuitFun n C y=false) :
    circuitFun n C (fun j => x j || y j)=false := by
  rw [cf_eq] at *
  apply join_wires C.gates (List.ofFn x) (List.ofFn y) _ (mono2 C hm)
    (by simp) (by simp) _ same _ hx hy
  intro i
  simp only [ofFn_getD]
  split <;> simp_all

theorem packing {n : Nat} {T : Type} [Fintype T] (C : Circuit) (hm : Monotone2 C)
    (rows : T → Fin n → Bool) (off : ∀ a, circuitFun n C (rows a)=false)
    (cross : ∀ a b, a≠b → circuitFun n C (fun i => rows a i || rows b i)=true) :
    Fintype.card T ≤ 2 ^ countA C.gates := by
  let key (a : T) : Fin (2 ^ countA C.gates) := ⟨_,code_lt C.gates (List.ofFn (rows a))⟩
  have inj : Function.Injective key := by
    intro a b h
    by_contra ne
    have bad := collision C hm _ _ (congrArg Fin.val h) (off a) (off b)
    rw [cross a b ne] at bad
    contradiction
  simpa using Fintype.card_le_of_injective key inj
end PEqualNP.Research.FalseCode
