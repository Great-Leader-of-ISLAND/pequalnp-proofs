import PEqualNP.CoPaid3143

namespace CoPhysical3648
open CoThetaNine CoThetaFreeCore
open PEqualNP.MetaComplexity

def seed : Input → Bool := or04.value
def bank : List (Input→Bool) := seed::vertices

def appendGate (w : List (Input→Bool)) (g : BinaryGate) :=
  w ++ [fun r => g.op (w.getD g.left absentBit r) (w.getD g.right absentBit r)]
def execute (gs : List BinaryGate) (w : List (Input→Bool)) := gs.foldl appendGate w
def start : List (Input→Bool) := List.ofFn vtx ++ [seed,absentBit]

private theorem mapRead (w : List (Input→Bool)) (i : Nat) (r : Input) :
    (w.map (fun f => f r)).getD i false = w.getD i absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

private theorem evalFold (gs : List BinaryGate) (w : List (Input→Bool)) (r : Input) :
    (execute gs w).map (fun f => f r) =
      gs.foldl (fun t g => t ++ [g.op (t.getD g.left false) (t.getD g.right false)]) (w.map (fun f => f r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (appendGate w g)).map _ = gs.foldl _ _
    rw [ih]
    simp [appendGate,mapRead]

theorem pattern_table : ∀ (a b u v x y : Bool),
    phase ((u==a) && (v==b)) ((x==a) && (y==b)) =
      applyKind (normalizedKind false (u==a) (v==b)) (phase u x) (phase v y) := by decide

private theorem supplied {ys w : List (Input→Bool)} (sub : ∀ f∈w,norm (row 0) f∈ys)
    (hz : absentBit∈ys) (i : Nat) : norm (row 0) (w.getD i absentBit)∈ys := by
  cases he : w[i]? with
  | none =>
    simp only [List.getD_eq_getElem?_getD,he,Option.getD_none]
    exact hz
  | some g =>
    simp only [List.getD_eq_getElem?_getD,he,Option.getD_some]
    exact sub g (List.mem_of_getElem? he)

def permitted (g : BinaryGate) := ∃ a b : Bool, g.op=fun x y => (x==a) && (y==b)

theorem simulate (gs : List BinaryGate) (leg : ∀ g∈gs,permitted g)
    (w ys : List (Input→Bool)) {n : Nat} (pre : Free bank n ys) (hz : absentBit∈ys)
    (cov : ∀ f∈w,norm (row 0) f∈ys) :
    ∃ zs, Free bank (n+gs.length) zs ∧ absentBit∈zs ∧ ∀ f∈execute gs w,norm (row 0) f∈zs := by
  induction gs generalizing n w ys with
  | nil => exact ⟨ys,by simpa using pre,hz,cov⟩
  | cons g gs ih =>
    obtain ⟨a,b,op⟩ := leg g List.mem_cons_self
    let x := w.getD g.left absentBit
    let y := w.getD g.right absentBit
    let kind := normalizedKind false (x (row 0)==a) (y (row 0)==b)
    let z : Input→Bool := fun r => applyKind kind (norm (row 0) x r) (norm (row 0) y r)
    have step : Free bank (n+1) (z::ys) :=
      Free.binary pre kind (supplied cov hz g.left) (supplied cov hz g.right)
    have eq : norm (row 0) (fun r => g.op (x r) (y r)) = z := by
      funext r
      rw [op]
      exact pattern_table a b (x (row 0)) (y (row 0)) (x r) (y r)
    have lift : ∀ f∈appendGate w g,norm (row 0) f∈z::ys := by
      intro f hf
      rcases List.mem_append.mp hf with old|new
      · exact List.mem_cons_of_mem _ (cov f old)
      · obtain rfl := List.mem_singleton.mp new
        exact eq ▸ List.mem_cons_self
    obtain ⟨zs,p,z0,cs⟩ := ih (fun h hh => leg h (List.mem_cons_of_mem _ hh)) (appendGate w g)
      (z::ys) step (List.mem_cons_of_mem _ hz) lift
    refine ⟨zs,?_,z0,cs⟩
    have e : n+(g::gs).length=n+1+gs.length := by simp; omega
    exact e ▸ p

theorem physical (C : BinaryCircuit) (flag : Bool) (leg : ∀ g∈C.gates,permitted g)
    (solves : ∀ r : Input, (C.eval (List.ofFn (fun i => vtx i r)++[seed r,false]) != flag)=ans r) :
    ∃ gs, gs.length=C.size ∧ sufficient bank ans gs := by
  have init : ∀ f∈start,norm (row 0) f∈bank := by
    intro f hf
    rcases List.mem_append.mp hf with raw|more
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp raw
      have e : norm (row 0) (vtx i)=vtx i := by
        have z : ∀ j : Fin 9, vtx j (row 0)=false := by decide
        funext r
        simp [CoThetaFreeCore.norm,phase,z]
      rw [e]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    · rcases List.mem_cons.mp more with e|more
      · subst f
        have e : norm (row 0) seed=seed := by
          have z : seed (row 0)=false := rfl
          funext r
          simp [CoThetaFreeCore.norm,phase,z]
        exact e ▸ List.mem_cons_self
      · obtain rfl := List.mem_singleton.mp more
        exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨zs,prog,hz,cs⟩ := simulate C.gates leg start bank Free.start
    (List.mem_cons_of_mem _ List.mem_cons_self) init
  let f := (execute C.gates start).getD C.output absentBit
  have ok (r : Input) : (f r != flag)=ans r := by
    have ev := congrArg (fun t : List Bool => t.getD C.output false) (evalFold C.gates start r)
    rw [mapRead] at ev
    change f r=C.eval (start.map (fun t => t r)) at ev
    have e : start.map (fun t => t r)=List.ofFn (fun i => vtx i r)++[seed r,false] := by
      simp [start,List.map_ofFn,absentBit]
    rw [e] at ev
    simpa only [ev] using solves r
  have eq : norm (row 0) f=ans := by
    funext r
    have h0 := ok (row 0)
    have h := ok r
    have z : ans (row 0)=false := by decide
    rw [z] at h0
    change phase (f (row 0)) (f r)=ans r
    cases a : f (row 0) <;> cases b : f r <;> cases c : ans r <;> cases flag <;> simp_all [phase]
  have read := supplied cs hz C.output
  change norm (row 0) f∈zs at read
  rw [eq] at read
  obtain ⟨gs,len,okTrace,out⟩ := trace_of_free prog
  exact ⟨gs,by simpa [BinaryCircuit.size] using len,okTrace,out ▸ read⟩


theorem conditional (lower : SignedLower) : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit), x1.size = (13 : ℕ) → x1.output < (24 : ℕ) → (∀ (x4 : ℕ) (x5 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[x4]? = Option.some x5 → x5.left < (11 : ℕ) + x4 ∧ x5.right < (11 : ℕ) + x4 ∧ ∃ (x7 : Bool) (x8 : Bool), x5.op = fun (x9 x10 : Bool) => x9 == x7 && x10 == x8) → ∃ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), Bool.false]) != Bool.false) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  intro C size _ pins
  by_contra fail
  have leg : ∀ g ∈ C.gates, permitted g := by
    intro g hg
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
    exact (pins i g hi).2.2
  have correct (r : Input) : (C.eval (List.ofFn (fun i => vtx i r)++[seed r,false]) != false)=ans r := by
    by_contra differs
    exact fail ⟨fun i => vtx i r,differs⟩
  obtain ⟨gs,hs,reg,out⟩ := physical C false leg correct
  have raw (i : Fin 9) : vtx i ∈ vertices :=
    List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have usable : sufficient vertices ans (or04::gs) := ⟨⟨raw 0,raw 4,reg⟩,out⟩
  have bound := fixed_head_lower lower (fixed_or04 gs usable)
  omega

#print axioms conditional
end CoPhysical3648
