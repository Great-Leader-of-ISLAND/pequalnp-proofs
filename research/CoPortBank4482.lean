import PEqualNP.Defs
import PEqualNP.CoPortTrace4482

namespace CoPortBank4482
open PEqualNP.CircuitLowerBounds CoPortTrace4482

structure Model (W X : Type) where
  zero : W
  one : W
  join : Bool → W → W → W
  val : W → X → Bool
  atZero : ∀ x, val zero x = false
  atOne : ∀ x, val one x = true
  applyJoin : ∀ d a b x, val (join d a b) x =
    if d then val a x || val b x else val a x && val b x

variable {W X : Type} [DecidableEq W] (M : Model W X)

def mode (g : Gate) : Bool := g.op.eval [true,false]

def operand (ws : List W) (g : Gate) (pin : Nat) : W :=
  match g.inputs[pin]? with
  | some j => ws.getD j M.zero
  | none => if mode g then M.zero else M.one

def value (ws : List W) (g : Gate) : W :=
  M.join (mode g) (operand M ws g 0) (operand M ws g 1)

def write (ws : List W) (g : Gate) := ws ++ [value M ws g]

def history (ws : List W) (gs : List Gate) := gs.foldl (write M) ws

def Covers (T : Finset W) (ws : List W) := ∀ w∈ws, w∈T

theorem read_mem {ws : List W} {T : Finset W} (cov : Covers T ws)
    (zero : M.zero∈T) (j : Nat) : ws.getD j M.zero∈T := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[j]? with
  | none => exact zero
  | some w => exact cov w (List.mem_of_getElem? h)

private theorem operand_mem {ws : List W} {T : Finset W} (cov : Covers T ws)
    (zero : M.zero∈T) (one : M.one∈T) (g : Gate) (i) : operand M ws g i∈T := by
  cases h : g.inputs[i]? with
  | none =>
    simp only [operand,h]
    split <;> assumption
  | some j => simpa only [operand,h] using read_mem M cov zero j

theorem bank (gs : List Gate) {root T n ws} (zero : M.zero∈T) (one : M.one∈T)
    (cov : Covers T ws) (before : Bank M.join root n T) :
    ∃ T', Bank M.join root (n+gs.length) T' ∧ Covers T' (history M ws gs) := by
  induction gs generalizing T n ws with
  | nil => exact ⟨T,by simpa using before,cov⟩
  | cons g gs ih =>
    let z := value M ws g
    have hz : Bank M.join root (n+1) (insert z T) :=
      Bank.gate before (mode g) _ _ (operand_mem M cov zero one g 0) (operand_mem M cov zero one g 1)
    have next : Covers (insert z T) (write M ws g) := by
      intro w hw
      rcases List.mem_append.mp hw with h|h
      · exact Finset.mem_insert_of_mem (cov w h)
      · have eq : w=z := List.mem_singleton.mp h
        exact eq.symm ▸ Finset.mem_insert_self z T
    obtain ⟨P,hP,covered⟩ := ih (Finset.mem_insert_of_mem zero) (Finset.mem_insert_of_mem one) next hz
    exact ⟨P,by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hP,covered⟩

theorem read_values (ws : List W) (x : X) (i : Nat) :
    (ws.map fun w => M.val w x).getD i false = M.val (ws.getD i M.zero) x := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact (M.atZero x).symm
  | some w => rfl

theorem correct_gate (ws : List W) (g : Gate) (x : X)
    (op : g.op=.and ∨ g.op=.or) (arity : g.inputs.length≤2) :
    M.val (value M ws g) x =
      g.op.eval (g.inputs.map fun j => (ws.map fun w => M.val w x).getD j false) := by
  rcases g with ⟨kind,ids⟩
  change kind=.and ∨ kind=.or at op
  change ids.length≤2 at arity
  rcases op with eq|eq <;> subst kind
  all_goals
    rcases ids with _|⟨a,as⟩
    · simp [value,operand,mode,GateOp.eval,M.applyJoin,M.atZero,M.atOne]
    · rcases as with _|⟨b,bs⟩
      · simp [value,operand,mode,GateOp.eval,M.applyJoin,M.atZero,M.atOne,read_values]
      · rcases bs with _|⟨c,cs⟩
        · simp [value,operand,mode,GateOp.eval,M.applyJoin,M.atZero,M.atOne,read_values]
        · simp at arity

theorem correct (gs : List Gate) (ws : List W) (x : X)
    (valid : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    (history M ws gs).map (fun w => M.val w x) =
      gs.foldl (fun wires g => wires++[g.op.eval (g.inputs.map (fun i => wires.getD i false))])
        (ws.map fun w => M.val w x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have legal := valid g List.mem_cons_self
    have rest := ih (write M ws g) (fun a ha => valid a (List.mem_cons_of_mem _ ha))
    change (history M (write M ws g) gs).map _ = _
    rw [rest]
    simp only [write,List.map_append,List.map_cons,List.map_nil,correct_gate M ws g x legal.1 legal.2,
      List.foldl_cons]

end CoPortBank4482
