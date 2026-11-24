import PEqualNP.CoFormula1963Protocol
import PEqualNP.CoFormula1963Geometry
import PEqualNP.CoFormula1963Ledger

namespace CoFormula1963Circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoFormula1963Geometry CoFormula1963Protocol
local notation "X" => (V ⊕ V)
open CoFormula1963Ledger

/-- A constant or a genuine formula. Simplifying constants also handles raw
    out-of-range reads and nullary/unary gates without dummy variables. -/
inductive Term where
  | fixed (b : Bool)
  | tree (t : Expr X)

def val (x : X → Bool) : Term → Bool
  | .fixed b => b
  | .tree t => t.eval x

def cost : Term → ℕ
  | .fixed _ => 0
  | .tree t => t.leaves-1

def combine (isAnd : Bool) : Term → Term → Term
  | .fixed a,.fixed b => .fixed (if isAnd then a && b else a || b)
  | .fixed a,.tree t | .tree t,.fixed a =>
    if isAnd then (if a then .tree t else .fixed false) else
      (if a then .fixed true else .tree t)
  | .tree a,.tree b => .tree (if isAnd then .conj a b else .disj a b)

theorem combine_val (x : X → Bool) (b : Bool) (a c : Term) :
    val x (combine b a c) = if b then val x a && val x c else val x a || val x c := by
  cases a with
  | fixed u =>
    cases c with
    | fixed v => cases b <;> rfl
    | tree v => cases u <;> cases b <;> simp [val,combine]
  | tree u =>
    cases c with
    | fixed v => cases v <;> cases b <;> simp [val,combine]
    | tree v => cases b <;> rfl

theorem leaves_pos (t : Expr X) : 0<t.leaves := by
  induction t <;> simp_all [Expr.leaves] <;> omega

theorem combine_cost (b : Bool) (a c : Term) :
    cost (combine b a c) ≤ 1+cost a+cost c := by
  cases a with
  | fixed u =>
    cases c with
    | fixed v => cases b <;> simp [cost,combine]
    | tree v => cases u <;> cases b <;> simp [cost,combine]
  | tree u =>
    cases c with
    | fixed v => cases v <;> cases b <;> simp [cost,combine]
    | tree v =>
      have a := leaves_pos u
      have c := leaves_pos v
      cases b <;> simp [cost,combine,Expr.leaves] <;> omega

def andFlag : GateOp → Bool
  | .and => true
  | _ => false

def build (w : List Term) (g : Gate) : Term :=
  match g.inputs with
  | [] => .fixed (andFlag g.op)
  | [i] => w.getD i (.fixed false)
  | i::j::_ => combine (andFlag g.op) (w.getD i (.fixed false)) (w.getD j (.fixed false))

def run (gs : List Gate) (w : List Term) :=
  gs.foldl (fun ws g => ws++[build ws g]) w

def evalRun (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun ws g => ws++[g.op.eval (g.inputs.map (fun i => ws.getD i false))]) w

def input (x : X → Bool) : List Bool :=
  (List.ofFn fun p : V => x (.inl p)) ++ List.ofFn (fun l : V => x (.inr l))

def initial : List Term :=
  (List.ofFn fun p : V => Term.tree (.atom (.inl p))) ++
  List.ofFn fun l : V => Term.tree (.atom (.inr l))

theorem map_get {A B : Type*} (f : A → B) (d : A) (w : List A) (i : ℕ) :
    (w.map f).getD i (f d) = f (w.getD i d) := by
  induction w generalizing i with
  | nil => rfl
  | cons a w ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem cost_get (w : List Term) (i : ℕ) :
    (w.map cost).getD i 0 = cost (w.getD i (.fixed false)) := map_get cost (Term.fixed false) w i

theorem value_get (x : X → Bool) (w : List Term) (i : ℕ) :
    (w.map (val x)).getD i false = val x (w.getD i (.fixed false)) := map_get (val x) (Term.fixed false) w i

theorem build_value (x : X → Bool) (w : List Term) (g : Gate)
    (h : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length≤2) :
    val x (build w g) = g.op.eval (g.inputs.map (fun i => (w.map (val x)).getD i false)) := by
  obtain ⟨op,is⟩ := g
  obtain ⟨ht,cap⟩ := h
  change op = .and ∨ op = .or at ht
  change is.length ≤ 2 at cap
  cases is with
  | nil => rcases ht with rfl | rfl <;> rfl
  | cons i is =>
    cases is with
    | nil =>
      rcases ht with rfl | rfl <;> simp only [build,List.map_cons,List.map_nil,value_get] <;>
        simp [GateOp.eval]
    | cons j is =>
      cases is with
      | nil =>
        rcases ht with rfl | rfl <;> simp only [build,List.map_cons,List.map_nil,value_get,combine_val] <;>
          simp [GateOp.eval,andFlag]
      | cons k is => simp at cap

theorem build_cost (w : List Term) (g : Gate) :
    cost (build w g) ≤ 1 + readCost (w.map cost) g.inputs := by
  obtain ⟨op,is⟩ := g
  cases is with
  | nil => simp [build,cost,readCost]
  | cons i is =>
    cases is with
    | nil =>
      change cost (w.getD i (.fixed false)) ≤ 1 + ((w.map cost).getD i 0 + 0)
      rw [cost_get]
      omega
    | cons j rest =>
      have q := combine_cost (andFlag op) (w.getD i (.fixed false)) (w.getD j (.fixed false))
      simp only [build,readCost,List.map_cons,List.sum_cons,cost_get]
      omega

theorem run_value (x : X → Bool) (gs : List Gate) (w : List Term)
    (good : ∀ g∈gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length≤2) :
    (run gs w).map (val x) = evalRun gs (w.map (val x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[build w g])).map (val x) = evalRun gs _
    rw [ih _ (fun k hk => good k (List.mem_cons_of_mem _ hk))]
    simp [build_value x w g (good g (by simp))]

theorem run_costs (gs : List Gate) :
    Trace 26 gs ((run gs initial).map cost) := by
  induction gs using List.reverseRecOn with
  | nil =>
    have h : initial.map cost = List.replicate 26 0 := by decide +kernel
    simpa only [run,List.foldl_nil,h] using (Trace.start (n:=26))
  | append_singleton gs g ih =>
    have h := Trace.step ih g (cost (build (run gs initial) g)) (build_cost _ _)
    simpa [run,List.foldl_append] using h

theorem initial_val (x : X → Bool) : initial.map (val x) = input x := by
  simp [initial,input,List.map_ofFn,Function.comp_def,val,Expr.eval]

theorem value_of_output (C : Circuit) (mono : Monotone2 C) (x : X → Bool) :
    val x ((run C.gates initial).getD C.output (.fixed false)) = C.eval (input x) := by
  rw [← value_get,run_value x C.gates initial (fun g hg => mono g hg),initial_val]
  rfl

/-- Any physically unshared, nonconstant Monotone2 circuit on these inputs
    has an equivalent formula on every input with at most C.size+1 leaves.
    No assumptions about projective-plane samples are made. -/
theorem exists_formula (C : Circuit) (mono : Monotone2 C) (single : noShare 26 C.gates)
    (u v : X → Bool) (hu : C.eval (input u) = true) (hv : C.eval (input v) = false) :
    ∃ t : Expr X, t.leaves ≤ C.size+1 ∧ ∀ x, t.eval x = C.eval (input x) := by
  let root := (run C.gates initial).getD C.output (.fixed false)
  have sem (x : X → Bool) : val x root = C.eval (input x) := value_of_output C mono x
  have cap : cost root ≤ C.size := by
    have c := any_wire (run_costs C.gates) single C.output
    simpa only [cost_get,Circuit.size,root] using c
  cases eq : root with
  | fixed b =>
    have yes := (sem u).trans hu
    have no := (sem v).trans hv
    simp only [eq,val] at yes no
    cases b <;> contradiction
  | tree t =>
    refine ⟨t,?_,?_⟩
    · rw [eq] at cap
      change t.leaves - 1 ≤ C.size at cap
      omega
    · intro x
      simpa only [eq,val] using sem x

#print axioms exists_formula
end CoFormula1963Circuit
