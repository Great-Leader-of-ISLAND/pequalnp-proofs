import PEqualNP.CoFormula1963Complete

namespace CoAlarmFactor1481
open CoFormula1963Protocol CoFormula1963Geometry CoFormula1963Private CoFormula1963Link

inductive Arms where
  | arm (t : Expr X)
  | meet (a b : Arms)

def Arms.expr : Arms → Expr X
  | .arm t => t
  | .meet a b => .conj a.expr b.expr

def Arms.size : Arms → Nat
  | .arm _ => 1
  | .meet a b => a.size+b.size

def Arms.gates : Arms → Nat
  | .arm t => t.leaves
  | .meet a b => a.gates+b.gates+1

def Arms.output (raw : X → Bool) (shared : Bool) : Arms → Bool
  | .arm t => shared || t.eval raw
  | .meet a b => a.output raw shared && b.output raw shared

theorem factor (arms : Arms) (row : X → Bool) (s : Bool) :
    arms.output row s=(s || arms.expr.eval row) := by
  induction arms with
  | arm t => rfl
  | meet a b hl hr => simp only [Arms.output,Arms.expr,Expr.eval,hl,hr]; cases s <;> simp

theorem gate_count (arms : Arms) : arms.gates+1=arms.expr.leaves+arms.size := by
  induction arms with
  | arm t => rfl
  | meet a b ha hb => simp only [Arms.gates,Arms.expr,Expr.leaves,Arms.size]; omega

theorem positive (t : Expr X) : 1 ≤ t.leaves := by
  induction t with
  | atom i => exact Nat.le_refl 1
  | conj a b ha hb => simp only [Expr.leaves]; omega
  | disj a b ha hb => simp only [Expr.leaves]; omega

theorem price (shared : Expr X) (arms : Arms)
    (yes : ∀ e : E, arms.output (pos e) (shared.eval (pos e))=true)
    (no : ∀ y : CoFormula1963Link.Y, arms.output (neg y) (shared.eval (neg y))=false) :
    63+arms.size ≤ shared.leaves-1+arms.gates := by
  let flat := Expr.disj shared arms.expr
  have high : ∀ e : E,flat.eval (pos e)=true := by
    intro e; exact (factor arms _ _).symm.trans (yes e)
  have low : ∀ y : CoFormula1963Link.Y,flat.eval (neg y)=false := by
    intro y; exact (factor arms _ _).symm.trans (no y)
  have rank := CoFormula1963Complete.leaves65 flat high low
  change 65 ≤ shared.leaves+arms.expr.leaves at rank
  have count := gate_count arms
  have big := positive shared
  omega

#print axioms price
end CoAlarmFactor1481
