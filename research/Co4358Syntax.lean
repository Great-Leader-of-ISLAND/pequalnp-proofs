import PEqualNP.Defs

namespace CoNum4358

structure Gate where
  isOr : Bool
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

def Gate.phys (g : Gate) : PEqualNP.CircuitLowerBounds.Gate :=
  ⟨if g.isOr then .or else .and, [g.a,g.b]⟩

def Gate.lifted (g : Gate) (marks : Bool × Bool) : PEqualNP.CircuitLowerBounds.Gate :=
  ⟨if g.isOr then .or else .and,
    [if marks.1 then 0 else g.a+1, if marks.2 then 0 else g.b+1]⟩

def Gate.sane (g : Gate) (width : Nat) : Prop :=
  g.a < width ∧ g.b < width ∧ g.a ≠ g.b

def Gate.reads2 (g : Gate) : Bool := g.isOr && [g.a,g.b].contains 2

abbrev Marked := Gate × (Bool × Bool)

def Allowed (s t : Nat) (r : Marked) : Prop :=
  (r.2.1 = true → r.1.a = s ∨ r.1.a = t) ∧
  (r.2.2 = true → r.1.b = s ∨ r.1.b = t)

def op (k x y : Bool) : Bool := if k then x || y else x && y

def Gate.val (g : Gate) (w : List Bool) : Bool :=
  op g.isOr (w.getD g.a false) (w.getD g.b false)

def Marked.val (r : Marked) (w : List Bool) : Bool :=
  op r.1.isOr (r.2.1 || w.getD r.1.a false) (r.2.2 || w.getD r.1.b false)

def ordinary (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.val ws]) w

def raised (ds : List Marked) (w : List Bool) : List Bool :=
  ds.foldl (fun ws d => ws ++ [Marked.val d ws]) w

end CoNum4358
