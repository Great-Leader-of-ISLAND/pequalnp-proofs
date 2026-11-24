import Mathlib.Data.List.Defs
import Mathlib.Tactic

namespace CoFormulaMinor4938

abbrev Word := BitVec 8
abbrev Fam := List Word
inductive Shape where
  | atom (i : Fin 3)
  | fork (op : Bool) (l r : Shape)

def lit (i : Fin 3) : Word := ![170,204,240] i

def gate (op : Bool) (x y : Word) := if op then x ||| y else x &&& y

def Shape.value : Shape → Fam
  | .atom i => [0,255,lit i,~~~(lit i)]
  | .fork op l r =>
    let A := l.value
    let B := r.value
    (A ++ B ++ A.flatMap (fun a => B.map (gate op a))).eraseDups

def Shape.leaves : Shape → Nat
  | .atom _ => 1
  | .fork _ l r => l.leaves + r.leaves

theorem nonempty (s : Shape) : 1≤s.leaves := by
  induction s with
  | atom i => decide
  | fork g l r hl hr => simp only [Shape.leaves]; omega

end CoFormulaMinor4938
