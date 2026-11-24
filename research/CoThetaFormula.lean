import Init

namespace CoThetaFormula

def unary (z o x : Bool) : Bool := if x then o else z

def combine (join x y : Bool) : Bool := if join then x || y else x && y

def ordered (x y : Bool) : Bool := !x || y

theorem mixed_leaf_elimination :
    ∀ (p0 p1 n0 n1 c0 c1 join : Bool),
    ordered p0 p1 = true → ordered n0 n1 = true → ordered c0 c1 = true →
    let before0 := unary c0 c1 (combine join p0 n1)
    let before1 := unary c0 c1 (combine join p1 n0)
    ordered before0 before1 = true →
      before0 = unary c0 c1 (combine join p0 (unary n0 n1 join)) ∧
      before1 = unary c0 c1 (combine join p1 (unary n0 n1 join)) := by
  decide

def signature (a b c d : Bool) : List Bool := [a, b, c, d]

def phase (neg val : Bool) : Bool := if neg then !val else val

def outcome (join sx sy flip : Bool) : List Bool :=
  let f := fun a b => phase flip (combine join (phase sx a) (phase sy b))
  signature (f false false) (f false true) (f true false) (f true true)

theorem mixed_edge_excludes_fixed_merge :
    ∀ (join sx sy flip0 flip1 : Bool),
    outcome join sx sy flip0 = signature false false false true →
    outcome join sx sy flip1 ≠ signature false true true true := by
  decide

end CoThetaFormula
