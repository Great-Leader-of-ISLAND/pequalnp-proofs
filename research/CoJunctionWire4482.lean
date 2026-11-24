import PEqualNP.CoRecipeOrbit4482

namespace CoJunctionWire4482
open CoPortRoots4482

/-- A wire formula can be recovered along the first-discovery pointer. Its
depth increases only when a new gate is introduced. -/
inductive Wire where
  | input (i : Fin 9)
  | gate (op : Bool) (a b : Wire)

def eval : Wire → CoRecipe4482.Entry
  | .input i => CoRecipe4482.input i
  | .gate op a b => CoRecipe4482.gate op (eval a) (eval b)

def rename (g : G) : Wire → Wire
  | .input i => .input (coordinate g i)
  | .gate op a b => .gate op (rename g a) (rename g b)

theorem full_rename (g : G) (w : Wire) :
    (eval (rename g w)).full=reorder (rowEquiv g) (eval w).full := by
  induction w with
  | input i => exact (raw_reordered g i).symm
  | gate op a b ha hb =>
    change join op (eval (rename g a)).full (eval (rename g b)).full =
      reorder (rowEquiv g) (join op (eval a).full (eval b).full)
    rw [ha,hb,reorder_join]

def code (w : Wire) : CoRecipeOrbit4482.Orbit :=
  ⟨eval w,fun g => (eval (rename g w)).full,fun g => full_rename g w⟩

/-- Sorted representative banks can use these syntax-only reconstruction
instructions. A malformed reference fails; proving a numerical routed edge
uses full truth values, so correctness does not rely on the syntax being
canonical. -/
def successor (xs : List Wire) (i j : Nat) (op da db : Bool) (g : G) : Option (List Wire) := do
  let a ← xs[i]?
  let b ← xs[j]?
  let held := (xs.zipIdx.filter (fun q =>
    !((q.2==i && da)||(q.2==j && db)))).map Prod.fst
  let updated := (.gate op a b :: held).map (rename g)
  pure (updated.mergeSort (fun x y => decide ((eval x).full.toNat ≤ (eval y).full.toNat)))

#print axioms full_rename
end CoJunctionWire4482
