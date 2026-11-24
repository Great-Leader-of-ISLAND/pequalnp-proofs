import PEqualNP.CoMinorLimit4938

namespace CoFormulaMinor4938

inductive Expr where
  | leaf (v : Fin 10) (neg : Bool)
  | fork (op : Bool) (l r : Expr)

def Expr.eval (x : Fin 10 → Word) : Expr → Word
  | .leaf v false => x v
  | .leaf v true => ~~~(x v)
  | .fork op l r => gate op (l.eval x) (r.eval x)

def glue (op : Bool) : Option Shape → Option Shape → Option Shape
  | none,y => y
  | x,none => x
  | some l,some r => some (.fork op l r)

def Expr.keep (port : Fin 10 → Option (Fin 3)) : Expr → Option Shape
  | .leaf v _ => (port v).map Shape.atom
  | .fork op l r => glue op (l.keep port) (r.keep port)

def permits : Option Shape → Word → Prop
  | none,w => w=0 ∨ w=255
  | some s,w => w∈s.value

theorem const_allowed (s : Shape) : (0 : Word)∈s.value ∧ (255 : Word)∈s.value := by
  induction s with
  | atom i => simp [Shape.value]
  | fork op l r ih _ =>
    simp only [Shape.value,List.mem_eraseDups,List.mem_append]
    exact ⟨Or.inl (Or.inl ih.1),Or.inl (Or.inl ih.2)⟩

private theorem small (s : Option Shape) {v : Word} (h : v=0 ∨ v=255) : permits s v := by
  cases s with
  | none => exact h
  | some s => rcases h with rfl|rfl; exact (const_allowed s).1; exact (const_allowed s).2

private theorem const_gate : ∀ (x : Word) (op : Bool) (y : Word), y=0 ∨ y=255 →
    (gate op x y=x ∨ gate op x y=0 ∨ gate op x y=255) ∧
    (gate op y x=x ∨ gate op y x=0 ∨ gate op y x=255) := by
  intro x op y h
  rcases h with rfl|rfl <;> cases op <;> revert x <;> decide +kernel

private theorem pass {s : Option Shape} {x z : Word} (h : permits s x)
    (hz : z=x ∨ z=0 ∨ z=255) : permits s z := by
  rcases hz with rfl|h'
  · exact h
  · exact small s h'

theorem fork_allowed (op : Bool) {l r : Option Shape} {x y : Word}
    (a : permits l x) (b : permits r y) : permits (glue op l r) (gate op x y) := by
  cases l with
  | none => exact pass b (const_gate y op x a).2
  | some l =>
    cases r with
    | none => exact pass a (const_gate x op y b).1
    | some r =>
      simp only [glue,permits,Shape.value,List.mem_eraseDups,List.mem_append,List.mem_flatMap,List.mem_map]
      exact Or.inr ⟨x,a,y,b,rfl⟩

theorem restriction (s : Expr) (x : Fin 10 → Word) (p : Fin 10 → Option (Fin 3))
    (ok : ∀ v, match p v with | some i => x v=lit i | none => x v=0 ∨ x v=255) :
    permits (s.keep p) (s.eval x) := by
  induction s with
  | leaf v d =>
    have fact := ok v
    cases hp : p v with
    | none =>
      rw [hp] at fact
      rcases fact with h|h <;> cases d <;> simp [Expr.keep,Expr.eval,hp,permits,h]
    | some i =>
      rw [hp] at fact
      cases d <;> simp [Expr.keep,Expr.eval,hp,permits,Shape.value,fact]
  | fork op l r a b => exact fork_allowed op a b

end CoFormulaMinor4938
