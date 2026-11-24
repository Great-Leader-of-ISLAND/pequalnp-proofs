import PEqualNP.CoPetersenWedges4938

namespace CoFormulaMinor4938

def Expr.scalar (x : Fin 10 → Bool) : Expr → Bool
  | .leaf v neg => if neg then !(x v) else x v
  | .fork op l r => if op then l.scalar x || r.scalar x else l.scalar x && r.scalar x

def scalarGraph (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 6 && x 8) || (x 7 && x 9) ||
  (x 8 && x 5) || (x 9 && x 6)

theorem bit_eval (t : Expr) (x : GInput) (k : Nat) (hk : k < 8) :
    (t.eval x).getLsbD k=t.scalar (fun v => (x v).getLsbD k) := by
  induction t with
  | leaf v n => cases n <;> simp [Expr.eval,Expr.scalar,BitVec.getLsbD_not,hk]
  | fork op a b ha hb =>
    cases op <;> simp [Expr.eval,Expr.scalar,gate,BitVec.getLsbD_or,BitVec.getLsbD_and,ha,hb]

theorem correct_words (t : Expr) (h : ∀ x,t.scalar x=scalarGraph x) : ∀ x : GInput,t.eval x=graph x := by
  intro x
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bit_eval _ _ _ hi,h]
  simp only [graph,scalarGraph,BitVec.getLsbD_or,BitVec.getLsbD_and]

def localCount (p : Fin 10 → Option (Fin 3)) : Expr → Nat
  | .leaf v _ => if (p v).isSome then 1 else 0
  | .fork _ l r => localCount p l + localCount p r

def weight : Option Shape → Nat | none => 0 | some t => t.leaves

theorem glue_weight (op : Bool) (x y : Option Shape) :
    weight (glue op x y)=weight x+weight y := by
  cases x <;> cases y <;> simp [glue,weight,Shape.leaves]

theorem keep_weight (t : Expr) (p : Fin 10 → Option (Fin 3)) : weight (t.keep p)=localCount p t := by
  induction t with
  | leaf v n => cases h : p v <;> simp [Expr.keep,localCount,h,weight,Shape.leaves]
  | fork op a b ha hb => simp only [Expr.keep,localCount,glue_weight,ha,hb]

theorem real_wedge (t : Expr) (h : ∀ x, t.scalar x=scalarGraph x) (i : I) : 5 ≤ localCount (port i) t := by
  have all := all_required t (correct_words t h) i
  rw [←keep_weight]
  cases hs : t.keep (port i) with
  | none =>
    have a := all 168 (by decide +kernel)
    rw [hs] at a
    exact False.elim ((by decide : ¬ permits none 168) a)
  | some s =>
    exact wedge_five s (fun x hx => by simpa [hs,permits] using all x hx)

#print axioms real_wedge
end CoFormulaMinor4938
