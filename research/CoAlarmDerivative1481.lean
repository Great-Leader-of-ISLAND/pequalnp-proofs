import PEqualNP.CoFormula1963Protocol

namespace CoAlarmDerivative1481
open CoFormula1963Protocol

variable {ι : Type*} [DecidableEq ι]

def occ (v : ι) : Expr ι → Nat
  | .atom i => if i=v then 1 else 0
  | .conj a b | .disj a b => occ v a + occ v b

def bumped (row : ι → Bool) (v : ι) (i : ι) : Bool := row i || decide (i=v)

def alarm (row : ι → Bool) (v : ι) : Expr ι → Bool
  | .atom i => decide (i=v)
  | .conj a b => (a.eval row && alarm row v b) || (alarm row v a && b.eval row)
  | .disj a b => alarm row v a || alarm row v b

theorem absent (t : Expr ι) (row : ι → Bool) (v : ι) (h : occ v t=0) :
    alarm row v t=false := by
  induction t with
  | atom i => by_cases eq : i=v <;> simp_all [occ,alarm]
  | conj a b ha hb =>
    simp only [occ,Nat.add_eq_zero] at h
    simp [alarm,ha h.1,hb h.2]
  | disj a b ha hb =>
    simp only [occ,Nat.add_eq_zero] at h
    simp [alarm,ha h.1,hb h.2]

private theorem product : ∀ a b c d : Bool, (c=false ∨ d=false) →
    ((a || c) && (b || d)) = ((a && b) || ((a && d) || (c && b))) := by decide

theorem one_formula (t : Expr ι) (row : ι → Bool) (v : ι) (bound : occ v t ≤ 1) :
    t.eval (bumped row v) = (t.eval row || alarm row v t) := by
  induction t with
  | atom i => rfl
  | conj a b ha hb =>
    change occ v a + occ v b ≤ 1 at bound
    have side : occ v a=0 ∨ occ v b=0 := by omega
    have zero : alarm row v a=false ∨ alarm row v b=false :=
      side.imp (absent a row v) (absent b row v)
    simp only [Expr.eval,alarm,ha (by omega),hb (by omega)]
    exact product _ _ _ _ zero
  | disj a b ha hb =>
    change occ v a + occ v b ≤ 1 at bound
    simp only [Expr.eval,alarm,ha (by omega),hb (by omega)]
    ac_rfl

theorem two_reads (t : Expr ι) (row : ι → Bool) (v : ι)
    (base : t.eval row=false) (both : t.eval (bumped row v)=true)
    (off : alarm row v t=false) : 2 ≤ occ v t := by
  by_contra h
  have eq := one_formula t row v (by omega)
  simp [base,both,off] at eq

#print axioms two_reads
end CoAlarmDerivative1481
