import PEqualNP.CoAlarmDerivative1481

namespace CoAlarmMonomial1481
open CoFormula1963Protocol CoAlarmDerivative1481

-- A monomial chooses one child of each OR and both children of each AND.
inductive Parse {ι : Type*} : Expr ι → List ι → Prop where
  | atom (i : ι) : Parse (.atom i) [i]
  | left {a b : Expr ι} {xs} : Parse a xs → Parse (.disj a b) xs
  | right {a b : Expr ι} {xs} : Parse b xs → Parse (.disj a b) xs
  | both {a b : Expr ι} {xs ys} : Parse a xs → Parse b ys → Parse (.conj a b) (xs++ys)

variable {ι : Type*} [DecidableEq ι]

theorem extract (t : Expr ι) (row : ι → Bool) (hit : t.eval row=true) :
    ∃ xs, Parse t xs ∧ ∀ i∈xs,row i=true := by
  induction t with
  | atom i => exact ⟨[i],.atom i,by simpa using hit⟩
  | disj a b ha hb =>
    rcases Bool.or_eq_true_iff.mp hit with h|h
    · obtain ⟨xs,p,ok⟩ := ha h
      exact ⟨xs,.left p,ok⟩
    · obtain ⟨xs,p,ok⟩ := hb h
      exact ⟨xs,.right p,ok⟩
  | conj a b ha hb =>
    obtain ⟨h,k⟩ := Bool.and_eq_true.mp hit
    obtain ⟨xs,p,px⟩ := ha h
    obtain ⟨ys,q,py⟩ := hb k
    exact ⟨xs++ys,.both p q,fun i hi => (List.mem_append.mp hi).elim (px i) (py i)⟩

theorem histories {t : Expr ι} {xs : List ι} (p : Parse t xs) (row : ι → Bool) (v : ι)
    (ok : ∀ i∈xs,bumped row v i=true) :
    (xs.count v=0 → t.eval row=true) ∧ (xs.count v=1 → alarm row v t=true) := by
  induction p with
  | atom i =>
    have accepted := ok i (by simp)
    by_cases eq : i=v
    · subst i
      simp [alarm]
    · have real : row i=true := by simpa [bumped,eq] using accepted
      simp [Expr.eval,alarm,eq,Ne.symm eq,real]
  | left _ ih =>
    obtain ⟨norm,one⟩ := ih ok
    exact ⟨fun h => by simp [Expr.eval,norm h],fun h => by simp [alarm,one h]⟩
  | right _ ih =>
    obtain ⟨norm,one⟩ := ih ok
    exact ⟨fun h => by simp [Expr.eval,norm h],fun h => by simp [alarm,one h]⟩
  | @both a b xs ys _ _ ha hb =>
    obtain ⟨az,ao⟩ := ha (fun i hi => ok i (List.mem_append_left _ hi))
    obtain ⟨bz,bo⟩ := hb (fun i hi => ok i (List.mem_append_right _ hi))
    rw [List.count_append]
    constructor
    · intro eq
      simp [Expr.eval,az (by omega),bz (by omega)]
    · intro eq
      by_cases z : xs.count v=0
      · simp [alarm,az z,bo (by omega)]
      · simp [alarm,bz (by omega),ao (by omega)]

theorem repeated_in_every_parse {t : Expr ι} {xs : List ι} (p : Parse t xs)
    (row : ι → Bool) (v : ι) (ok : ∀ i∈xs,bumped row v i=true)
    (off : t.eval row=false) (silent : alarm row v t=false) : 2≤xs.count v := by
  obtain ⟨z,o⟩ := histories p row v ok
  by_contra! small
  rcases (show xs.count v=0 ∨ xs.count v=1 by omega) with h|h
  · simp [off] at z
    exact z h
  · simp [silent] at o
    exact o h

#print axioms repeated_in_every_parse
end CoAlarmMonomial1481
