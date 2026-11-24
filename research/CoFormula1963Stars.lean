import PEqualNP.CoFormula1963Link

namespace CoFormula1963Stars
open CoFormula1963Geometry CoFormula1963Protocol CoFormula1963Link

def star (p : V) : Expr X :=
  .conj (.atom (.inl p))
    (.disj (.disj (.atom (.inr p)) (.atom (.inr (p-1))))
      (.disj (.atom (.inr (p-3))) (.atom (.inr (p-9)))))

def optimal : Expr X := ((List.range 12).map (fun i => star ⟨(i+1)%13,Nat.mod_lt _ (by decide)⟩)).foldl Expr.disj (star 0)

theorem exact_size : optimal.leaves = 65 := by decide +kernel

theorem accepts : ∀ e : E, optimal.eval (pos e) = true := by decide +kernel

private theorem neighborhood : ∀ p : V,
    inc p p ∧ inc p (p-1) ∧ inc p (p-3) ∧ inc p (p-9) := by decide +kernel

private theorem star_false (p : V) (y : Y) : (star p).eval (neg y) = false := by
  by_cases hp : p ∈ quad y.1 y.2
  · have off (l : V) (hl : inc p l) : neg y (.inr l) = false := by
      unfold neg
      exact decide_eq_false (fun h => h p hp hl)
    obtain ⟨a,b,c,d⟩ := neighborhood p
    simp [star,Expr.eval,off p a,off (p-1) b,off (p-3) c,off (p-9) d]
  · have z : neg y (.inl p) = false := by unfold neg; exact decide_eq_false hp
    simp [star,Expr.eval,z]

private theorem fold_false (y : Y) (xs : List (Expr X)) (t : Expr X)
    (ht : t.eval (neg y) = false) (hs : ∀ w∈xs,w.eval (neg y) = false) :
    (xs.foldl Expr.disj t).eval (neg y) = false := by
  induction xs generalizing t with
  | nil => exact ht
  | cons w ws ih =>
    exact ih _ (by simp [Expr.eval,ht,hs w (by simp)]) (fun z hz => hs z (List.mem_cons_of_mem _ hz))

theorem rejects (r : Fin 18) (s : V) : optimal.eval (neg (r,s)) = false := by
  apply fold_false (r,s) _ _ (star_false _ _)
  intro w hw
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
  exact star_false _ _

#print axioms exact_size
#print axioms rejects
end CoFormula1963Stars
