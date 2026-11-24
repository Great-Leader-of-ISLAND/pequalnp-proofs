import PEqualNP.CoJunctionCost4482
import PEqualNP.CoPortCheckMove4482

namespace CoJunctionImages4482
open CoPortRoots4482 CoPortFrontier4482

/-- The transporter only acts on the existing signal dictionary. Compute
the new signal under that transporter by its two already-mapped parents. -/
def cachedStep (f : W → W) (xs : List W) (op : Bool) (a b : W) (da db : Bool) :=
  join op (f a) (f b) :: (eraseIf (eraseIf xs a da) b db).map f

private theorem erase_subset {xs : List W} {w z : W} {d : Bool}
    (h : z ∈ eraseIf xs w d) : z ∈ xs := by
  cases d with
  | false => exact h
  | true => exact (List.mem_filter.mp h).1

private theorem agreeMap {α β : Type} {f g : α → β} (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : xs.map f = xs.map g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons]
    rw [h a List.mem_cons_self,ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem cached_map {f : W → W} {xs : List W} {g : G}
    (cache : ∀ x∈xs, f x = reorder (rowEquiv g) x)
    {a b : W} (ha : a∈xs) (hb : b∈xs) (op da db : Bool) :
    cachedStep f xs op a b da db =
      (successor xs op a b da db).map (reorder (rowEquiv g)) := by
  change join op (f a) (f b) :: _ =
    (reorder (rowEquiv g) (join op a b)) :: _
  rw [cache a ha,cache b hb,reorder_join]
  have tail := agreeMap (f:=f) (g:=reorder (rowEquiv g)) (eraseIf (eraseIf xs a da) b db)
    (fun x hx => cache x (erase_subset (erase_subset hx)))
  exact congrArg (List.cons (join op (reorder (rowEquiv g) a) (reorder (rowEquiv g) b))) tail

theorem equalSet {xs ys : List W} (h : CoJunctionCost4482.sameSet xs ys = true) :
    xs.toFinset = ys.toFinset := by
  obtain ⟨hxy,hyx⟩ := Bool.and_eq_true_iff.mp h
  ext w
  simp only [List.mem_toFinset]
  constructor
  · intro m
    simpa using List.all_eq_true.mp hxy w m
  · intro m
    simpa using List.all_eq_true.mp hyx w m

theorem cached_route {f : W → W} {xs tgt : List W} {g : G}
    (cache : ∀ x∈xs, f x = reorder (rowEquiv g) x)
    {a b : W} (ha : a∈xs) (hb : b∈xs) {op da db : Bool}
    (matchTarget : CoJunctionCost4482.sameSet (cachedStep f xs op a b da db) tgt = true) :
    (successor xs op a b da db).toFinset.image (reorder (rowEquiv g))=tgt.toFinset := by
  rw [cached_map cache ha hb op da db] at matchTarget
  have eq := equalSet matchTarget
  rw [←eq]
  ext y
  simp

#print axioms cached_route
end CoJunctionImages4482
