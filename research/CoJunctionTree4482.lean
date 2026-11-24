import PEqualNP.CoJunctionWire4482
namespace CoJunctionTree4482
open CoPortRoots4482 CoPortFrontier4482 CoJunctionWire4482

def value (w : Wire) := (eval w).full
def values (xs : List Wire) := xs.map value

private def insertWire (w : Wire) : List Wire → List Wire
  | [] => [w]
  | x::xs =>
    if (value w).toNat ≤ (value x).toNat then w::x::xs else x::insertWire w xs

private theorem inInsert (w a : Wire) (xs : List Wire) :
    a∈insertWire w xs ↔ a=w ∨ a∈xs := by
  induction xs with
  | nil => simp [insertWire]
  | cons x xs ih =>
    by_cases le : (value w).toNat≤(value x).toNat
    · simp [insertWire,le]
    · simp only [insertWire,if_neg le,List.mem_cons,ih]
      tauto

private def ordered : List Wire → List Wire
  | [] => []
  | x::xs => insertWire x (ordered xs)

private theorem inOrdered (xs : List Wire) (a : Wire) : a∈ordered xs ↔ a∈xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [ordered,inInsert,ih,List.mem_cons]

def imageBank (g : G) (xs : List Wire) := ordered (xs.map (rename g))

theorem set_image (g : G) (xs : List Wire) :
    (values (imageBank g xs)).toFinset = (values xs).toFinset.image (reorder (rowEquiv g)) := by
  ext w
  constructor
  · intro m
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp m)
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ((inOrdered _ y).mp hy)
    exact Finset.mem_image.mpr ⟨value x,List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hx,rfl⟩),
      (full_rename g x).symm⟩
  · intro m
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp m
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨rename g x,(inOrdered _ _).mpr (List.mem_map.mpr ⟨x,hx,rfl⟩),full_rename g x⟩

def forget (xs : List Wire) (w : W) (d : Bool) :=
  if d then xs.filter fun x => value x != w else xs

private theorem forget_values (xs : List Wire) (w : W) (d : Bool) :
    values (forget xs w d) = eraseIf (values xs) w d := by
  cases d with
  | false => rfl
  | true =>
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      cases h : value x != w <;> simp_all [values,forget,eraseIf,List.filter_cons]

/-- First discovery carries its actual parent rule and graph symmetry. Under
this reconstruction every fresh target automatically matches the real image.
Only edges referring back to an already recorded state need a numeric match. -/
def discover (g : G) (xs : List Wire) (op : Bool) (a b : Wire) (da db : Bool) :=
  imageBank g (.gate op a b :: forget (forget xs (value a) da) (value b) db)

theorem discovery_route (g : G) (xs : List Wire) (op : Bool) (a b : Wire) (da db : Bool) :
    (CoPortFrontier4482.successor (values xs) op (value a) (value b) da db).toFinset.image
       (reorder (rowEquiv g)) = (values (discover g xs op a b da db)).toFinset := by
  unfold discover
  rw [set_image]
  have eq : values (.gate op a b :: forget (forget xs (value a) da) (value b) db) =
      CoPortFrontier4482.successor (values xs) op (value a) (value b) da db := by
    change join op (value a) (value b) :: values (forget (forget xs (value a) da) (value b) db) = _
    rw [forget_values,forget_values]
    rfl
  rw [eq]

#print axioms discovery_route
end CoJunctionTree4482
