import PEqualNP.CoNine3024CanonTable

namespace CoFused3174
open CoNine3024 CoNine3024.Canon

def weight : List Atom → Nat
  | [] => 0
  | a::xs => a.fixed+weight xs

def union : List Atom → Cells
  | [] => 0
  | a::xs => separator a ||| union xs

private theorem weight_from (xs : List Atom) (n : Nat) :
    xs.foldl (fun z a => z+a.fixed) n=n+weight xs := by
  induction xs generalizing n with
  | nil => simp [weight]
  | cons a xs ih => simp [weight,List.foldl_cons,ih,Nat.add_assoc]

private theorem union_from (xs : List Atom) (x : Cells) :
    xs.foldl (fun z a => z ||| separator a) x=x ||| union xs := by
  induction xs generalizing x with
  | nil => simp [union]
  | cons a xs ih => simp [union,List.foldl_cons,ih,BitVec.or_assoc]

private theorem weight_append (xs ys : List Atom) : weight (xs++ys)=weight xs+weight ys := by
  induction xs with
  | nil => simp [weight]
  | cons a xs ih => simp [weight,ih,Nat.add_assoc]

private theorem union_append (xs ys : List Atom) : union (xs++ys)=union xs ||| union ys := by
  induction xs with
  | nil => simp [union]
  | cons a xs ih => simp [union,ih,BitVec.or_assoc]

private theorem zero_bits (a : Cells) : (0:Cells) ||| a=a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_or]

private theorem money (s : State) (a b z : Atom) (m : Nat) (r : List Atom) :
    safe (child s a b z r m)=
    ((s.spent+(a.fixed ||| b.fixed)+z.fixed+weight r+weight (maskKeep a b m)) &&& forbidden==0) := by
  unfold safe child
  simp only [weight_from,weight,weight_append]
  apply congrArg (fun n : Nat => (n &&& forbidden)==0)
  omega

private theorem cover (g : Geometry) (a b z : Atom) (r : List Atom) (m : Nat) :
    covered g (z::(maskKeep a b m++r))=
    (((separator z ||| union r ||| union (maskKeep a b m)) &&& g.need)==g.need) := by
  unfold covered
  rw [union_from,zero_bits]
  simp only [union,union_append]
  exact congrArg (fun x : Cells => (x &&& g.need)==g.need) (by ac_rfl)

private theorem width (s : State) (a b z : Atom) (r : List Atom) (m : Nat) :
    (child s a b z r m).wires.length = (r.length+(maskKeep a b m).length+1) := by
  simp only [child,List.length_cons,List.length_append]
  omega

def oneOp (g : Geometry) (k : Nat) (s : State) (a b : Atom) (d : Bool) (r : List Atom)
    (price : Nat) (coveredElse : Cells) (next : State → Bool) : Bool :=
  let z := operation g d a b
  let resultCover := separator z ||| coveredElse
  let fee := s.spent+(a.fixed ||| b.fixed)+z.fixed+price
  ([0,1,2,3] : List Nat).all fun m =>
    let kept := maskKeep a b m
    if r.length+kept.length+1≤k+1 then
      if ((resultCover ||| union kept) &&& g.need)==g.need then
        if ((fee+weight kept) &&& forbidden)==0 then
          if z.full==0 || z.full==BitVec.allOnes 512 || s.wires.any (fun w => w.full==z.full) then true
          else next (child s a b z r m)
        else true
      else true
    else true

private theorem oneOp_sound {g k s a b d next} (seen : oneOp g k s a b d (rest s a b)
    (weight (rest s a b)) (union (rest s a b)) next=true) {t : State}
    (allowed : t∈choices g k s a b d) : next t=true := by
  unfold choices at allowed
  dsimp only at allowed
  split at allowed
  · simp at allowed
  · rename_i notBad
    obtain ⟨m,hm,eq⟩ := List.mem_filterMap.mp allowed
    split at eq
    · rename_i ok
      cases eq
      obtain ⟨small,pay,cov⟩ := ok
      rw [width] at small
      rw [money] at pay
      change covered g (_::(maskKeep a b m++rest s a b))=true at cov
      rw [cover] at cov
      exact by
        have got := List.all_eq_true.mp seen m hm
        simpa only [small,if_true,cov,pay,notBad,if_false] using got
    · contradiction

def check (g : Geometry) (k : Nat) (s : State) (next : State → Bool) : Bool :=
  (pairs s.wires).all fun (a,b) =>
    let r := rest s a b
    let p := weight r
    let c := union r
    oneOp g k s a b false r p c next && oneOp g k s a b true r p c next

theorem check_sound {g k s next} (h : check g k s next=true) {t : State}
    (edge : t∈children g k s) : next t=true := by
  obtain ⟨⟨a,b⟩,pair,which⟩ := List.mem_flatMap.mp edge
  have checked := List.all_eq_true.mp h (a,b) pair
  simp only [Bool.and_eq_true] at checked
  rcases List.mem_append.mp which with first|second
  · exact oneOp_sound checked.1 first
  · exact oneOp_sound checked.2 second

def localNode (guard : Nat → State → Bool) (g : Geometry) (k : Nat) (t : Table) (s : State) : Bool :=
  !(live g s) && check g k s (fun v =>
    let q := order v
    hit t q || closed guard g k q)

theorem local_sound {guard g k t s} (proved : valid guard g k t) (h : localNode guard g k t s=true) :
    run guard g (k+1) s=false := by
  simp only [localNode,Bool.and_eq_true,Bool.not_eq_true'] at h
  apply node_false proved
  simp only [node,Bool.and_eq_true,Bool.not_eq_true',Bool.or_eq_true]
  exact ⟨h.1,Or.inr (List.all_eq_true.mpr fun _ edge => check_sound h.2 edge)⟩

theorem grouped {guard g k next curr} {groups block : Nat} (old : valid guard g k next)
    (positive : 0<block) (enough : curr.size≤groups*block)
    (checked : ∀ b : Fin groups, batch (fun i => localNode guard g k next (curr.state i))
      (b.val*block) block=true) : valid guard g (k+1) curr := by
  intro i hi
  let b : Fin groups := ⟨i/block,(Nat.div_lt_iff_lt_mul positive).mpr (lt_of_lt_of_le hi enough)⟩
  apply local_sound old
  apply batch_mem (checked b)
  · exact Nat.div_mul_le_self i block
  · change i<(i/block)*block+block
    have h := Nat.mod_add_div i block
    rw [Nat.mul_comm block (i/block)] at h
    have bound := Nat.mod_lt i positive
    omega

end CoFused3174
