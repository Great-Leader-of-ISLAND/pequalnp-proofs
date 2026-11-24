import PEqualNP.CoAO3143Cotree

namespace CoAO3143.OneShare
open Cotree
set_option maxRecDepth 16384

/-- Input coordinates and the shared signal are kept syntactically distinct,
even if an intermediate truth column happens to equal an old coordinate. -/
inductive F where
  | atom : Sig → F
  | port : F
  | fork : Bool → F → F → F

def F.val (z : Sig) : F → Sig
  | .atom a => a
  | .port => z
  | .fork d l r => bin d (l.val z) (r.val z)

def F.vars : F → List Sig
  | .atom a => [a]
  | .port => []
  | .fork _ l r => l.vars ++ r.vars

def F.ports : F → Nat
  | .atom _ => 0
  | .port => 1
  | .fork _ l r => l.ports+r.ports

def F.bind (f : Sig → F) : F → F
  | .atom a => f a
  | .port => .port
  | .fork d l r => .fork d (l.bind f) (r.bind f)

theorem bind_val (e : F) (f : Sig→F) (s : Sig) (ok : ∀a,(f a).val s=a) :
    (e.bind f).val s=e.val s := by
  induction e with
  | atom a => exact ok a
  | port => rfl
  | fork d l r ih jh => simp only [F.bind,F.val,ih,jh]

theorem bind_ports (e : F) (f : Sig→F) (closed : ∀x,(f x).ports=0) :
    (e.bind f).ports=e.ports := by
  induction e with
  | atom a => exact closed a
  | port => rfl
  | fork d l r ih jh => simp only [F.bind,F.ports,ih,jh]

theorem bind_vars (e : F) (f : Sig→F) : (e.bind f).vars=e.vars.flatMap (fun a => (f a).vars) := by
  induction e with
  | atom a => simp [F.bind,F.vars]
  | port => rfl
  | fork d l r ih jh => simp only [F.bind,F.vars,ih,jh,List.flatMap_append]

def weight (f : Sig→F) : List Sig → Nat
  | [] => 0
  | x::xs => (f x).ports + weight f xs

private theorem weight_append (f : Sig→F) (xs ys : List Sig) :
    weight f (xs++ys)=weight f xs+weight f ys := by
  induction xs with
  | nil => simp [weight]
  | cons a xs ih => simp [weight,ih,Nat.add_assoc]

theorem bind_weight (e : F) (f : Sig→F) : (e.bind f).ports=e.ports+weight f e.vars := by
  induction e with
  | atom a => simp [F.bind,F.ports,F.vars,weight]
  | port => rfl
  | fork d l r ih jh =>
    simp only [F.bind,F.ports,F.vars,ih,jh,weight_append]
    omega

private def tally (a : Sig) : List Sig → Nat
  | [] => 0
  | x::xs => (if x=a then 1 else 0)+tally a xs

private theorem tally_once (a : Sig) (xs : List Sig) (nd : xs.Nodup) :
    tally a xs=if a∈xs then 1 else 0 := by
  induction xs with
  | nil => simp [tally]
  | cons x xs ih =>
    obtain ⟨fresh,n⟩ := List.nodup_cons.mp nd
    by_cases eq : x=a
    · subst x; simp [tally,ih n,fresh]
    · simp [tally,ih n,eq,Ne.symm eq]

private theorem weight_pair (f : Sig→F) (a z : Sig)
    (od : ∀x,(f x).ports=(if x=a then 1 else 0)+(if x=z then 1 else 0)) (xs : List Sig) :
    weight f xs=tally a xs+tally z xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [weight,tally,od,ih]
    omega

def embed : ReadTree → F
  | .atom a => .atom a
  | .fork d l r => .fork d (embed l) (embed r)

theorem embed_ports (e : ReadTree) : (embed e).ports=0 := by
  induction e with
  | atom => rfl
  | fork _ _ _ ih jh => simp [embed,F.ports,ih,jh]

theorem embed_val (e : ReadTree) (s : Sig) : (embed e).val s=e.value := by
  induction e with
  | atom => rfl
  | fork _ _ _ ih jh => simp only [embed,F.val,ReadTree.value,ih,jh]

theorem embed_set (e : ReadTree) : (embed e).vars.toFinset=e.sources := by
  induction e with
  | atom a => simp [embed,F.vars,ReadTree.sources]
  | fork d l r ih jh => simp [embed,F.vars,ReadTree.sources,ih,jh]

theorem embed_nodup (e : ReadTree) (h : e.linear) : (embed e).vars.Nodup := by
  induction e with
  | atom a => simp [embed,F.vars]
  | fork d l r ih jh =>
    obtain ⟨hl,hr,dis⟩ := h
    apply (ih hl).append (jh hr)
    rw [List.disjoint_left]
    intro a h₁ h₂
    exact Finset.disjoint_left.mp dis
      (embed_set l ▸ List.mem_toFinset.mpr h₁) (embed_set r ▸ List.mem_toFinset.mpr h₂)

private theorem flat_nd {xs : List Sig} (nd : xs.Nodup) (f : Sig→List Sig) (back : Sig→Sig)
    (one : ∀ x∈xs,(f x).Nodup) (recover : ∀x∈xs,∀y∈f x,back y=x) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
    rw [List.flatMap_cons]
    apply (one a List.mem_cons_self).append
      (ih rest (fun x hx => one x (List.mem_cons_of_mem _ hx))
        (fun x hx => recover x (List.mem_cons_of_mem _ hx)))
    rw [List.disjoint_left]
    intro y ya ys
    obtain ⟨x,hx,yx⟩ := List.mem_flatMap.mp ys
    have E : a=x := (recover a List.mem_cons_self y ya).symm.trans
      (recover x (List.mem_cons_of_mem _ hx) y yx)
    exact fresh (by simpa only [E] using hx)

structure Factor (S : Finset Sig) where
  inner : F
  outer : F
  value : outer.val (inner.val zero)=target
  closed : inner.ports=0
  twice : outer.ports=2
  distinct : (inner.vars ++ outer.vars).Nodup
  sources : (inner.vars ++ outer.vars).toFinset=S

private def join (d : Bool) (a b : Sig) : F := .fork d (.atom a) (.atom b)

private theorem clean {U : Finset Sig} {a b : Sig} {d : Bool} (ab : a≠b) (au : a∉U) (bu : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (old : Factor (insert (bin d a b) U)) :
    Nonempty (Factor (insert a (insert b U))) := by
  let z := bin d a b
  let f := fun t : Sig => if t=z then join d a b else F.atom t
  let xs := old.inner.vars ++ old.outer.vars
  have mem (x : Sig) : x∈xs ↔ x=z ∨ x∈U := by
    change x∈old.inner.vars++old.outer.vars ↔ _
    rw [←List.mem_toFinset,old.sources,Finset.mem_insert]
  have ev (s x : Sig) : (f x).val s=x := by by_cases e : x=z <;> simp [f,e,join,F.val,z]
  have item (x w : Sig) : w∈(f x).vars ↔ (x=z ∧ (w=a ∨ w=b)) ∨ (x≠z ∧ w=x) := by
    by_cases e : x=z <;> simp [f,e,join,F.vars]
  let back := fun y : Sig => if y=a ∨ y=b then z else y
  have nd : (xs.flatMap (fun x => (f x).vars)).Nodup := by
    apply flat_nd old.distinct _ back
    · intro x hx; by_cases e : x=z <;> simp [f,e,join,F.vars,ab]
    · intro x hx y hy
      rcases (item x y).mp hy with ⟨xz,ya|yb⟩ | ⟨xz,yx⟩
      · simp [back,ya,xz]
      · simp [back,yb,xz]
      · rw [yx]
        have hu := (mem x).mp hx |>.resolve_left xz
        have na : x≠a := fun e => au (e ▸ hu)
        have nb : x≠b := fun e => bu (e ▸ hu)
        simp [back,na,nb]
  have vars : (old.inner.bind f).vars ++ (old.outer.bind f).vars=xs.flatMap (fun x => (f x).vars) := by
    rw [bind_vars,bind_vars,←List.flatMap_append]
  have cf (x : Sig) : (f x).ports=0 := by by_cases hx : x=z <;> simp [f,hx,join,F.ports]
  refine ⟨⟨old.inner.bind f,old.outer.bind f,?_,?_,?_,by rw [vars]; exact nd,?_⟩⟩
  · rw [bind_val _ _ _ (ev _),bind_val _ _ _ (ev _)]
    exact old.value
  · rw [bind_ports _ _ cf]; exact old.closed
  · rw [bind_ports _ _ cf]; exact old.twice
  · rw [vars]
    ext w
    simp only [List.mem_toFinset,List.mem_flatMap,Finset.mem_insert]
    constructor
    · rintro ⟨x,hx,hy⟩
      obtain ⟨_,e⟩ | ⟨xz,wx⟩ := (item x w).mp hy
      · tauto
      · rw [wx]
        exact Or.inr (Or.inr ((mem x).mp hx |>.resolve_left xz))
    · rintro (rfl|rfl|u)
      · exact ⟨z,(mem z).mpr (.inl rfl),(item _ _).mpr (.inl ⟨rfl,.inl rfl⟩)⟩
      · exact ⟨z,(mem z).mpr (.inl rfl),(item _ _).mpr (.inl ⟨rfl,.inr rfl⟩)⟩
      · have wz : w≠z := fun e => by
          have zu : z∈U := by simpa only [e] using u
          exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem zu))
        exact ⟨w,(mem w).mpr (.inr u),(item _ _).mpr (.inr ⟨wz,rfl⟩)⟩

private theorem shared {k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (au : a∈U) (bu : b∉U) (fresh : bin d a b∉insert a (insert b U))
    (tail : Live k 0 (insert (bin d a b) U)) (tight : (insert (bin d a b) U).card=k+1) :
    Nonempty (Factor (insert a (insert b U))) := by
  obtain ⟨e,ev,el,es⟩ := tight_tree tail rfl (by omega)
  let z := bin d a b
  let xs := (embed e).vars
  let f := fun x : Sig => if x=z then F.fork d .port (.atom b) else if x=a then .port else .atom x
  have mem (w : Sig) : w∈xs ↔ w=z ∨ w∈U := by
    change w∈(embed e).vars ↔ _
    rw [←List.mem_toFinset,embed_set,es,Finset.mem_insert]
  have zb : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have za : z≠a := fun E => zb (by simpa only [E] using au)
  have ab : a≠b := fun E => bu (E ▸ au)
  have item (x w : Sig) : w∈(f x).vars ↔ (x=z ∧ w=b) ∨ (x≠z ∧ x≠a ∧ w=x) := by
    by_cases ez : x=z
    · simp [f,ez,F.vars]
    · by_cases ea : x=a
      · simp [f,ea,Ne.symm za,F.vars]
      · simp [f,ez,ea,F.vars]
  have eval (x : Sig) : (f x).val a=x := by
    by_cases ez : x=z
    · simp only [f,if_pos ez,F.val]; exact ez.symm
    · by_cases ea : x=a
      · simp only [f,if_neg ez,if_pos ea,F.val]; exact ea.symm
      · simp only [f,if_neg ez,if_neg ea,F.val]
  let back := fun y : Sig => if y=b then z else y
  have nd : (xs.flatMap (fun x => (f x).vars)).Nodup := by
    apply flat_nd (embed_nodup e el) _ back
    · intro x hx
      by_cases ez : x=z
      · simp [f,ez,F.vars]
      · by_cases ea : x=a
        · simp [f,ea,Ne.symm za,F.vars]
        · simp [f,ez,ea,F.vars]
    · intro x hx y hy
      rcases (item x y).mp hy with ⟨xz,yb⟩ | ⟨xz,_,yx⟩
      · simp [back,yb,xz]
      · rw [yx]
        have hu := (mem x).mp hx |>.resolve_left xz
        have xb : x≠b := fun E => bu (E ▸ hu)
        simp [back,xb]
  have all (w : Sig) : w∈xs.flatMap (fun x => (f x).vars) ↔ w=b ∨ (w∈U ∧ w≠a) := by
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨x,hx,hy⟩
      rcases (item _ _).mp hy with ⟨_,wb⟩ | ⟨xz,xa,wx⟩
      · exact .inl wb
      · rw [wx]
        exact .inr ⟨(mem x).mp hx |>.resolve_left xz,xa⟩
    · rintro (rfl|⟨wu,wa⟩)
      · exact ⟨z,(mem z).mpr (.inl rfl),(item _ _).mpr (.inl ⟨rfl,rfl⟩)⟩
      · have wz : w≠z := fun E => zb (E ▸ wu)
        exact ⟨w,(mem w).mpr (.inr wu),(item _ _).mpr (.inr ⟨wz,wa,rfl⟩)⟩
  let inner := F.atom a
  let outer := (embed e).bind f
  have vs : inner.vars ++ outer.vars=a::xs.flatMap (fun x => (f x).vars) := by simp [inner,outer,F.vars,bind_vars,xs]
  have two : outer.ports=2 := by
    have od (x : Sig) : (f x).ports=(if x=a then 1 else 0)+(if x=z then 1 else 0) := by
      by_cases hx : x=z <;> by_cases ha : x=a <;> simp_all [f,F.ports]
    have az : a∈xs := (mem a).mpr (.inr au)
    have zz : z∈xs := (mem z).mpr (.inl rfl)
    change ((embed e).bind f).ports=2
    rw [bind_weight,embed_ports,weight_pair f a z od]
    change 0+(tally a xs+tally z xs)=2
    rw [tally_once _ _ (embed_nodup e el),tally_once _ _ (embed_nodup e el)]
    change 0+((if a∈xs then 1 else 0)+(if z∈xs then 1 else 0))=2
    simp [az,zz]
  refine ⟨⟨inner,outer,?_,rfl,two,?_,?_⟩⟩
  · change ((embed e).bind f).val a=target
    rw [bind_val _ _ _ eval,embed_val,ev]
  · rw [vs,List.nodup_cons]
    exact ⟨fun h => by simpa [ab] using (all a).mp h,nd⟩
  · rw [vs]
    ext w
    simp only [List.mem_toFinset,List.mem_cons,Finset.mem_insert,all]
    by_cases wa : w=a <;> simp_all

private theorem bin_swap (d : Bool) (a b : Sig) : bin d a b=bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

/-- One unit beyond tree size has a single common subformula. Removing the
two abstract ports leaves every original variable present exactly once,
over the two syntactically separate formulas. -/
theorem factor_aux {k t S} (h : Live k t S) (hz : t=0) (slack : S.card+t=k) :
    Nonempty (Factor S) := by
  induction h with
  | stop => simp at slack
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb ab hf tail ih =>
    subst t
    have zu : bin d a b∉U := fun m => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have after := ProtocolProof.width tail
    rw [Finset.card_insert_of_notMem zu] at after
    by_cases au : a∈U
    · have ai : a∈insert b U := Finset.mem_insert_of_mem au
      rw [Finset.insert_eq_of_mem ai] at slack
      by_cases bu : b∈U
      · rw [Finset.insert_eq_of_mem bu] at slack; omega
      · rw [Finset.card_insert_of_notMem bu] at slack
        exact shared au bu hf tail (by rw [Finset.card_insert_of_notMem zu]; omega)
    · have ai : a∉insert b U := by simpa [ab] using au
      rw [Finset.card_insert_of_notMem ai] at slack
      by_cases bu : b∈U
      · rw [Finset.insert_eq_of_mem bu] at slack
        have hh := shared (d:=d) bu au
          (by simpa only [bin_swap d b a,Finset.insert_comm b a] using hf)
          (by simpa only [bin_swap d b a] using tail)
          (by rw [bin_swap d b a,Finset.card_insert_of_notMem zu]; omega)
        simpa only [Finset.insert_comm b a] using hh
      · rw [Finset.card_insert_of_notMem bu] at slack
        obtain ⟨old⟩ := ih rfl (by rw [Finset.card_insert_of_notMem zu]; omega)
        exact clean ab au bu hf old

theorem factor {k S} (h : Live k 0 S) (size : S.card=k) : Nonempty (Factor S) :=
  factor_aux h rfl (by omega)

#print axioms factor
end CoAO3143.OneShare
