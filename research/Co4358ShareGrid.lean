import PEqualNP.Co4358OneShareCotree
import PEqualNP.Co4358TinyRect
namespace CoNum4358.Tiny.ShareGrid
open CoAO3143
open CoAO3143.ProtocolProof (Forced separates)

def up (X : Finset K) : Finset Sig := X.image wide
def FreeCell (X : Finset K) (p : Fin 8) (n : Fin 7) := ∀a∈X,directed a p n=false
def Required (X : Finset K) (p : Fin 8) (n : Fin 7) :=
  (∃m,FreeCell X p m) ∧ (∃q,FreeCell X q n)
def Owner (X : Finset K) (p : Fin 8) (n : Fin 7) (a : K) := ∀b∈X,directed b p n=true → b=a

def Arc (X : Finset K) (D : Fin 8→Fin 7→Prop) (d : Bool) (a b : K) := if d then
  ∃ (p : Fin 8) (i j : Fin 7), D p i ∧ Owner X p i a ∧ D p j ∧ Owner X p j b
  else ∃ (n : Fin 7) (i j : Fin 8), D i n ∧ Owner X i n a ∧ D j n ∧ Owner X j n b

def Linked (r : K → K → Prop) (s : Finset K) :=
  ∀ c : K→Bool, (∀x∈s,∀y∈s,r x y → c x=c y) → ∀x∈s,∀y∈s,c x=c y

def Compatible (X : Finset K) (D : Fin 8→Fin 7→Prop) :=
  ∀ s⊆X, (∀d,Linked (Arc X D d) s) → ∀a∈s,∀b∈s,a=b

def Feasible (A B : Finset K) :=
  (∀p n,Required B p n → ∃w∈A,directed w p n=true) ∧
    Compatible A (Required B) ∧ Compatible B (FreeCell A)

theorem separates_iff (a : K) (p : Fin 8) (n : Fin 7) :
    separates (pos p) (negRow n) (wide a) ↔ directed a p n=true := by
  simp only [separates,pos_bit,neg_bit,directed,Bool.and_eq_true,Bool.not_eq_true']

theorem free_cell {X : Finset K} {p n} (h : FreeCell X p n) :
    OneShare.Miss (up X) (pos p) (negRow n) := by
  intro w hw yes
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hw
  exact Bool.false_ne_true ((h a ha).symm.trans ((separates_iff a p n).mp yes))

theorem required_grid {X : Finset K} {p n} (h : Required X p n) :
    OneShare.InGrid (up X) (pos p) (negRow n) := by
  obtain ⟨⟨m,hm⟩,⟨q,hq⟩⟩ := h
  exact ⟨⟨negRow m,free_cell hm⟩,⟨pos q,free_cell hq⟩⟩

theorem owner_forced {X : Finset K} {p n a} (h : Owner X p n a) :
    Forced (up X) (pos p) (negRow n) (wide a) := by
  intro w hw yes
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hw
  exact congrArg wide (h b hb ((separates_iff _ _ _).mp yes))

theorem restrict_graph {X : Finset K} {large : Row→Row→Prop} {D : Fin 8→Fin 7→Prop}
    (old : OneShare.Compatible (up X) large) (ok : ∀p n,D p n→large (pos p) (negRow n)) :
    Compatible X D := by
  have arcs (d : Bool) {a b} (edge : Arc X D d a b) : OneShare.Edge (up X) large d (wide a) (wide b) := by
    cases d
    · obtain ⟨n,i,j,hi,oi,hj,oj⟩ := edge
      exact ⟨negRow n,pos i,pos j,ok _ _ hi,owner_forced oi,ok _ _ hj,owner_forced oj⟩
    · obtain ⟨p,i,j,hi,oi,hj,oj⟩ := edge
      exact ⟨pos p,negRow i,negRow j,ok _ _ hi,owner_forced oi,ok _ _ hj,owner_forced oj⟩
  intro s sub all a ha b hb
  apply wide_inj
  apply old (up s) (Finset.image_mono sub) _ (wide a) (Finset.mem_image_of_mem _ ha)
    (wide b) (Finset.mem_image_of_mem _ hb)
  intro d color mono x hx y hy
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
  apply all d (fun a => color (wide a)) _ v hv w hw
  intro r hr t ht arc
  exact mono _ (Finset.mem_image_of_mem _ hr) _ (Finset.mem_image_of_mem _ ht) (arcs d arc)

theorem tight_plus_one {k : Nat} {X : Finset K} (run : Live k 0 (up X)) (size : X.card=k) :
    ∃ A⊆X, A.Nonempty ∧ Feasible A (X\A) := by
  classical
  have count : (up X).card=k := (Finset.card_image_of_injective _ wide_inj).trans size
  obtain ⟨T,U,tn,both,dis,cover,inner,outer⟩ := OneShare.single_share_necessary run count
  let A := X.filter fun a => wide a∈T
  have sub : A⊆X := Finset.filter_subset _ _
  have tt : up A=T := by
    ext w
    constructor
    · intro hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hv).2
    · intro hw
      have all : w∈up X := both ▸ Finset.mem_union_left U hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp all
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hv,hw⟩)
  have uu : up (X\A)=U := by
    ext w
    constructor
    · intro hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨vx,va⟩ := Finset.mem_sdiff.mp hv
      have all : wide v∈T∪U := by rw [both]; exact Finset.mem_image_of_mem _ vx
      exact (Finset.mem_union.mp all).resolve_left (fun vt => va (Finset.mem_filter.mpr ⟨vx,vt⟩))
    · intro hw
      have all : w∈up X := both ▸ Finset.mem_union_right T hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp all
      apply Finset.mem_image_of_mem
      apply Finset.mem_sdiff.mpr
      exact ⟨hv,fun va => Finset.disjoint_left.mp dis (Finset.mem_filter.mp va).2 hw⟩
  rw [←tt,←uu] at cover inner outer
  have na : A.Nonempty := by
    obtain ⟨v,hv⟩ := tn
    rw [←tt] at hv
    obtain ⟨x,hx,_⟩ := Finset.mem_image.mp hv
    exact ⟨x,hx⟩
  refine ⟨A,sub,na,?_,restrict_graph inner (fun _ _ h => required_grid h),
    restrict_graph outer (fun _ _ h => free_cell h)⟩
  intro p n need
  obtain ⟨v,hv,yes⟩ := cover (pos p) (negRow n) (required_grid need)
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
  exact ⟨a,ha,(separates_iff _ _ _).mp yes⟩

#print axioms tight_plus_one
end CoNum4358.Tiny.ShareGrid
