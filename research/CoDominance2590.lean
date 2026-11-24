import PEqualNP.Defs

namespace CoDominance2590
universe u
variable {R : Type u}
abbrev Wire (R : Type u) := R → Bool
abbrev Bank (R : Type u) := Wire R → Prop

/-- The first function is the original wire's truth on all tested rows. -/
def Better (target a b : Wire R) : Prop :=
  (∀ r, target r=true → a r=true → b r=true) ∧
  (∀ r, target r=false → b r=true → a r=true)

theorem same (target a : Wire R) : Better target a a :=
  ⟨fun _ _ h => h,fun _ _ h => h⟩

theorem compose {target a b c : Wire R} (ab : Better target a b) (bc : Better target b c) : Better target a c :=
  ⟨fun r h e => bc.1 r h (ab.1 r h e),fun r h e => ab.2 r h (bc.2 r h e)⟩

def mix (join : Bool) (a b : Wire R) : Wire R :=
  fun r => if join then a r || b r else a r && b r

private theorem monotone (join a b x y : Bool) (ax : a=true → x=true) (byy : b=true → y=true)
    (v : (if join then a || b else a && b)=true) :
    (if join then x || y else x && y)=true := by
  cases join <;> cases a <;> cases b <;> cases x <;> cases y <;> simp_all

theorem gate {target a b x y : Wire R} (d : Bool) (ax : Better target a x) (byy : Better target b y) :
    Better target (mix d a b) (mix d x y) := by
  exact ⟨fun r h => monotone d _ _ _ _ (ax.1 r h) (byy.1 r h),
    fun r h => monotone d _ _ _ _ (ax.2 r h) (byy.2 r h)⟩

theorem output {target v : Wire R} (h : Better target target v) : v=target := by
  funext r
  cases e : target r with
  | false =>
    by_contra bad
    have yes : v r=true := by cases z : v r <;> simp_all
    exact Bool.false_ne_true (e.symm.trans (h.2 r e yes))
  | true => exact h.1 r e e

def insert (w : Wire R) (pool : Bank R) : Bank R := fun v => v=w ∨ pool v

inductive Built (base : Bank R) : Nat → Bank R → Prop
  | start : Built base 0 base
  | paid {h : Nat} {pool : Bank R} {a b : Wire R} (pre : Built base h pool) (ha : pool a) (hb : pool b)
      (d : Bool) : Built base (h+1) (insert (mix d a b) pool)

def Sim (target : Wire R) (original proxy : Bank R) : Prop :=
  ∀ w, original w → ∃ v, proxy v ∧ Better target w v

theorem free {target : Wire R} {old pool : Bank R} (res : Sim target old pool)
    {a b x y z : Wire R} (d : Bool) (hx : Better target a x) (hy : Better target b y)
    (available : pool z) (better : Better target (mix d x y) z) :
    Sim target (insert (mix d a b) old) pool := by
  intro w hw
  rcases hw with rfl|past
  · exact ⟨z,available,compose (gate d hx hy) better⟩
  · exact res w past

theorem extend {target : Wire R} {old pool : Bank R} (res : Sim target old pool)
    {a b x y : Wire R} (d : Bool) (hx : Better target a x) (hy : Better target b y) :
    Sim target (insert (mix d a b) old) (insert (mix d x y) pool) := by
  intro w hw
  rcases hw with rfl|past
  · exact ⟨_,Or.inl rfl,gate d hx hy⟩
  · obtain ⟨v,hv,good⟩ := res w past
    exact ⟨v,Or.inr hv,good⟩

inductive Tail (target : Wire R) : Nat → Bank R → Prop
  | done {pool : Bank R} (endOK : pool target) : Tail target 0 pool
  | step {k : Nat} {pool : Bank R} {a b : Wire R} (ha : pool a) (hb : pool b) (d : Bool)
      (next : Tail target k (insert (mix d a b) pool)) : Tail target (k+1) pool

theorem continuation {target : Wire R} {k : Nat} {old : Bank R} (rest : Tail target k old)
    {base pool : Bank R} {h : Nat} (pre : Built base h pool) (sim : Sim target old pool) :
    ∃ result, Built base (h+k) result ∧ result target := by
  induction rest generalizing pool h with
  | done ok =>
    obtain ⟨v,hv,e⟩ := sim _ ok
    exact ⟨pool,by simpa using pre,(output e) ▸ hv⟩
  | @step k old a b ha hb d next ih =>
    obtain ⟨x,hx,ax⟩ := sim _ ha
    obtain ⟨y,hy,byy⟩ := sim _ hb
    obtain ⟨out,proof,finished⟩ := ih (Built.paid pre hx hy d) (extend sim d ax byy)
    exact ⟨out,by convert proof using 1 <;> omega,finished⟩

theorem required {target : Wire R} {base old pool : Bank R} {price h k : Nat}
    (lower : ∀ j p, Built base j p → p target → price≤j)
    (projected : Built base h pool) (sim : Sim target old pool) (remain : Tail target k old) :
    price≤h+k := by
  obtain ⟨p,hp,fin⟩ := continuation remain projected sim
  exact lower _ _ hp fin

end CoDominance2590
