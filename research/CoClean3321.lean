import Mathlib

namespace CoClean3321

abbrev Side (P : Type) := P → Bool
abbrev Signal (P L : Type) := Side P → Side L → Bool
def zero {P : Type} : Side P := fun _ => false
noncomputable def single {P : Type} (p : P) : Side P := by
  classical
  exact fun x => decide (x=p)

def edge {P L : Type} (I : P→L→Prop) (x : Side P) (y : Side L) : Prop :=
  ∃ p l, I p l ∧ x p=true ∧ y l=true

/-- The three-way implication in L-meta-3321, expressed on separate shores. -/
def Clean {P L : Type} (I : P→L→Prop) (h : Signal P L) : Prop :=
  ∀ x y, h x y=true → h x zero=true ∨ h zero y=true ∨ edge I x y

def Onehot {P L : Type} (h : Signal P L) : Prop :=
  (∀ p : P, h (single p) zero=false) ∧ (∀ l : L, h zero (single l)=false)

theorem enlarge {P L : Type} {I J : P→L→Prop} {h : Signal P L}
    (sub : ∀ p l, I p l → J p l) (clean : Clean I h) : Clean J h := by
  intro x y hx
  rcases clean x y hx with v|v|⟨p,l,e,hp,hl⟩
  · exact Or.inl v
  · exact Or.inr (Or.inl v)
  · exact Or.inr (Or.inr ⟨p,l,sub p l e,hp,hl⟩)

/-- Each new variable is wired to one old representative. Empty fibers are
    constantly false; all other fibers are combined by a pure-shore OR. -/
noncomputable def push {P Q : Type} (f : P→Q) (x : Side P) : Side Q := by
  classical
  exact fun q => decide (∃ p, f p=q ∧ x p=true)

theorem push_zero {P Q : Type} (f : P→Q) : push f zero = zero := by
  classical
  funext q
  simp [push,zero]

theorem push_single {P Q : Type} (f : P→Q) (p : P) : push f (single p)=single (f p) := by
  classical
  funext q
  apply Bool.eq_iff_iff.mpr
  simp [push,single,eq_comm]

theorem edge_pull {P Q L M : Type} (f : P→Q) (g : L→M) (I : Q→M→Prop)
    (x : Side P) (y : Side L) :
    edge I (push f x) (push g y) ↔ edge (fun p l => I (f p) (g l)) x y := by
  classical
  constructor
  · rintro ⟨q,m,e,hq,hm⟩
    obtain ⟨p,ep,hp⟩ : ∃ p, f p=q ∧ x p=true := of_decide_eq_true hq
    obtain ⟨l,el,hl⟩ : ∃ l, g l=m ∧ y l=true := of_decide_eq_true hm
    exact ⟨p,l,by simpa [ep,el] using e,hp,hl⟩
  · rintro ⟨p,l,e,hp,hl⟩
    refine ⟨f p,g l,e,?_,?_⟩
    · exact decide_eq_true ⟨p,rfl,hp⟩
    · exact decide_eq_true ⟨l,rfl,hl⟩

theorem pull_clean_onehot {P Q L M : Type} (f : P→Q) (g : L→M) (I : Q→M→Prop)
    (h : Signal Q M) (clean : Clean I h) (ones : Onehot h) :
    let H : Signal P L := fun x y => h (push f x) (push g y)
    Clean (fun p l => I (f p) (g l)) H ∧ Onehot H := by
  dsimp only
  constructor
  · intro x y hit
    rcases clean _ _ hit with hp|hl|e
    · exact Or.inl (by simpa [push_zero] using hp)
    · exact Or.inr (Or.inl (by simpa [push_zero] using hl))
    · exact Or.inr (Or.inr ((edge_pull f g I x y).mp e))
  · constructor
    · intro p
      simpa [push_single,push_zero] using ones.1 (f p)
    · intro l
      simpa [push_single,push_zero] using ones.2 (g l)

/-- The only new AND when restoring a point-centered star: its truth always
    witnesses an actual edge, even on a mixed multivertex assignment. -/
noncomputable def pointStar {P L : Type} (c : P) (ns : Finset L) : Signal P L := by
  classical
  exact fun x y => x c && decide (∃ l∈ns, y l=true)

theorem pointStar_clean_onehot {P L : Type} (I : P→L→Prop) (c : P) (ns : Finset L)
    (links : ∀ l∈ns, I c l) : Clean I (pointStar c ns) ∧ Onehot (pointStar c ns) := by
  classical
  constructor
  · intro x y hit
    obtain ⟨hx,hy⟩ := Bool.and_eq_true.mp hit
    obtain ⟨l,hl,yy⟩ : ∃ l∈ns, y l=true := of_decide_eq_true hy
    exact Or.inr (Or.inr ⟨c,l,links l hl,hx,yy⟩)
  · constructor <;> intros <;> simp [pointStar,zero]

theorem swap_clean_onehot {P L : Type} (I : P→L→Prop) (h : Signal P L)
    (clean : Clean I h) (ones : Onehot h) :
    Clean (fun l p => I p l) (fun y x => h x y) ∧ Onehot (fun y x => h x y) := by
  constructor
  · intro y x hit
    rcases clean x y hit with p|l|⟨i,j,e,a,b⟩
    · exact Or.inr (Or.inl p)
    · exact Or.inl l
    · exact Or.inr (Or.inr ⟨j,i,e,b,a⟩)
  · exact ⟨ones.2,ones.1⟩

#print axioms CoClean3321.pull_clean_onehot
#print axioms CoClean3321.pointStar_clean_onehot
end CoClean3321
