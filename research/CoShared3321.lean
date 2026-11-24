import PEqualNP.CoClean3321
namespace CoClean3321

def Grows {P L : Type} (h : Signal P L) := ∀ {x x' : Side P} {y y' : Side L},
  (∀ p, x p=true → x' p=true) → (∀ l, y l=true → y' l=true) → h x y=true → h x' y'=true

def prod {P L : Type} (h k : Signal P L) : Signal P L := fun x y => h x y && k x y

private theorem paired {P L : Type} (I : P→L→Prop) (p : P) (l : L) :
    edge I (single p) (single l) ↔ I p l := by
  classical
  constructor
  · rintro ⟨q,m,e,hq,hm⟩
    have a : q=p := of_decide_eq_true hq
    have b : m=l := of_decide_eq_true hm
    simpa [a,b] using e
  · exact fun e => ⟨p,l,e,by simp [single],by simp [single]⟩

theorem crosses {P L : Type} {I : P→L→Prop} {h k : Signal P L}
    (mh : Grows h) (mk : Grows k) (clean : Clean I (prod h k)) (ones : Onehot (prod h k))
    {p : P} {l : L} (ph : h (single p) zero=true) (lk : k zero (single l)=true) : I p l := by
  have a : h (single p) (single l)=true := mh (fun _ hp => hp) (by simp [zero]) ph
  have b : k (single p) (single l)=true := mk (by simp [zero]) (fun _ hl => hl) lk
  have acts : prod h k (single p) (single l)=true := Bool.and_eq_true_iff.mpr ⟨a,b⟩
  rcases clean _ _ acts with wrong|wrong|found
  · rw [ones.1] at wrong
    contradiction
  · rw [ones.2] at wrong
    contradiction
  · exact (paired I p l).mp found

/-- Even two different readers of one shared wire have the same possible
    opposite singleton coordinate once that wire accepts two points. -/
theorem shared_opposite_unique {P L : Type} {I : P→L→Prop} {w k v : Signal P L}
    (noSquare : ∀ p q l m, p≠q → l≠m → ¬ (I p l ∧ I p m ∧ I q l ∧ I q m))
    (mw : Grows w) (mk : Grows k) (mv : Grows v)
    (ck : Clean I (prod w k)) (ok : Onehot (prod w k))
    (cv : Clean I (prod w v)) (ov : Onehot (prod w v))
    {p q : P} {l m : L} (pq : p≠q)
    (wp : w (single p) zero=true) (wq : w (single q) zero=true)
    (kl : k zero (single l)=true) (vm : v zero (single m)=true) : l=m := by
  by_contra ne
  exact noSquare p q l m pq ne
    ⟨crosses mw mk ck ok wp kl,crosses mw mv cv ov wp vm,
     crosses mw mk ck ok wq kl,crosses mw mv cv ov wq vm⟩

structure Mask (P L : Type) where
  points : Finset P
  lines : Finset L

noncomputable def lit {P L : Type} (a : Mask P L) : Signal P L := by
  classical
  exact fun x y => decide ((∃ p∈a.points, x p=true) ∨ (∃ l∈a.lines, y l=true))

private theorem lit_left {P L : Type} (a : Mask P L) (x : Side P) :
    lit a x zero=true ↔ ∃ p∈a.points, x p=true := by
  classical
  simp [lit,zero]
private theorem lit_right {P L : Type} (a : Mask P L) (y : Side L) :
    lit a zero y=true ↔ ∃ l∈a.lines, y l=true := by
  classical
  simp [lit,zero]
private theorem lit_p {P L : Type} (a : Mask P L) (p : P) :
    lit a (single p) zero=true ↔ p∈a.points := by
  classical
  simp [lit,zero,single]
private theorem lit_l {P L : Type} (a : Mask P L) (l : L) :
    lit a zero (single l)=true ↔ l∈a.lines := by
  classical
  simp [lit,zero,single]

private theorem lit_grows {P L : Type} (a : Mask P L) : Grows (lit a) := by
  classical
  intro x x' y y' px ly hit
  change decide ((∃ p∈a.points, x' p=true) ∨ (∃ l∈a.lines, y' l=true))=true
  apply decide_eq_true
  rcases of_decide_eq_true hit with ⟨p,hp,v⟩|⟨l,hl,v⟩
  · exact Or.inl ⟨p,hp,px p v⟩
  · exact Or.inr ⟨l,hl,ly l v⟩

/-- Necessary and sufficient for an AND of two arbitrary OR masks to satisfy
    the exact strong gate condition; the two opposite rectangles are separate. -/
theorem rectangle_criterion {P L : Type} (I : P→L→Prop) (a b : Mask P L) :
    (Clean I (prod (lit a) (lit b)) ∧ Onehot (prod (lit a) (lit b))) ↔
    Disjoint a.points b.points ∧ Disjoint a.lines b.lines ∧
    (∀ p∈a.points, ∀ l∈b.lines, I p l) ∧ (∀ p∈b.points, ∀ l∈a.lines, I p l) := by
  classical
  constructor
  · rintro ⟨clean,ones⟩
    have eq : prod (lit b) (lit a)=prod (lit a) (lit b) := by
      funext x y; simp [prod,Bool.and_comm]
    have clean' : Clean I (prod (lit b) (lit a)) := eq.symm ▸ clean
    have ones' : Onehot (prod (lit b) (lit a)) := eq.symm ▸ ones
    refine ⟨Finset.disjoint_left.mpr ?_,Finset.disjoint_left.mpr ?_,?_,?_⟩
    · intro p hp hq
      have both : prod (lit a) (lit b) (single p) zero=true :=
        Bool.and_eq_true_iff.mpr ⟨(lit_p a p).mpr hp,(lit_p b p).mpr hq⟩
      rw [ones.1] at both
      contradiction
    · intro l hl hm
      have both : prod (lit a) (lit b) zero (single l)=true :=
        Bool.and_eq_true_iff.mpr ⟨(lit_l a l).mpr hl,(lit_l b l).mpr hm⟩
      rw [ones.2] at both
      contradiction
    · intro p hp l hl
      exact crosses (lit_grows a) (lit_grows b) clean ones ((lit_p a p).mpr hp) ((lit_l b l).mpr hl)
    · intro p hp l hl
      exact crosses (lit_grows b) (lit_grows a) clean' ones' ((lit_p b p).mpr hp) ((lit_l a l).mpr hl)
  · rintro ⟨dp,dl,ab,ba⟩
    constructor
    · intro x y v
      obtain ⟨va,vb⟩ := Bool.and_eq_true_iff.mp v
      rcases of_decide_eq_true va with pa|la <;> rcases of_decide_eq_true vb with pb|lb
      · exact Or.inl (Bool.and_eq_true_iff.mpr ⟨(lit_left a x).mpr pa,(lit_left b x).mpr pb⟩)
      · obtain ⟨p,hp,pv⟩ := pa
        obtain ⟨l,hl,lv⟩ := lb
        exact Or.inr (Or.inr ⟨p,l,ab p hp l hl,pv,lv⟩)
      · obtain ⟨p,hp,pv⟩ := pb
        obtain ⟨l,hl,lv⟩ := la
        exact Or.inr (Or.inr ⟨p,l,ba p hp l hl,pv,lv⟩)
      · exact Or.inr (Or.inl (Bool.and_eq_true_iff.mpr ⟨(lit_right a y).mpr la,(lit_right b y).mpr lb⟩))
    · have off (b : Bool) (e : b≠true) : b=false := by cases b <;> simp_all
      constructor
      · intro p
        apply off
        intro hit
        obtain ⟨hp,hq⟩ := Bool.and_eq_true_iff.mp hit
        exact Finset.disjoint_left.mp dp ((lit_p a p).mp hp) ((lit_p b p).mp hq)
      · intro l
        apply off
        intro hit
        obtain ⟨hl,hm⟩ := Bool.and_eq_true_iff.mp hit
        exact Finset.disjoint_left.mp dl ((lit_l a l).mp hl) ((lit_l b l).mp hm)

#print axioms CoClean3321.rectangle_criterion
#print axioms CoClean3321.shared_opposite_unique
end CoClean3321
