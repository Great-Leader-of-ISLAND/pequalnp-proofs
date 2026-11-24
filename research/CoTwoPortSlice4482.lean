import PEqualNP.CoPortSlice4482
namespace CoTwoPortSlice4482
open CoPortSlice4482

abbrev Pair := Bool × Bool
def below (a b : Pair) := (a.1=true → b.1=true) ∧ (a.2=true → b.2=true)

/-- On a Boolean interval of dimension at most two, the only incomparable
    interior elements are 01 and 10. Oppositely ordered labels at its fixed
    endpoints force the orientation of all comparable elements. -/
theorem two_bit_interval : ∀ (d : Pair → Bool) (l h p n : Pair),
    below l p → below p h → below l n → below n h →
    d l = false → d h = true → d p = true → d n = false →
    (p.1=true ∧ n.1=false) ∨ (p.2=true ∧ n.2=false) := by decide +kernel

theorem two_marks (b : Nat) (vals : Input → Pair)
    (mono : ∀ x y, leInput x y → below (vals x) (vals y))
    (determined : ∀ x y, sameOn b x y → vals x=vals y → graph x=graph y)
    (lo hi p n : Input)
    (sl : sameOn b lo p) (sh : sameOn b hi p) (sn : sameOn b n p)
    (lop : leInput lo p) (phi : leInput p hi) (lon : leInput lo n) (nhi : leInput n hi)
    (lf : graph lo=false) (ht : graph hi=true) (pt : graph p=true) (nf : graph n=false) :
    ((vals p).1=true ∧ (vals n).1=false) ∨ ((vals p).2=true ∧ (vals n).2=false) := by
  classical
  let d := fun v : Pair => decide (∃ a, sameOn b a p ∧ vals a=v ∧ graph a=true)
  have eq (x : Input) (s : sameOn b x p) : d (vals x)=graph x := by
    cases g : graph x with
    | false =>
      apply Bool.eq_false_iff.mpr
      intro cert
      obtain ⟨a,same,m,e⟩ := of_decide_eq_true cert
      have clash := determined a x (by
        intro i hit
        exact (same i hit).trans (s i hit).symm) m
      rw [e,g] at clash
      contradiction
    | true =>
      exact decide_eq_true ⟨x,s,rfl,g⟩
  exact two_bit_interval d (vals lo) (vals hi) (vals p) (vals n)
    (mono _ _ lop) (mono _ _ phi) (mono _ _ lon) (mono _ _ nhi)
    ((eq lo sl).trans lf) ((eq hi sh).trans ht)
    ((eq p (by intro i _; rfl)).trans pt) ((eq n sn).trans nf)

#print axioms two_marks
end CoTwoPortSlice4482
