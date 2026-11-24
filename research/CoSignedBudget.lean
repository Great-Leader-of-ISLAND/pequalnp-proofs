import PEqualNP.Outside.L_meta_1667

namespace PEqualNP.Research.SignedBudget
open PEqualNP.Outside.L_meta_1667

def pref (K : Finset Nat) (t : Nat) := K.filter (· < t)

theorem pref_succ (K : Finset Nat) (t : Nat) :
    (pref K (t+1)).card = (pref K t).card + (if t ∈ K then 1 else 0) := by
  classical
  by_cases h : t ∈ K
  · have eq : pref K (t+1) = insert t (pref K t) := by
      ext j
      simp only [pref,Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hj,lt⟩
        by_cases e : j=t
        · exact Or.inl e
        · exact Or.inr ⟨hj,by omega⟩
      · rintro (rfl | ⟨hj,lt⟩)
        · exact ⟨h,by omega⟩
        · exact ⟨hj,by omega⟩
    simp [eq,h,pref]
  · have eq : pref K (t+1) = pref K t := by
      ext j
      simp only [pref,Finset.mem_filter]
      constructor
      · rintro ⟨hj,lt⟩
        have ne : j ≠ t := fun e => h (e ▸ hj)
        exact ⟨hj,by omega⟩
      · rintro ⟨hj,lt⟩
        exact ⟨hj,by omega⟩
    simp [eq,h]

def lit {R : Type} (w : Nat → Wire R) (a : Nat × Bool) : Wire R :=
  if a.2 then inv (w a.1) else w a.1

def ready {R} (w : Nat → Wire R) (K : Finset Nat) (t : Nat) (bank : List (Wire R)) :=
  ∀ i < t, Available bank (w i) ∧ (i ∈ K → Available bank (inv (w i)))

theorem signed_avail {R} {w : Nat → Wire R} {K : Finset Nat} {t bank} (h : ready w K t bank)
    (a : Nat × Bool) (order : a.1 < t) (legal : a.2 = true → a.1 ∈ K ∨ Constant (w a.1)) :
    Available bank (lit w a) := by
  rcases a with ⟨j,b⟩
  cases b with
  | false => exact (h j order).1
  | true =>
    rcases legal rfl with hm | hc
    · exact (h j order).2 hm
    · exact Or.inr (inv_constant hc)

theorem budget {R : Type} (w : Nat → Wire R) (K : Finset Nat) (base : List (Wire R))
    (n m : Nat) (raw : ∀ i < n, Available base (w i))
    (spec : ∀ j, n ≤ j → j < n+m → ∃ op a b,
      a.1 < j ∧ b.1 < j ∧ (a.2=true → a.1∈K ∨ Constant (w a.1)) ∧
      (b.2=true → b.1∈K ∨ Constant (w b.1)) ∧ w j = combine op (lit w a) (lit w b)) :
    ∀ t ≤ n+m, ∃ p bank, Reach base p bank ∧ ready w K t bank ∧
      supply bank base ∧ p ≤ (t-n) + (pref K t).card := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨0,base,Reach.start,fun i h => by omega,fun a ha => Or.inl ha,by omega⟩
  | succ t ih =>
    intro ht
    obtain ⟨p,bank,reach,old,keep,hp⟩ := ih (by omega)
    have step : ∃ q next, Reach base q next ∧ Available next (w t) ∧
        (∀ v, Available bank v → Available next v) ∧ q ≤ (t+1-n) + (pref K t).card := by
      by_cases hn : t < n
      · have av := raw t hn
        exact ⟨p,bank,reach,av.elim (keep _) Or.inr,fun _ h => h,by omega⟩
      · obtain ⟨op,a,b,ha,hb,la,lb,ev⟩ := spec t (by omega) (by omega)
        have r := Reach.two op reach (signed_avail old a ha la) (signed_avail old b hb lb)
        exact ⟨p+1,_,r,Or.inl (by simp [ev]),fun v h => available_cons _ h,by omega⟩
    obtain ⟨q,next,r,cur,retain,hq⟩ := step
    rw [pref_succ]
    by_cases paid : t ∈ K
    · refine ⟨q+1,inv (w t)::next,Reach.one r cur,?_,?_,by simp [paid]; omega⟩
      · intro i hi
        by_cases e : i=t
        · subst i
          exact ⟨available_cons _ cur,fun _ => Or.inl (by simp)⟩
        · have earlier := old i (by omega)
          exact ⟨available_cons _ (retain _ earlier.1),fun h => available_cons _ (retain _ (earlier.2 h))⟩
      · exact fun v hv => available_cons _ (retain _ (keep v hv))
    · refine ⟨q,next,r,?_,fun v hv => retain _ (keep v hv),by simpa [paid] using hq⟩
      intro i hi
      by_cases e : i=t
      · subst i
        exact ⟨cur,fun h => False.elim (paid h)⟩
      · have earlier := old i (by omega)
        exact ⟨retain _ earlier.1,fun h => retain _ (earlier.2 h)⟩

end PEqualNP.Research.SignedBudget
