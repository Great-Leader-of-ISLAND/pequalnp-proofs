import Mathlib
import PEqualNP.Defs

namespace CoTheta3174Public

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive Der {α : Type} (op : Fin 4 → α → α → α) : ℕ → Set α → α → Prop
  | here {W : Set α} {y : α} : y ∈ W → Der op 0 W y
  | weak {k : ℕ} {W : Set α} {y : α} : Der op k W y → Der op (k + 1) W y
  | step {k : ℕ} {W : Set α} {y : α} (t : Fin 4) (a b : α) : a ∈ W → b ∈ W →
      Der op k (insert (op t a b) W) y → Der op (k + 1) W y

theorem Der.mono {α : Type} {op : Fin 4 → α → α → α} {k : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) : ∀ {W' : Set α}, W ⊆ W' → Der op k W' y := by
  induction h with
  | here hy => intro W' hs; exact Der.here (hs hy)
  | weak _ ih => intro W' hs; exact Der.weak (ih hs)
  | step t a b ha hb _ ih =>
    intro W' hs
    exact Der.step t a b (hs ha) (hs hb) (ih (Set.insert_subset_insert hs))

theorem Der.le {α : Type} {op : Fin 4 → α → α → α} {k k' : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) (hk : k ≤ k') : Der op k' W y := by
  induction hk with
  | refl => exact h
  | step _ ih => exact Der.weak ih

theorem Der.map {α β : Type} {op : Fin 4 → α → α → α} {op' : Fin 4 → β → β → β} (e : α → β)
    (he : ∀ t a b, e (op t a b) = op' t (e a) (e b)) {k : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) : Der op' k (e '' W) (e y) := by
  induction h with
  | here hy => exact Der.here ⟨_, hy, rfl⟩
  | weak _ ih => exact Der.weak ih
  | step t a b ha hb _ ih =>
    refine Der.step t (e a) (e b) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ?_
    rwa [Set.image_insert_eq, he] at ih

theorem Der.elim {α β : Type} {op : Fin 4 → α → α → α} {op' : Fin 4 → β → β → β} (e : α → β)
    (he : ∀ t a b, e (op t a b) = op' t (e a) (e b)) (x : α)
    (hl : ∀ t b, op' t (e x) b = e x ∨ op' t (e x) b = b)
    (hr : ∀ t b, op' t b (e x) = e x ∨ op' t b (e x) = b)
    {k : ℕ} {W : Set α} {y : α} (h : Der op k W y) :
    ∀ U : Set α, W ⊆ insert x U → y ≠ x → e x ∈ e '' U →
      Der op k U y ∨ ∃ k', k = k' + 1 ∧ Der op' k' (e '' U) (e y) := by
  induction h with
  | here hy =>
    intro U hs hne _
    exact Or.inl (Der.here ((hs hy).resolve_left hne))
  | weak _ ih =>
    intro U hs hne hx
    rcases ih U hs hne hx with h | ⟨k', rfl, h⟩
    · exact Or.inl (Der.weak h)
    · exact Or.inr ⟨_, rfl, Der.weak h⟩
  | @step k W y t a b ha hb h ih =>
    intro U hs hne hx
    have im (w : α) (hw : w ∈ W) : e w ∈ e '' U := by
      rcases hs hw with rfl | hw
      · exact hx
      · exact ⟨w, hw, rfl⟩
    by_cases hab : a ∈ U ∧ b ∈ U
    · have hs' : insert (op t a b) W ⊆ insert x (insert (op t a b) U) := by
        rintro w (rfl | hw)
        · exact Or.inr (Or.inl rfl)
        · rcases hs hw with rfl | hw
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hw)
      have hx' : e x ∈ e '' insert (op t a b) U := by
        obtain ⟨u, hu, h⟩ := hx; exact ⟨u, Or.inr hu, h⟩
      rcases ih _ hs' hne hx' with hd | ⟨k', hk', hd⟩
      · exact Or.inl (Der.step t a b hab.1 hab.2 hd)
      · refine Or.inr ⟨k' + 1, by rw [hk'], ?_⟩
        rw [Set.image_insert_eq, he] at hd
        exact Der.step t (e a) (e b) ⟨a, hab.1, rfl⟩ ⟨b, hab.2, rfl⟩ hd
    · have hc : e (op t a b) ∈ e '' U := by
        rw [he]
        by_cases hau : a ∈ U
        · have hbx : b = x := by
            rcases hs hb with h | h
            · exact h
            · exact absurd ⟨hau, h⟩ hab
          subst hbx
          rcases hr t (e a) with h | h
          · rw [h]; exact hx
          · rw [h]; exact im a ha
        · have hax : a = x := by
            rcases hs ha with h | h
            · exact h
            · exact absurd h hau
          subst hax
          rcases hl t (e b) with h | h
          · rw [h]; exact hx
          · rw [h]; exact im b hb
      refine Or.inr ⟨k, rfl, (h.map e he).mono ?_⟩
      rintro _ ⟨w, rfl | hw, rfl⟩
      · exact hc
      · exact im w hw

def opB (t : Fin 4) (a b : Bool) : Bool :=
  match t with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | 3 => b && !a

def opF {Ω : Type} (t : Fin 4) (f g : Ω → Bool) : Ω → Bool := fun x => opB t (f x) (g x)

def opN (t : Fin 4) (a b : ℕ) : ℕ :=
  match t with
  | 0 => Nat.land a b
  | 1 => Nat.lor a b
  | 2 => Nat.xor a (Nat.land a b)
  | 3 => Nat.xor b (Nat.land a b)

lemma land_bit (x y i : ℕ) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i

lemma lor_bit (x y i : ℕ) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

lemma xor_bit (x y i : ℕ) : (Nat.xor x y).testBit i = (x.testBit i != y.testBit i) := by
  simpa [bne] using Nat.testBit_xor x y i

lemma shr_bit (x s i : ℕ) : (Nat.shiftRight x s).testBit i = x.testBit (s + i) := by
  have := Nat.testBit_shiftRight (x := x) (i := s) (j := i)
  simpa using this

lemma opN_bit (t : Fin 4) (a b i : ℕ) :
    (opN t a b).testBit i = opB t (a.testBit i) (b.testBit i) := by
  fin_cases t <;> simp only [opN, opB, land_bit, lor_bit, xor_bit] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

lemma Der.agree {Ω : Type} {k : ℕ} {W : Set (Ω → Bool)} {y : Ω → Bool} (h : Der opF k W y)
    (p q : Ω) : (∀ w ∈ W, w p = w q) → y p = y q := by
  induction h with
  | here hy => intro hw; exact hw _ hy
  | weak _ ih => exact ih
  | step t a b ha hb _ ih =>
    intro hw
    refine ih ?_
    rintro w (rfl | hm)
    · simp only [opF, hw a ha, hw b hb]
    · exact hw w hm

structure St where
  t : Fin 4
  a : ℕ
  b : ℕ

def St.val (s : St) : ℕ := opN s.t s.a s.b

def Valid (y : ℕ) : Set ℕ → List St → Prop
  | W, [] => y ∈ W
  | W, s :: l => s.a ∈ W ∧ s.b ∈ W ∧ s.val ∉ W ∧ Valid y (insert s.val W) l

def need (y : ℕ) : List St → Finset ℕ
  | [] => {y}
  | s :: l => insert s.a (insert s.b ((need y l).erase s.val))

def Useful (y : ℕ) : List St → Prop
  | [] => True
  | s :: l => s.val ∈ need y l ∧ Useful y l

def killB (m : ℕ) (s : St) : Bool := Nat.beq (Nat.land s.a m) 0 || Nat.beq (Nat.land s.b m) 0

def kills (m : ℕ) (l : List St) : ℕ := l.countP (killB m)

def Chain : ℕ → List St → Prop
  | _, [] => True
  | p, s :: l => (s.a = p ∨ s.b = p ∨ p ≤ s.val) ∧ Chain s.val l

lemma valid_of_der {k : ℕ} {W : Set ℕ} {y : ℕ} (h : Der opN k W y) :
    ∃ l, l.length ≤ k ∧ Valid y W l := by
  induction h with
  | here hy => exact ⟨[], by simp, hy⟩
  | weak _ ih => obtain ⟨l, h1, h2⟩ := ih; exact ⟨l, by omega, h2⟩
  | @step k W y t a b ha hb _ ih =>
    obtain ⟨l, h1, h2⟩ := ih
    by_cases hc : opN t a b ∈ W
    · rw [Set.insert_eq_of_mem hc] at h2; exact ⟨l, by omega, h2⟩
    · exact ⟨⟨t, a, b⟩ :: l, by simp; omega, ha, hb, hc, h2⟩

lemma need_sub {y : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l → ∀ x ∈ need y l, x ∈ W := by
  induction l with
  | nil => intro W h x hx; rw [need, Finset.mem_singleton] at hx; rw [hx]; exact h
  | cons s l ih =>
    intro W h x hx
    obtain ⟨ha, hb, hc, hv⟩ := h
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with rfl | rfl | ⟨h1, h2⟩
    · exact ha
    · exact hb
    · exact (ih hv x h2).resolve_left h1

lemma valid_drop {y c : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y (insert c W) l →
    c ∉ need y l → Valid y W l := by
  induction l with
  | nil =>
    intro W h hc
    rw [need, Finset.mem_singleton] at hc
    exact h.resolve_left (fun e => hc e.symm)
  | cons s l ih =>
    intro W h hc
    obtain ⟨ha, hb, hf, hv⟩ := h
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hc
    push Not at hc
    obtain ⟨h1, h2, h3⟩ := hc
    have hne : c ≠ s.val := fun e => hf (Or.inl e.symm)
    refine ⟨ha.resolve_left (Ne.symm h1), hb.resolve_left (Ne.symm h2), fun h => hf (Or.inr h), ?_⟩
    rw [Set.insert_comm] at hv
    exact ih hv (h3 hne)

lemma useful_of_min {y : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l →
    (∀ l', Valid y W l' → l.length ≤ l'.length) → Useful y l := by
  induction l with
  | nil => intro W _ _; trivial
  | cons s l ih =>
    intro W h hmin
    obtain ⟨ha, hb, hf, hv⟩ := h
    refine ⟨?_, ih hv fun l' hl' => ?_⟩
    · by_contra hc
      have := hmin l (valid_drop l hv hc)
      simp at this
    · have := hmin (s :: l') ⟨ha, hb, hf, hl'⟩
      simpa using this

lemma need_card {y : ℕ} (l : List St) (h : Useful y l) : (need y l).card ≤ l.length + 1 := by
  induction l with
  | nil => simp [need]
  | cons s l ih =>
    obtain ⟨h1, h2⟩ := h
    have e := Finset.card_erase_of_mem h1
    have i := ih h2
    have c1 := Finset.card_insert_le s.a (insert s.b ((need y l).erase s.val))
    have c2 := Finset.card_insert_le s.b ((need y l).erase s.val)
    have p := Finset.card_pos.mpr ⟨_, h1⟩
    rw [need, List.length_cons]
    omega

lemma need_next {y : ℕ} {s : St} {l : List St} {x : ℕ} (h : x ∈ need y l) :
    x = s.val ∨ x ∈ need y (s :: l) := by
  by_cases hx : x = s.val
  · exact Or.inl hx
  · right; rw [need]; simp [hx, h]

lemma need_agree {y i j : ℕ} (l : List St) (h : ∀ x ∈ need y l, x.testBit i = x.testBit j) :
    y.testBit i = y.testBit j := by
  induction l with
  | nil => exact h y (by simp [need])
  | cons s l ih =>
    refine ih fun x hx => ?_
    rcases need_next (s := s) hx with rfl | hx
    · rw [St.val, opN_bit, opN_bit, h s.a (by simp [need]), h s.b (by simp [need])]
    · exact h x hx

lemma kill_forced {y m x : ℕ} (hy : Nat.land y m ≠ 0) (l : List St) (hx : x ∈ need y l)
    (hm : Nat.land x m = 0) : 1 ≤ kills m l := by
  induction l with
  | nil => rw [need, Finset.mem_singleton] at hx; rw [hx] at hm; exact absurd hm hy
  | cons s l ih =>
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    have hk : killB m s = true → 1 ≤ kills m (s :: l) := fun h => by
      rw [kills, List.countP_cons_of_pos h]; omega
    rcases hx with rfl | rfl | ⟨_, h2⟩
    · exact hk (by unfold killB; rw [hm]; rfl)
    · exact hk (by unfold killB; rw [hm]; exact Bool.or_true _)
    · have := ih h2
      have c : kills m l ≤ kills m (s :: l) := by
        rw [kills, kills, List.countP_cons]; omega
      omega

lemma land_op (t : Fin 4) (a b m : ℕ) :
    Nat.land (opN t a b) m = opN t (Nat.land a m) (Nat.land b m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [land_bit, opN_bit]
  fin_cases t <;> cases a.testBit i <;> cases b.testBit i <;> cases m.testBit i <;> rfl

lemma opN_zero_left (t : Fin 4) (b : ℕ) : opN t 0 b = 0 ∨ opN t 0 b = b := by
  have key (c : Bool → Bool) (h : ∀ i, (opN t 0 b).testBit i = c (b.testBit i))
      (hc : c = (fun _ => false) ∨ c = id) : opN t 0 b = 0 ∨ opN t 0 b = b := by
    rcases hc with rfl | rfl
    · left; apply Nat.eq_of_testBit_eq; intro i; rw [h]; simp
    · right; apply Nat.eq_of_testBit_eq; intro i; rw [h]; rfl
  fin_cases t
  · exact key _ (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)

def swapT : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2

lemma opN_swap (t : Fin 4) (a b : ℕ) : opN t a b = opN (swapT t) b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [opN_bit, opN_bit]
  fin_cases t <;> cases a.testBit i <;> cases b.testBit i <;> rfl

lemma opN_zero_right (t : Fin 4) (b : ℕ) : opN t b 0 = 0 ∨ opN t b 0 = b := by
  rw [opN_swap]; exact opN_zero_left _ _

lemma opN_self (t : Fin 4) (a : ℕ) : opN t a a = 0 ∨ opN t a a = a := by
  have key (c : Bool → Bool) (h : ∀ i, (opN t a a).testBit i = c (a.testBit i))
      (hc : c = (fun _ => false) ∨ c = id) : opN t a a = 0 ∨ opN t a a = a := by
    rcases hc with rfl | rfl
    · left; apply Nat.eq_of_testBit_eq; intro i; rw [h]; simp
    · right; apply Nat.eq_of_testBit_eq; intro i; rw [h]; rfl
  fin_cases t
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)

lemma der_masked {y m : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l → 0 ∈ W →
    ∃ n, n + kills m l = l.length ∧ Der opN n ((fun w => Nat.land w m) '' W) (Nat.land y m) := by
  induction l with
  | nil => intro W h _; exact ⟨0, by simp [kills], Der.here ⟨y, h, rfl⟩⟩
  | cons s l ih =>
    intro W h h0
    obtain ⟨ha, hb, _, hv⟩ := h
    obtain ⟨n, hn, hd⟩ := ih hv (Or.inr h0)
    have im (w : ℕ) (hw : w ∈ W) : Nat.land w m ∈ (fun w => Nat.land w m) '' W := ⟨w, hw, rfl⟩
    have z : 0 ∈ (fun w => Nat.land w m) '' W := ⟨0, h0, by simp [Nat.land]⟩
    by_cases hk : killB m s = true
    · refine ⟨n, ?_, hd.mono ?_⟩
      · rw [kills, List.countP_cons_of_pos hk, List.length_cons]
        rw [kills] at hn; omega
      · rintro _ ⟨w, rfl | hw, rfl⟩
        · show Nat.land s.val m ∈ _
          rw [St.val, land_op]
          rw [killB, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at hk
          rcases hk with h | h
          · rw [h]
            rcases opN_zero_left s.t (Nat.land s.b m) with e | e
            · rw [e]; exact z
            · rw [e]; exact im _ hb
          · rw [h]
            rcases opN_zero_right s.t (Nat.land s.a m) with e | e
            · rw [e]; exact z
            · rw [e]; exact im _ ha
        · exact im w hw
    · refine ⟨n + 1, ?_, ?_⟩
      · rw [kills, List.countP_cons_of_neg hk, List.length_cons]
        rw [kills] at hn; omega
      · refine Der.step s.t _ _ (im _ ha) (im _ hb) ?_
        rw [Set.image_insert_eq] at hd
        have e : Nat.land s.val m = opN s.t (Nat.land s.a m) (Nat.land s.b m) := land_op _ _ _ _
        rw [← e]; exact hd

lemma valid_swap {y : ℕ} (s1 s2 : St) (post : List St) (h1 : s2.a ≠ s1.val) (h2 : s2.b ≠ s1.val)
    (pre : List St) : ∀ {W : Set ℕ}, Valid y W (pre ++ s1 :: s2 :: post) →
      Valid y W (pre ++ s2 :: s1 :: post) := by
  induction pre with
  | nil =>
    intro W h
    obtain ⟨ha, hb, hc, ha2, hb2, hc2, hv⟩ := h
    refine ⟨ha2.resolve_left h1, hb2.resolve_left h2, fun h => hc2 (Or.inr h), Or.inr ha, Or.inr hb,
      ?_, ?_⟩
    · rintro (e | h)
      · exact hc2 (Or.inl e.symm)
      · exact hc h
    · rw [Set.insert_comm]; exact hv
  | cons s pre ih =>
    intro W h
    obtain ⟨ha, hb, hc, hv⟩ := h
    exact ⟨ha, hb, hc, ih hv⟩

def keyN (l : List St) : ℕ := l.foldl (fun acc s => 2 * acc + s.val) 0

lemma fold_lt (l : List St) : ∀ {x x' : ℕ}, x < x' →
    l.foldl (fun acc s => 2 * acc + s.val) x < l.foldl (fun acc s => 2 * acc + s.val) x' := by
  induction l with
  | nil => intro x x' h; exact h
  | cons s l ih =>
    intro x x' h
    exact ih (show 2 * x + s.val < 2 * x' + s.val by omega)

lemma key_swap (pre post : List St) (s1 s2 : St) (h : s2.val < s1.val) :
    keyN (pre ++ s2 :: s1 :: post) < keyN (pre ++ s1 :: s2 :: post) := by
  unfold keyN
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_cons,
    List.foldl_cons]
  exact fold_lt post (by omega)

lemma chain_of {l : List St} : ∀ (p : ℕ),
    (∀ s l', l = s :: l' → (s.a = p ∨ s.b = p ∨ p ≤ s.val)) →
    (∀ pre s1 s2 post, l = pre ++ s1 :: s2 :: post →
      (s2.a = s1.val ∨ s2.b = s1.val ∨ s1.val ≤ s2.val)) → Chain p l := by
  induction l with
  | nil => intro p _ _; trivial
  | cons s l ih =>
    intro p h1 h2
    refine ⟨h1 s l rfl, ih s.val (fun s' l' e => ?_) (fun pre s1 s2 post e => ?_)⟩
    · exact h2 [] s s' l' (by rw [e]; rfl)
    · exact h2 (s :: pre) s1 s2 post (by rw [e]; rfl)

lemma exists_min {α : Type} (S : Set α) (f : α → ℕ) (h : S.Nonempty) :
    ∃ l ∈ S, ∀ l' ∈ S, f l ≤ f l' := by
  obtain ⟨l, hl, hm⟩ := (measure f).wf.has_min S h
  exact ⟨l, hl, fun l' hl' => not_lt.mp (hm l' hl')⟩

def headV : List St → ℕ
  | [] => 0
  | s :: _ => s.val

lemma exists_sorted {y : ℕ} {W : Set ℕ} {k : ℕ} (h : Der opN k W y) :
    ∃ l, l.length ≤ k ∧ Valid y W l ∧ Useful y l ∧ Chain 0 l ∧
      ∀ l', Valid y W l' → l'.length = l.length → headV l ≤ headV l' := by
  obtain ⟨l0, hk0, hv0⟩ := valid_of_der h
  obtain ⟨l1, hv1, hmin⟩ := exists_min {l | Valid y W l} List.length ⟨l0, hv0⟩
  obtain ⟨l2, ⟨hv2, hlen2⟩, hhead⟩ :=
    exists_min {l | Valid y W l ∧ l.length = l1.length} headV ⟨l1, hv1, rfl⟩
  obtain ⟨l, ⟨hv, hlen, hh⟩, hkey⟩ :=
    exists_min {l | Valid y W l ∧ l.length = l1.length ∧ headV l = headV l2} keyN ⟨l2, hv2, hlen2, rfl⟩
  refine ⟨l, ?_, hv, useful_of_min l hv (fun l' hl' => by rw [hlen]; exact hmin l' hl'), ?_, ?_⟩
  · rw [hlen]; exact (hmin l0 hv0).trans hk0
  · refine chain_of 0 (fun s l' _ => Or.inr (Or.inr (Nat.zero_le _))) ?_
    intro pre s1 s2 post e
    by_contra hc
    push Not at hc
    obtain ⟨c1, c2, c3⟩ := hc
    rw [e] at hv hlen hh hkey
    have sv := valid_swap s1 s2 post c1 c2 pre hv
    have sl : (pre ++ s2 :: s1 :: post).length = l1.length := by
      rw [← hlen]; simp
    cases pre with
    | nil =>
      have := hhead _ ⟨sv, sl⟩
      rw [← hh] at this
      change s1.val ≤ s2.val at this
      omega
    | cons p pre =>
      have := hkey _ ⟨sv, sl, by rw [← hh]; rfl⟩
      have := key_swap (p :: pre) post s1 s2 c3
      omega
  · intro l' hl' hl
    rw [hh]; exact hhead l' ⟨hl', by rw [hl, hlen]⟩

lemma step_facts {y : ℕ} {W : Set ℕ} {s : St} {l : List St} (h : Valid y W (s :: l)) (h0 : 0 ∈ W) :
    s.a ≠ 0 ∧ s.b ≠ 0 ∧ s.a ≠ s.b ∧ s.val ≠ 0 ∧ s.val ≠ s.a ∧ s.val ≠ s.b ∧
      s.val ∉ need y (s :: l) := by
  have hn := need_sub (s :: l) h
  obtain ⟨ha, hb, hc, _⟩ := h
  refine ⟨?_, ?_, ?_, fun e => hc (e ▸ h0), fun e => hc (e ▸ ha), fun e => hc (e ▸ hb),
    fun hh => hc (hn _ hh)⟩
  · intro e
    rcases opN_zero_left s.t s.b with h | h
    · exact hc (by rw [St.val, e, h]; exact h0)
    · exact hc (by rw [St.val, e, h]; exact hb)
  · intro e
    rcases opN_zero_right s.t s.a with h | h
    · exact hc (by rw [St.val, e, h]; exact h0)
    · exact hc (by rw [St.val, e, h]; exact ha)
  · intro e
    rcases opN_self s.t s.a with h | h
    · exact hc (by rw [St.val, ← e, h]; exact h0)
    · exact hc (by rw [St.val, ← e, h]; exact ha)

structure Wr where
  w : ℕ
  s : ℕ
  f : ℕ

def sepN (L w : ℕ) : ℕ := Nat.land (Nat.xor w (Nat.shiftRight w 143)) L

def covL : List Wr → ℕ
  | [] => 0
  | a :: l => Nat.lor a.s (covL l)

def flL : List Wr → ℕ
  | [] => 0
  | a :: l => Nat.lor a.f (flL l)

def lenL : List Wr → ℕ
  | [] => 0
  | _ :: l => Nat.succ (lenL l)

def absentL (g : ℕ) : List Wr → Bool
  | [] => true
  | x :: l => cond (Nat.beq x.w g) false (absentL g l)

def app : List Wr → List Wr → List Wr
  | [], m => m
  | a :: l, m => a :: app l m

def sub (a b : ℕ) : Bool := Nat.beq (Nat.land a b) a

def force (x : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun n _ => f (Nat.succ n)) x

lemma force_eq (x : ℕ) (f : ℕ → Bool) : force x f = f x := by cases x <;> rfl

abbrev Next := List Wr → ℕ → ℕ → ℕ → ℕ → Bool

def tryG (L : ℕ) (r : Next) (k m : ℕ) (rest : List Wr) (cr c1 c2 c3 : ℕ) (a b : Wr) (last : ℕ)
    (uses : Bool) (g fg : ℕ) : Bool :=
  cond (Nat.beq g 0) false (cond (Nat.beq g a.w) false (cond (Nat.beq g b.w) false
    (cond (cond uses true (Nat.ble last g))
      (cond (sub fg c1)
        (force (sepN L g) fun sg =>
          force (Nat.lor cr sg) fun base =>
            (cond (Nat.beq base L) (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: rest) c1 c2 c3 g) false)
              false) ||
            (cond (Nat.ble m (Nat.succ k))
              ((cond (sub a.f c1) (cond (Nat.beq (Nat.lor base a.s) L)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: a :: rest) c1 c2 c3 g) false) false) false) ||
               (cond (sub b.f c1) (cond (Nat.beq (Nat.lor base b.s) L)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: b :: rest) c1 c2 c3 g) false) false) false) ||
               (cond (Nat.ble m k) (cond (sub a.f c1) (cond (sub b.f c1)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: a :: b :: rest) c1 c2 c3 g) false) false)
                  false) false))
              false))
        false)
      false)))

def plainP (L : ℕ) (r : Next) (k m c1 c2 c3 last : ℕ) (a b : Wr) (rest : List Wr) : Bool :=
  force (Nat.lor a.f b.f) fun K =>
    cond (sub K c1)
      (force (Nat.lor c2 (Nat.xor c1 (Nat.land c1 K))) fun d1 =>
       force (Nat.lor c3 (Nat.xor c2 (Nat.land c2 K))) fun d2 =>
       force (Nat.xor c3 (Nat.land c3 K)) fun d3 =>
        cond (sub (flL rest) d1)
          (force (covL rest) fun cr =>
            force (Nat.land a.w b.w) fun ab =>
              tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last) ab K ||
              (tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.lor a.w b.w) (Nat.land a.f b.f) ||
              (tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.xor a.w ab) a.f ||
              tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.xor b.w ab) b.f)))
          false)
      false

def ownSide (s other cr : ℕ) : ℕ :=
  Nat.xor s (Nat.land s (Nat.lor other cr))

def leftNeed (t : Fin 4) : Bool :=
  match t with
  | 0 => true
  | 1 => false
  | 2 => false
  | 3 => true

def rightNeed (t : Fin 4) : Bool :=
  match t with
  | 0 => true
  | 1 => false
  | 2 => true
  | 3 => false

def agreePart (want : Bool) (masked original : ℕ) :=
  if want then Nat.beq masked original else Nat.beq masked 0

def canUse (t : Fin 4) (loose : Bool) (ua ub pa pb : ℕ) :=
  loose || (agreePart (leftNeed t) pa ua && agreePart (rightNeed t) pb ub)

def withCheck (b : Bool) (act : Unit → Bool) := cond b (act ()) false


def tryP (L : ℕ) (r : Next) (k m c1 c2 c3 last : ℕ) (a b : Wr) (rest : List Wr) : Bool :=
  if Nat.ble m (Nat.succ k) then plainP L r k m c1 c2 c3 last a b rest else
  force (Nat.lor a.f b.f) fun K =>
    cond (sub K c1)
      (force (Nat.lor c2 (Nat.xor c1 (Nat.land c1 K))) fun d1 =>
       force (Nat.lor c3 (Nat.xor c2 (Nat.land c2 K))) fun d2 =>
       force (Nat.xor c3 (Nat.land c3 K)) fun d3 =>
        cond (sub (flL rest) d1)
          (force (covL rest) fun cr =>
            force (ownSide a.s b.s cr) fun ua =>
            force (ownSide b.s a.s cr) fun ub =>
            force (Nat.land ua b.w) fun pa =>
            force (Nat.land ub a.w) fun pb =>
            let ok (t : Fin 4) := canUse t (Nat.ble m (Nat.succ k)) ua ub pa pb
            let uses := Nat.beq a.w last || Nat.beq b.w last
            let go := tryG L r k m rest cr d1 d2 d3 a b last uses
            (withCheck (ok 0) fun _ => go (Nat.land a.w b.w) K) ||
            ((withCheck (ok 1) fun _ => go (Nat.lor a.w b.w) (Nat.land a.f b.f)) ||
            ((withCheck (ok 2) fun _ => go (Nat.xor a.w (Nat.land a.w b.w)) a.f) ||
             (withCheck (ok 3) fun _ => go (Nat.xor b.w (Nat.land a.w b.w)) b.f))))
          false)
      false

def pairsB (a : Wr) : List Wr → List Wr → List (Wr × Wr × List Wr)
  | _, [] => []
  | acc, b :: l => (a, b, app acc l) :: pairsB a (b :: acc) l

def pairsA : List Wr → List Wr → List (Wr × Wr × List Wr)
  | _, [] => []
  | acc, a :: l => pairsB a acc l ++ pairsA (a :: acc) l

def anyP (p : Wr → Wr → List Wr → Bool) : List (Wr × Wr × List Wr) → Bool
  | [] => false
  | x :: l => p x.1 x.2.1 x.2.2 || anyP p l

def isT (y : ℕ) : List Wr → Bool
  | [a] => Nat.beq a.w y
  | _ => false

def search (L y : ℕ) : ℕ → Next
  | 0, v, _, _, _, _ => isT y v
  | k + 1, v, c1, c2, c3, last =>
    isT y v || anyP (tryP L (search L y k) k (lenL v) c1 c2 c3 last) (pairsA [] v)

lemma lenL_eq (v : List Wr) : lenL v = v.length := by
  induction v with
  | nil => rfl
  | cons a l ih => rw [lenL, ih]; rfl

lemma app_eq (a b : List Wr) : app a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x l ih => rw [app, ih]; rfl

lemma absent_true {g : ℕ} {l : List Wr} (h : ∀ x ∈ l, x.w ≠ g) : absentL g l = true := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : Nat.beq x.w g = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]; exact h x (by simp)
    rw [absentL, hx]
    exact ih fun u hu => h u (by simp [hu])

lemma sub_true {a b : ℕ} (h : ∀ i, a.testBit i = true → b.testBit i = true) : sub a b = true := by
  rw [sub, Nat.beq_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [land_bit]
  cases ha : a.testBit i
  · rfl
  · rw [h i ha]; rfl

lemma anyP_true {p : Wr → Wr → List Wr → Bool} {l : List (Wr × Wr × List Wr)} {a b : Wr}
    {r : List Wr} (hm : (a, b, r) ∈ l) (hp : p a b r = true) : anyP p l = true := by
  induction l with
  | nil => simp at hm
  | cons x l ih =>
    rw [anyP, Bool.or_eq_true]
    rcases List.mem_cons.mp hm with rfl | h
    · exact Or.inl hp
    · exact Or.inr (ih h)

lemma pairsB_spec (a b : Wr) (l : List Wr) : ∀ acc : List Wr, b ∈ l →
    ∃ r, (a, b, r) ∈ pairsB a acc l ∧ (acc ++ l).Perm (b :: r) := by
  induction l with
  | nil => intro acc h; simp at h
  | cons x l ih =>
    intro acc h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨acc ++ l, by simp [pairsB, app_eq], List.perm_middle⟩
    · obtain ⟨r, h1, h2⟩ := ih (x :: acc) h
      exact ⟨r, by simp [pairsB, h1], List.perm_middle.trans h2⟩

lemma pairsA_spec (a b : Wr) (hab : a ≠ b) (l : List Wr) : ∀ acc : List Wr, a ∈ l → b ∈ l →
    ∃ r, ((a, b, r) ∈ pairsA acc l ∨ (b, a, r) ∈ pairsA acc l) ∧ (acc ++ l).Perm (a :: b :: r) := by
  induction l with
  | nil => intro acc h; simp at h
  | cons x l ih =>
    intro acc ha hb
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with e | hb'
      · exact absurd e.symm hab
      · obtain ⟨r, h1, h2⟩ := pairsB_spec a b l acc hb'
        exact ⟨r, Or.inl (by rw [pairsA]; exact List.mem_append_left _ h1),
          List.perm_middle.trans (h2.cons a)⟩
    · rcases List.mem_cons.mp hb with rfl | hb'
      · obtain ⟨r, h1, h2⟩ := pairsB_spec b a l acc ha'
        exact ⟨r, Or.inr (by rw [pairsA]; exact List.mem_append_left _ h1),
          (List.perm_middle.trans (h2.cons b)).trans (List.Perm.swap a b r)⟩
      · obtain ⟨r, h1, h2⟩ := ih (x :: acc) ha' hb'
        refine ⟨r, ?_, List.perm_middle.trans h2⟩
        rcases h1 with h | h
        · exact Or.inl (by rw [pairsA]; exact List.mem_append_right _ h)
        · exact Or.inr (by rw [pairsA]; exact List.mem_append_right _ h)

structure Rep (L H : ℕ) (mask : ℕ → ℕ) (v : List Wr) (S : Finset ℕ) : Prop where
  nd : (v.map Wr.w).Nodup
  mem : ∀ x, x ∈ S ↔ ∃ u ∈ v, u.w = x
  sep : ∀ u ∈ v, u.s = sepN L u.w
  fl : ∀ u ∈ v, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0

def Bud (H : ℕ) (mask : ℕ → ℕ) (c1 c2 c3 : ℕ) (l : List St) : Prop :=
  ∀ h < H, kills (mask h) l ≤ 3 ∧ (1 ≤ kills (mask h) l → c1.testBit h = true) ∧
    (2 ≤ kills (mask h) l → c2.testBit h = true) ∧ (3 ≤ kills (mask h) l → c3.testBit h = true)

lemma cov_bit (l : List Wr) (i : ℕ) : (covL l).testBit i = l.any fun a => a.s.testBit i := by
  induction l with
  | nil => simp [covL]
  | cons a l ih => rw [covL, lor_bit, ih, List.any_cons]

lemma fl_bit (l : List Wr) (i : ℕ) : (flL l).testBit i = l.any fun a => a.f.testBit i := by
  induction l with
  | nil => simp [flL]
  | cons a l ih => rw [flL, lor_bit, ih, List.any_cons]

lemma sepN_bit (L w i : ℕ) :
    (sepN L w).testBit i = ((w.testBit i != w.testBit (143 + i)) && L.testBit i) := by
  rw [sepN, land_bit, xor_bit, shr_bit]

private theorem agreePart_true {bound w : ℕ} {want : Bool}
    (hits : ∀ i, bound.testBit i=true → w.testBit i=want) :
    agreePart want (Nat.land bound w) bound=true := by
  cases want with
  | false =>
    apply Nat.beq_eq.mpr
    apply Nat.eq_of_testBit_eq
    intro i
    cases hb : bound.testBit i with
    | false => simp [land_bit,hb]
    | true => simp [land_bit,hb,hits i hb]
  | true =>
    apply Nat.beq_eq.mpr
    apply Nat.eq_of_testBit_eq
    intro i
    cases hb : bound.testBit i with
    | false => simp [land_bit,hb]
    | true => simp [land_bit,hb,hits i hb]

private theorem pair_bit_table : ∀ (t : Fin 4) (l c a x b y : Bool),
    (c || ((opB t a b != opB t x y) && l))=l →
    ((((a != x) && l) != (((a != x) && l) && (((b != y) && l) || c)))=true → b=leftNeed t) ∧
    ((((b != y) && l) != (((b != y) && l) && (((a != x) && l) || c)))=true → a=rightNeed t) := by
  decide +kernel

private theorem pair_test_true {L cr : ℕ} {a b : Wr} {t : Fin 4}
    (ha : a.s=sepN L a.w) (hb : b.s=sepN L b.w)
    (covers : Nat.lor cr (sepN L (opN t a.w b.w))=L) :
    canUse t false (ownSide a.s b.s cr) (ownSide b.s a.s cr)
      (Nat.land (ownSide a.s b.s cr) b.w) (Nat.land (ownSide b.s a.s cr) a.w)=true := by
  have atRow (i : Nat) := congrArg (fun n : Nat => n.testBit i) covers
  have row (i : Nat) :
      (cr.testBit i || ((opB t (a.w.testBit i) (b.w.testBit i) !=
        opB t (a.w.testBit (143+i)) (b.w.testBit (143+i))) && L.testBit i))=L.testBit i := by
    simpa only [lor_bit,sepN_bit,opN_bit] using atRow i
  unfold canUse
  rw [Bool.false_or,Bool.and_eq_true]
  constructor
  · apply agreePart_true
    intro i hi
    apply (pair_bit_table t _ _ _ _ _ _ (row i)).1
      (by simpa only [ownSide,xor_bit,land_bit,lor_bit,ha,hb,sepN_bit] using hi)
  · apply agreePart_true
    intro i hi
    apply (pair_bit_table t _ _ _ _ _ _ (row i)).2
      (by simpa only [ownSide,xor_bit,land_bit,lor_bit,ha,hb,sepN_bit] using hi)

private theorem no_dropped_gate (L : ℕ) (r : Next) (k m : ℕ) (rest : List Wr)
    (cr c1 c2 c3 : ℕ) (a b : Wr) (last : ℕ) (uses : Bool) (g fg : ℕ)
    (tight : Nat.ble m (Nat.succ k)=false) (bad : Nat.lor cr (sepN L g)≠L) :
    tryG L r k m rest cr c1 c2 c3 a b last uses g fg=false := by
  have e : Nat.beq (Nat.lor cr (sepN L g)) L=false := by
    cases h : Nat.beq (Nat.lor cr (sepN L g)) L with
    | false => rfl
    | true => exact (bad (Nat.beq_eq.mp h)).elim
  simp [tryG,force_eq,tight,e]

private theorem guard_sound {L k m cr c1 c2 c3 last fg : ℕ} {rest : List Wr}
    {r : Next} {a b : Wr} {uses : Bool} (t : Fin 4)
    (ha : a.s=sepN L a.w) (hb : b.s=sepN L b.w) :
    withCheck (canUse t (Nat.ble m (Nat.succ k)) (ownSide a.s b.s cr) (ownSide b.s a.s cr)
      (Nat.land (ownSide a.s b.s cr) b.w) (Nat.land (ownSide b.s a.s cr) a.w))
      (fun _ => tryG L r k m rest cr c1 c2 c3 a b last uses (opN t a.w b.w) fg) =
      tryG L r k m rest cr c1 c2 c3 a b last uses (opN t a.w b.w) fg := by
  cases loose : Nat.ble m (Nat.succ k) with
  | true => simp [canUse,withCheck]
  | false =>
    by_cases hit : Nat.lor cr (sepN L (opN t a.w b.w))=L
    · rw [pair_test_true ha hb hit]
      rfl
    · rw [no_dropped_gate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ loose hit]
      simp [withCheck]

private theorem tryP_eq_plain {L : ℕ} {a b : Wr} (r : Next) (k m c1 c2 c3 last : ℕ)
    (rest : List Wr) (ha : a.s=sepN L a.w) (hb : b.s=sepN L b.w) :
    tryP L r k m c1 c2 c3 last a b rest=plainP L r k m c1 c2 c3 last a b rest := by
  unfold tryP
  split
  · rfl
  · unfold plainP
    simp only [force_eq]
    rw [guard_sound 0 ha hb,guard_sound 1 ha hb,guard_sound 2 ha hb,guard_sound 3 ha hb]


end CoTheta3174Public
