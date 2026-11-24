import PEqualNP.Outside.L_meta_1737

-- The elimination and renaming proofs below specialize the checked work in L-meta-1737.
-- The new invariant retains the AND/OR basis at every emitted gate.
namespace CoMonoRestriction2585

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1737

def MonoGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def HasMonoSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x

theorem monoGate_ok {g : Gate} (h : MonoGate g) : Ok g := by
  obtain ⟨hop,len⟩ := h
  exact ⟨hop.elim Or.inl (fun e => Or.inr (Or.inl e)),len⟩

theorem mono_norm {g : Gate} (h : MonoGate g) : normGate g=g := by
  obtain ⟨op,ins⟩ := g
  rcases h.1 with left|right
  · change op=GateOp.and at left
    subst op
    rfl
  · change op=GateOp.or at right
    subst op
    rfl

theorem simplify_mono (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op=GateOp.and ∨ op=GateOp.or) : ∀ g∈(simplify op m ins).1, MonoGate g := by
  intro g hg
  rcases hop with rfl|rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify,simpAnd] at hg <;> (subst hg; simp [MonoGate])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify,simpOr] at hg <;> (subst hg; simp [MonoGate])

theorem elim_mono (n : ℕ) (gs : List Gate) (old : ∀ g∈gs, MonoGate g) :
    ∀ acc : List Stat × List Gate, (∀ g∈acc.2, MonoGate g) → ∀ g∈(elim n gs acc).2, MonoGate g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (fun a ha => old a (List.mem_cons_of_mem _ ha)) (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1|h1
    · exact h g' h1
    · exact simplify_mono _ _ _ (old g List.mem_cons_self).1 g' (by simpa using h1)


theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasMonoSize (n + 1) f (s + 1)) :
    HasMonoSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have monoGS : ∀ g∈gs, MonoGate g := by
    intro g hg
    obtain ⟨g0,hg0,rfl⟩ := List.mem_map.1 hg
    rw [mono_norm (ok g0 hg0)]
    exact ok g0 hg0
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (monoGate_ok (ok g0 hg0))
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Sum.inl false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_mono n gs monoGS _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasMonoSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasMonoSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have monoGS : ∀ g∈gs, MonoGate g := by
    intro g hg
    obtain ⟨g0,hg0,rfl⟩ := List.mem_map.1 hg
    rw [mono_norm (ok g0 hg0)]
    exact ok g0 hg0
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (monoGate_ok (ok g0 hg0))
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_mono n gs monoGS _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasMonoSize n h s) : HasMonoSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasMonoSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasMonoSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasMonoSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasMonoSize (n + 1) f (s + 1)) :
    HasMonoSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasMonoSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := CoMonoRestriction2585.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end CoMonoRestriction2585


namespace CoMonoPendantStar

open PEqualNP.MetaComplexity
open CoMonoRestriction2585 (HasMonoSize gate_elim_at one_gate_at)

def star {n : ℕ} (f : (Fin n → Bool) → Bool) (v u w : Fin n) (x : Fin n → Bool) : Bool :=
  f x || (x u && (x v || x w))

def half {n : ℕ} (f : (Fin n → Bool) → Bool) (v u : Fin n) (b : Bool) (x : Fin n → Bool) : Bool :=
  f x || (x u && (x v || b))

theorem arm_lower {n k s : ℕ} {f : (Fin (n+1) → Bool) → Bool}
    (v u w : Fin (n+1)) (vu : v≠u) (vw : v≠w) (uw : u≠w)
    (oldU : ∀ x b, f (Function.update x u b) = f x)
    (oldW : ∀ x b, f (Function.update x w b) = f x)
    (empty : f (fun _ => false) = false)
    (single : f (Function.update (fun _ => false) v true) = false)
    (nc : ∃ x y, f x ≠ f y)
    (positive : 0 < k) (lower : ∀ size, HasMonoSize (n+1) f size → k ≤ size)
    (original : HasMonoSize (n+1) (star f v u w) s) : k + 3 ≤ s := by
  classical
  have wfix (b : Bool) (x : Fin (n+1) → Bool) :
      star f v u w (Function.update x w b) = half f v u b x := by
    simp [star,half,oldW,Function.update_of_ne uw,Function.update_of_ne vw]
  have uoff (b : Bool) (x : Fin (n+1) → Bool) :
      half f v u b (Function.update x u false) = f x := by
    simp [half,oldU]
  have depW : ∃ x, star f v u w (Function.update x w (!x w)) ≠ star f v u w x := by
    refine ⟨Function.update (fun _ => false) u true,?_⟩
    simp [star,oldU,oldW,empty,Function.update_of_ne vu,Function.update_of_ne vw,Function.update_of_ne uw,Function.update_of_ne uw.symm]
  have activeW (b : Bool) : ∃ x y, star f v u w (Function.update x w b) ≠
      star f v u w (Function.update y w b) := by
    obtain ⟨x,y,ne⟩ := nc
    exact ⟨Function.update x u false,Function.update y u false,by simpa only [wfix,uoff] using ne⟩
  obtain ⟨b,t,budget,circuit⟩ := gate_elim_at n (star f v u w) w s depW activeW original
  have eqW : (fun x => star f v u w (Function.update x w b))=half f v u b := funext (wfix b)
  rw [eqW] at circuit
  have depU : ∃ x, half f v u b (Function.update x u (!x u)) ≠ half f v u b x := by
    refine ⟨Function.update (fun _ => false) v true,?_⟩
    simp [half,oldU,single,Function.update_of_ne vu,Function.update_of_ne vu.symm]
  have actU : ∃ x y, half f v u b (Function.update x u false) ≠
      half f v u b (Function.update y u false) := by
    obtain ⟨x,y,ne⟩ := nc
    exact ⟨x,y,by simpa only [uoff] using ne⟩
  have eqU : (fun x => half f v u b (Function.update x u false))=f := funext (uoff b)
  cases t with
  | zero =>
    obtain ⟨C,ok,le,ev⟩ := circuit
    have larger : HasMonoSize (n+1) (half f v u b) (0+1) := ⟨C,ok,by omega,ev⟩
    have reduced := one_gate_at n (half f v u b) u false 0 depU actU larger
    rw [eqU] at reduced
    have := lower 0 reduced
    omega
  | succ j =>
    have reduced := one_gate_at n (half f v u b) u false j depU actU circuit
    rw [eqU] at reduced
    have := lower j reduced
    omega

end CoMonoPendantStar
