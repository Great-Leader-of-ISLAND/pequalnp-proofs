import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1631

open PEqualNP.CircuitLowerBounds

-- The fold comparison follows the accepted monotone wire lemma in L-meta-1018.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


end PEqualNP.Outside.L_meta_1631

open PEqualNP.Outside.L_meta_1631

theorem PEqualNP.Outside.L_meta_1631 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o : Fin N → ℕ, ((∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true)) ↔
    ∀ t : Fin N, ev (o t) (fun v : Fin N => decide (v ∉ L t)) = false ∧ (p0 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p0)) = true) ∧ (p1 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p1)) = true) ∧
      (∀ p ∈ L t, ev (o t) (fun v : Fin N => decide (v = p0 ∨ v = p)) = true ∧ ev (o t) (fun v : Fin N => decide (v = p1 ∨ v = p)) = true) ∧ (t ≠ i0 → ev (o t) (fun v : Fin N => decide (v ∉ L i0)) = true) ∧
      (∀ w ∈ L t ∩ L i0, w ≠ p0 → w ≠ p1 → ev (o t) (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)) = true)) := by
  classical
  intro q N L i0 p0 p1 hq hN hcard hinter hpairs hne hp0 hp1 gates gops gpos gback ev hev o
  have mono (w : ℕ) (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) :
      ev w x = true → ev w y = true := by
    rw [hev w x, hev w y]
    apply wiresFrom_mono gates (fun g h => (gops g h).1) (List.ofFn x) (List.ofFn y) (by simp) _ w
    intro k hk
    by_cases h : k < N
    · rw [List.getD_eq_getElem _ _ (by simpa using h)] at hk
      rw [List.getD_eq_getElem _ _ (by simpa using h)]
      simp only [List.getElem_ofFn] at hk ⊢
      exact hxy _ hk
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
      exact Bool.noConfusion hk
  have coF (t : Fin N) : p0 ∉ L t ∨ p1 ∉ L t ∨ ∀ u, u ∉ L i0 → u ∉ L t := by
    by_cases ht : t = i0
    · subst t
      exact Or.inr (Or.inr (fun _ h => h))
    by_cases ha : p0 ∈ L t
    · right
      left
      intro hb
      exact hne (Finset.card_le_one.mp (hinter t i0 ht).le p0 (Finset.mem_inter.mpr ⟨ha,hp0⟩)
        p1 (Finset.mem_inter.mpr ⟨hb,hp1⟩))
    · exact Or.inl ha
  have outside (t : Fin N) (ht : t ≠ i0) : ∃ p ∈ L t, p ∉ L i0 := by
    by_contra hn
    have hs : L t ⊆ L i0 := by
      intro p hp
      by_contra hf
      exact hn ⟨p,hp,hf⟩
    have hh := hinter t i0 ht
    rw [Finset.inter_eq_left.mpr hs, hcard t] at hh
    omega
  constructor
  · intro agree t
    have yes (x : Fin N → Bool)
        (care : x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true)
        (p : Fin N) (hp : p ∈ L t) (on : x p = true) : ev (o t) x = true := by
      rw [agree t x care]
      have hit : ∃ v ∈ L t, x v = true := ⟨p, hp, on⟩
      simp [hit]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have care : decide (p0 ∉ L t) = true ∨ decide (p1 ∉ L t) = true ∨
          ∀ u : Fin N, u ∉ L i0 → decide (u ∉ L t) = true := by
        rcases coF t with h | h | h
        · exact Or.inl (by simp [h])
        · exact Or.inr (Or.inl (by simp [h]))
        · exact Or.inr (Or.inr (fun u hu => by simp [h u hu]))
      rw [agree t (fun v => decide (v ∉ L t)) care]
      have miss : ¬ ∃ v ∈ L t, decide (v ∉ L t) = true := by
        rintro ⟨v, hv, h⟩
        simpa [hv] using h
      simp [miss]
    · intro hp
      exact yes (fun v => decide (v = p0)) (Or.inl (by simp)) p0 hp (by simp)
    · intro hp
      exact yes (fun v => decide (v = p1)) (Or.inr (Or.inl (by simp))) p1 hp (by simp)
    · intro p hp
      exact ⟨yes (fun v => decide (v = p0 ∨ v = p)) (Or.inl (by simp)) p hp (by simp),
        yes (fun v => decide (v = p1 ∨ v = p)) (Or.inr (Or.inl (by simp))) p hp (by simp)⟩
    · intro ht
      obtain ⟨p, hp, hout⟩ := outside t ht
      exact yes (fun v => decide (v ∉ L i0))
        (Or.inr (Or.inr (fun u hu => by simp [hu]))) p hp (by simp [hout])
    · intro w hw _ _
      exact yes (fun v => decide (v ∉ L i0 ∨ v = w))
        (Or.inr (Or.inr (fun u hu => by simp [hu]))) w (Finset.mem_inter.mp hw).1 (by simp)
  · intro tests t x hf
    classical
    obtain ⟨hneg, hs0, hs1, hpair, hoff, hboth⟩ := tests t
    by_cases hx : ∃ p ∈ L t, x p = true
    · simp only [hx, decide_true]
      obtain ⟨p, hp, xp⟩ := hx
      rcases hf with x0 | x1 | xoff
      · apply mono (o t) (fun v : Fin N => decide (v = p0 ∨ v = p)) x ?_ (hpair p hp).1
        intro v hv
        obtain h | h := (of_decide_eq_true hv : v = p0 ∨ v = p)
        · simpa only [h] using x0
        · simpa only [h] using xp
      · apply mono (o t) (fun v : Fin N => decide (v = p1 ∨ v = p)) x ?_ (hpair p hp).2
        intro v hv
        obtain h | h := (of_decide_eq_true hv : v = p1 ∨ v = p)
        · simpa only [h] using x1
        · simpa only [h] using xp
      · by_cases ht : t = i0
        · subst t
          by_cases h0 : p = p0
          · subst p
            apply mono (o i0) (fun v : Fin N => decide (v = p0)) x ?_ (hs0 hp)
            intro v hv
            simpa only [(of_decide_eq_true hv : v = p0)] using xp
          · by_cases h1 : p = p1
            · subst p
              apply mono (o i0) (fun v : Fin N => decide (v = p1)) x ?_ (hs1 hp)
              intro v hv
              simpa only [(of_decide_eq_true hv : v = p1)] using xp
            · apply mono (o i0) (fun v : Fin N => decide (v ∉ L i0 ∨ v = p)) x ?_
                (hboth p (Finset.mem_inter.mpr ⟨hp, hp⟩) h0 h1)
              intro v hv
              obtain hv' | hv' := (of_decide_eq_true hv : v ∉ L i0 ∨ v = p)
              · exact xoff v hv'
              · simpa only [hv'] using xp
        · apply mono (o t) (fun v : Fin N => decide (v ∉ L i0)) x ?_ (hoff ht)
          intro v hv
          exact xoff v (of_decide_eq_true hv)
    · have hfalse : ev (o t) x = false := by
        cases he : ev (o t) x with
        | false => rfl
        | true =>
          have hle : ∀ v : Fin N, x v = true → decide (v ∉ L t) = true := by
            intro v hv
            apply decide_eq_true
            intro hmem
            exact hx ⟨v, hmem, hv⟩
          have h := mono (o t) x (fun v : Fin N => decide (v ∉ L t)) hle he
          simp only [hneg, Bool.false_eq_true] at h
      simpa only [hx, decide_false] using hfalse
