import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1632

open PEqualNP.CircuitLowerBounds

open PEqualNP.CircuitLowerBounds

private def appendValue1632 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem inputFold1632 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl appendValue1632 w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (appendValue1632 w g).length := by
      simp only [appendValue1632, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (appendValue1632 w g) hlt]
    simp only [appendValue1632, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem inputEval1632 {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    Circuit.eval ⟨gs, p.val⟩ (List.ofFn x) = x p := by
  change (gs.foldl appendValue1632 (List.ofFn x)).getD p.val false = x p
  rw [inputFold1632 gs (List.ofFn x) p.val (by simpa only [List.length_ofFn] using p.isLt)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, p.isLt, ↓reduceDIte, Option.getD_some]

end PEqualNP.Outside.L_meta_1632

open PEqualNP.Outside.L_meta_1632

theorem PEqualNP.Outside.L_meta_1632 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    (∀ l l' : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p0 ∈ L l' ∧ p1 ∉ L l') → l ≠ l' → ∀ p ∈ L l, p ≠ p0 → p1 ∉ L l' ∧ p ∉ L l') ∧
    (∀ m m' : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p1 ∈ L m' ∧ p0 ∉ L m') → m ≠ m' → ∀ p ∈ L m, p ≠ p1 → p0 ∉ L m' ∧ p ∉ L m') ∧
    (∀ m : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → p0 ∉ L m) ∧ (∀ l : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → p1 ∉ L l) ∧
    (∀ M m : Fin N, (p0 ∉ L M ∧ p1 ∉ L M) → (p1 ∈ L m ∧ p0 ∉ L m) → ∀ p ∈ L M, p ∉ L m → p0 ∉ L m ∧ p ∉ L m) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ∃ c : Fin N, L l ∩ L m = {c}) ∧
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      ∀ p t : Fin N, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (p : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = false ↔ p ∈ L t) := by
  classical
  intro q N L i0 p0 p1 hq hN hcard hinter hpairs hne hp0 hp1
  have uniquePoint (a b : Fin N) (hd : a ≠ b) (u v : Fin N)
      (ua : u ∈ L a) (ub : u ∈ L b) (va : v ∈ L a) (vb : v ∈ L b) : u = v :=
    Finset.card_le_one.mp (hinter a b hd).le u (Finset.mem_inter.mpr ⟨ua,ub⟩)
      v (Finset.mem_inter.mpr ⟨va,vb⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' hl hl' hd p hp hn
    exact ⟨hl'.2, fun hp' => hn (uniquePoint l l' hd p p0 hp hp' hl.1 hl'.1)⟩
  · intro m m' hm hm' hd p hp hn
    exact ⟨hm'.2, fun hp' => hn (uniquePoint m m' hd p p1 hp hp' hm.1 hm'.1)⟩
  · intro m hm
    exact hm.2
  · intro l hl
    exact hl.2
  · intro M m hM hm p hp hpm
    exact ⟨hm.2,hpm⟩
  · intro l m hl hm
    have hd : l ≠ m := fun h => hm.2 (h ▸ hl.1)
    exact Finset.card_eq_one.mp (hinter l m hd)
  · intro gates _ _ _ p t
    rw [inputEval1632]
    simp
