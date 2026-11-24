import PEqualNP.CoPetersenRestrictScan

namespace PEqualNP.Research.PetersenRestrict

open PEqualNP.CircuitLowerBounds

/-- Original, effective pin indices. In particular NOT's optional second pin is excluded. -/
def pins (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

private theorem map_pins (g : Gate) (refs : List Wire) :
    (pins g).map (resolve refs) = effective g.op (g.inputs.map (resolve refs)) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> cases ins <;> rfl

theorem simplify_fixed_port (g : Gate) (refs : List Wire) (i : ℕ) (b : Bool)
    (hr : resolve refs i = .fixed b) (hi : i ∈ pins g) :
    (simplify refs g).cost = 0 := by
  apply simplify_fixed refs g b
  rw [← map_pins]
  exact List.mem_map.mpr ⟨i, hi, hr⟩

/-- All named indices already exist at this prefix and are represented by constants.
Existence at the prefix prevents mistaking a future wire for a permanently fixed false pin. -/
def Ready (s : Finset ℕ) (refs : List Wire) : Prop :=
  ∀ i ∈ s, i < refs.length ∧ ∃ b, resolve refs i = .fixed b

private theorem ready_append {s : Finset ℕ} {refs : List Wire} (hr : Ready s refs) (w : Wire) :
    Ready s (refs ++ [w]) := by
  intro i hi
  obtain ⟨hlt, b, hb⟩ := hr i hi
  refine ⟨?_, b, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · simpa only [resolve, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] using hb

/-- Count each subsequent gate once, even when both of its input pins are already fixed. -/
def directSavings (s : Finset ℕ) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
    if (pins g).toFinset ∩ s = ∅ then directSavings s gs else directSavings s gs + 1

theorem scan_direct (s : Finset ℕ) : ∀ (gs : List Gate) (n : ℕ) (refs : List Wire),
    Ready s refs → directSavings s gs ≤ saved (scan gs n refs).trace := by
  intro gs
  induction gs with
  | nil => intros; exact Nat.le_refl 0
  | cons g gs ih =>
    intro n refs hr
    cases hp : simplify refs g with
    | reuse w =>
      have hh := ih n (refs ++ [cap n w]) (ready_append hr _)
      by_cases he : (pins g).toFinset ∩ s = ∅
      · simp only [scan, hp, directSavings, he, ite_true, saved]
        omega
      · simpa only [scan, hp, directSavings, he, if_false, saved] using Nat.add_le_add_right hh 1
    | emit a =>
      have he : (pins g).toFinset ∩ s = ∅ := by
        by_contra hn
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hn
        obtain ⟨hpin, hfixed⟩ := Finset.mem_inter.mp hi
        obtain ⟨_, b, hb⟩ := hr i hfixed
        have hc := simplify_fixed_port g refs i b hb (List.mem_toFinset.mp hpin)
        rw [hp] at hc
        cases hc
      have hh := ih (n+1) (refs ++ [.port n]) (ready_append hr _)
      simpa only [scan, hp, directSavings, he, if_true, saved] using hh

/-- A prescribed, ordered list of zero-gate actions in the trace gives a lower bound
regardless of arbitrary intervening uses or additional eliminations. -/
theorem saved_sublist {as bs : List Plan} (h : as.Sublist bs) : saved as ≤ saved bs := by
  induction h with
  | slnil => exact Nat.le_refl 0
  | cons x h ih =>
    cases x with
    | reuse w => exact Nat.le.step ih
    | emit g => exact ih
  | cons_cons x h ih =>
    cases x with
    | reuse w => exact Nat.add_le_add_right ih 1
    | emit g => exact ih

theorem charge_reuses {ps : List Plan} (ws : List Wire) (hs : (ws.map Plan.reuse).Sublist ps) :
    ws.length ≤ saved ps := by
  have hn : saved (ws.map Plan.reuse) = ws.length := by
    clear hs
    induction ws with
    | nil => rfl
    | cons w ws ih => simp only [List.map_cons, saved, List.length_cons, ih]
  rw [← hn]
  exact saved_sublist hs

end PEqualNP.Research.PetersenRestrict
