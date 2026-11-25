import PEqualNP.CoCommute1675
import PEqualNP.CoAllPorts4482

namespace Co5056Frozen
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoCommute1675 CoPortRoots4482

def FrozenFive : Prop :=
  ∀ gs : List Gate, gs.length ≤ 7 →
    (∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) →
    ∀ O : Finset Nat, O.card ≤ 5 →
      ∃ x y : Fin 9 → Bool, graph x ≠ graph y ∧ (x 0 || x 2) = (y 0 || y 2) ∧
        ∀ i ∈ O, ((circuit gs).wires (List.ofFn x)).getD i false =
          ((circuit gs).wires (List.ofFn y)).getD i false

private theorem firstValue (a : Gate) (gs : List Gate) (out : Nat) (x : Fin 9 → Bool) :
    ((Circuit.mk (a::gs) out).wires (List.ofFn x)).getD 9 false =
      a.op.eval (a.inputs.map (fun i => (List.ofFn x).getD i false)) := by
  change (gs.foldl step (step (List.ofFn x) a)).getD 9 false = _
  rw [read_kept gs _ _ (by simp [step])]
  simp [step, read_snoc]

private theorem canonical (a : Gate) (gs : List Gate) (out : Nat) (x : Fin 9 → Bool)
    (fixed : ((Circuit.mk (a::gs) out).wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) :
    (Circuit.mk (a::gs) out).wires (List.ofFn x) = (circuit gs).wires (List.ofFn x) := by
  rw [firstValue] at fixed
  change gs.foldl step (step (List.ofFn x) a) = gs.foldl step (step (List.ofFn x) head)
  exact congrArg (gs.foldl step) (by simp [step,head,GateOp.eval,List.getD_eq_getElem?_getD,fixed])

theorem of_frozen (frozen : FrozenFive) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size = (8 : ℕ) →       (∀ x4 ∈ x1.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →         (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) →           have x6 : ℕ → ℕ → Prop := fun (x6 x7 : ℕ) => Relation.ReflTransGen (fun (x8 x9 : ℕ) => (10 : ℕ) ≤ x9 ∧ x9 < (17 : ℕ) ∧ x8 < x9 ∧ x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x9 - (9 : ℕ))).inputs) x6 x7;           have x7 : (Fin (9 : ℕ) → Bool) → Bool := fun (x7 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (9 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (9 : ℕ) (x8 % (10 : ℕ)));           ∀ x8 ⊆ Finset.range (17 : ℕ), x8.card = (6 : ℕ) → (9 : ℕ) ∈ x8 → ¬((0 : ℕ) ∈ x8 ∧ (2 : ℕ) ∈ x8) → (∀ x13 < (9 : ℕ), ∃ x15 ∈ x8, x6 x13 x15) → (∃ (x14 : Finset ℕ), (4 : ℕ) ≤ x14.card ∧ ∀ x15 ∈ x14, (10 : ℕ) ≤ x15 ∧ x15 < (17 : ℕ) ∧ ∃ x17 ∈ x8, x6 x15 x17) → ∃ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ) → Bool), x7 x15 ≠ x7 x16 ∧ ∀ x17 ∈ x8, (x1.wires (List.ofFn x15)).getD x17 Bool.false = (x1.wires (List.ofFn x16)).getD x17 Bool.false := by
  classical
  intro C fan count nn headSpec
  dsimp only
  intro O inside six seedObs distinctRaw reach rawCount
  obtain ⟨gs,out⟩ := C
  cases gs with
  | nil => simp [Circuit.size] at count
  | cons a gs =>
    have legal : ∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
      intro g hg
      have mem : g∈(Circuit.mk (a::gs) out).gates := List.mem_cons_of_mem _ hg
      obtain ⟨ops,cap⟩ := fan g mem
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
      exact ⟨ops.elim Or.inl (fun h => Or.inr (h.resolve_right (nn g mem))),cap⟩
    have size : gs.length ≤ 7 := by simp only [Circuit.size,List.length_cons] at count; omega
    have limit : (O.erase 9).card ≤ 5 := by rw [Finset.card_erase_of_mem seedObs,six]; decide
    obtain ⟨x,y,diff,same,rest⟩ := frozen gs size legal (O.erase 9) limit
    refine ⟨x,y,diff,?_⟩
    intro i mem
    by_cases e : i=9
    · subst i
      exact (headSpec x).trans (same.trans (headSpec y).symm)
    · rw [canonical a gs out x (headSpec x),canonical a gs out y (headSpec y)]
      exact rest i (Finset.mem_erase.mpr ⟨e,mem⟩)

#print axioms of_frozen
end Co5056Frozen
