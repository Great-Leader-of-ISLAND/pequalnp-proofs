import PEqualNP.Outside.L_meta_2004

namespace PEqualNP.Research.FirstGateRank
open CircuitLowerBounds MetaComplexity

-- A final component with all the original inputs but possibly lacking the
-- last input leaves at most two component labels in the no-cost wiring.
theorem essential_except_last (n : Nat) (D : Circuit) (m : Monotone2 D)
    (ess : ∀ i : Fin n, ∃ x y : Fin (n+1) → Bool,
      (∀ j, j ≠ i.castSucc → x j = y j) ∧ circuitFun (n+1) D x ≠ circuitFun (n+1) D y) :
    n ≤ D.size + 1 := by
  classical
  obtain ⟨c,hsize,hwire⟩ := PEqualNP.Outside.L_meta_2004.core (n+1) (Fin.last n) D.gates
    (fun g hg => (m g hg).2)
  obtain ⟨k,hk⟩ := hwire D.output
  have eql (i : Fin n) : c i.castSucc = c k := by
    obtain ⟨x,y,agree,diff⟩ := ess i
    by_contra bad
    apply diff
    rw [PEqualNP.Outside.L_meta_2004.cf_eq,PEqualNP.Outside.L_meta_2004.cf_eq]
    apply hk
    intro j hj
    apply agree j
    rintro rfl
    exact bad hj
  have sub : Finset.univ.image c ⊆ {c k,c (Fin.last n)} := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [eql j]
  have small := Finset.card_le_card sub
  have pair : ({c k,c (Fin.last n)} : Finset (Fin (n+1))).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  change n ≤ D.gates.length+1
  omega

def headValue {n : Nat} (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false)

theorem snocList {n : Nat} (x : Fin n → Bool) (v : Bool) :
    List.ofFn (Fin.snoc x v : Fin (n+1) → Bool) = List.ofFn x ++ [v] := by
  rw [List.ofFn_succ']
  simp

theorem first_rank {n : Nat} (g : Gate) (gs : List Gate) (o : Nat)
    (hm : Monotone2 ⟨g::gs,o⟩)
    (preserved : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ headValue g x = headValue g y ∧
      circuitFun n ⟨g::gs,o⟩ x ≠ circuitFun n ⟨g::gs,o⟩ y) :
    n ≤ (Circuit.mk (g::gs) o).size := by
  let D : Circuit := ⟨gs,o⟩
  have eqn (x : Fin n → Bool) : circuitFun (n+1) D (Fin.snoc x (headValue g x)) =
      circuitFun n ⟨g::gs,o⟩ x := by
    change D.eval (List.ofFn (Fin.snoc x (headValue g x) : Fin (n+1) → Bool)) = _
    rw [snocList]
    rfl
  apply essential_except_last n D (fun a ha => hm a (List.mem_cons_of_mem _ ha))
  intro i
  obtain ⟨x,y,xy,hh,hne⟩ := preserved i
  refine ⟨Fin.snoc x (headValue g x),Fin.snoc y (headValue g y),?_,?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun t => ?_) j
    · simp only [Fin.snoc_last]
      exact fun _ => hh
    · simp only [Fin.snoc_castSucc]
      intro ne
      apply xy
      intro h
      exact ne (congrArg Fin.castSucc h)
  · simpa only [eqn] using hne

end PEqualNP.Research.FirstGateRank
