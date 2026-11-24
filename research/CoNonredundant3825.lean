import PEqualNP.Defs
namespace CoNonredundant3825
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wire (n : ℕ) (C : Circuit) (i : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD i false

def bypassable (n : ℕ) (C : Circuit) (k : ℕ) : Prop :=
  (∃ b : Bool,∀ x,wire n C (n+k) x=b) ∨
    (∃ i<n+k,∀ x,wire n C (n+k) x=wire n C i x)

def nonconstant (n : ℕ) (C : Circuit) : Prop := ∀ b : Bool,¬∀ x,wire n C C.output x=b

/- The append-and-rebuild compression below is generalized from the published
   R_meta_2498_1, PR 4979. It keeps all raw inputs, allows arbitrary n and arbitrary
   output, and bounds the cost for any simultaneous set of aliases or constants. -/
theorem compress {n : ℕ} (C : Circuit) (hC : FanInTwo C) (nonconst : nonconstant n C)
    (S : Finset ℕ) (hS : ∀ k∈S,k<C.gates.length ∧ bypassable n C k) :
    ∃ D : Circuit,FanInTwo D ∧ circuitFun n D=circuitFun n C ∧ D.size+S.card≤C.size := by
  classical
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have evalNot (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]; omega
  have lengthOf (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]; omega
  have last (w : List Bool) (b : Bool) (n : ℕ) (hn : w.length = n) :
      (w ++ [b]).getD n false = b := by
    subst hn
    simp [List.getD_eq_getElem?_getD]
  have beyond (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have getOf (n : ℕ) (y : Fin n → Bool) (m : Fin n) : (List.ofFn y).getD m.val false = y m := by
    simp [List.getD_eq_getElem?_getD]
  let W : (Fin n → Bool) → List Bool := fun y => C.wires (List.ofFn y)
  let N : List Gate → (Fin n → Bool) → List Bool := fun gs y => gs.foldl step (List.ofFn y)
  have hNlen (gs y) : (N gs y).length = n + gs.length := by simp [N, lengthOf]
  have hWlen (y) : (W y).length = n + C.gates.length := by
    change (C.gates.foldl step (List.ofFn y)).length = _
    simp [lengthOf]
  have keepN (gs : List Gate) (g : Gate) (i : ℕ) (hi : i < n + gs.length) (y) :
      (N (gs ++ [g]) y).getD i false = (N gs y).getD i false := by
    simp only [N, List.foldl_append]
    exact keep [g] _ i (by simpa [lengthOf] using hi)
  have newN (gs : List Gate) (g : Gate) (y) :
      (N (gs ++ [g]) y).getD (n + gs.length) false =
        g.op.eval (g.inputs.map fun i => (N gs y).getD i false) := by
    simp only [N, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact last _ _ _ (by simp [lengthOf])
  have gateW (k : ℕ) (hk : k < C.gates.length) (y) :
      (W y).getD (n + k) false =
        (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i =>
          if i < n + k then (W y).getD i false else false) := by
    have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by simp
    let P := (C.gates.take k).foldl step (List.ofFn y)
    have hP : P.length = n + k := by simp [P, lengthOf]; omega
    have hW : W y = (C.gates.drop (k + 1)).foldl step (step P C.gates[k]) := by
      change C.gates.foldl step (List.ofFn y) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hlow (i : ℕ) (hi : i < n + k) : (W y).getD i false = P.getD i false := by
      rw [hW, keep _ _ _ (by simp [step]; omega)]
      simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (hP ▸ hi)]
    rw [hW, keep _ _ _ (by simp [step]; omega)]
    have h1 : (step P C.gates[k]).getD (n + k) false =
        (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i => P.getD i false) :=
      last _ _ _ hP
    rw [h1, ← hW]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    split_ifs with hi
    · exact (hlow i hi).symm
    · exact beyond _ _ (by omega)
  let Good : List Gate → ℕ → Prop := fun gs i =>
    (∃ b : Bool, ∀ y, (W y).getD i false = b) ∨
    (∃ i' < n + gs.length, ∀ y, (W y).getD i false = (N gs y).getD i' false)
  have main (k : ℕ) (hk : k ≤ C.gates.length) : ∃ gs : List Gate,
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) ∧
      gs.length + (S.filter (· < k)).card ≤ k ∧ ∀ i < n + k, Good gs i := by
    induction k with
    | zero =>
      refine ⟨[], by simp, by simp, fun i hi => ?_⟩
      exact Or.inr ⟨i,by simpa using hi,fun y => by
        change (C.gates.foldl step (List.ofFn y)).getD i false=(List.ofFn y).getD i false
        exact keep _ _ _ (by simpa using hi)⟩
    | succ k ih =>
      have hk' : k < C.gates.length := by omega
      obtain ⟨gs, hfan, hcount, hgood⟩ := ih (by omega)
      have hfilter : (S.filter (· < k + 1)).card ≤ (S.filter (· < k)).card + 1 := by
        have hsub : S.filter (· < k + 1) ⊆ insert k (S.filter (· < k)) := by
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_insert] at ha ⊢
          rcases Nat.lt_succ_iff_lt_or_eq.mp ha.2 with h | h
          · exact Or.inr ⟨ha.1, h⟩
          · exact Or.inl h
        exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      by_cases hG : Good gs (n + k)
      · refine ⟨gs, hfan, by omega, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < (n + k) + 1 by omega) with h | h
        · exact hgood i h
        · exact h ▸ hG
      have notConst (b : Bool) : ¬ ∀ y, (W y).getD (n + k) false = b :=
        fun h => hG (Or.inl ⟨b, h⟩)
      have notAlias (i : ℕ) (hi : i < n + k) :
          ¬ ∀ y, (W y).getD (n + k) false = (W y).getD i false := by
        intro h
        rcases hgood i hi with ⟨b, hb⟩ | ⟨i', hi', hb⟩
        · exact hG (Or.inl ⟨b, fun y => (h y).trans (hb y)⟩)
        · exact hG (Or.inr ⟨i', hi', fun y => (h y).trans (hb y)⟩)
      have hkS : k ∉ S := by
        intro hmem
        rcases (hS k hmem).2 with ⟨b, hb⟩ | ⟨i, hi, hb⟩
        · exact notConst b fun y => hb y
        · exact notAlias i hi fun y => hb y
      have hfilter' : S.filter (· < k + 1) = S.filter (· < k) := by
        ext a
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
          · exact h
          · exact absurd (h ▸ h1) hkS
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by omega⟩
      let val : ℕ → (Fin n → Bool) → Bool := fun i y =>
        if i < n + k then (W y).getD i false else false
      have valCases (i : ℕ) : (∃ b : Bool, ∀ y, val i y = b) ∨
          (i < n + k ∧ ∃ i' < n + gs.length, ∀ y, val i y = (N gs y).getD i' false) := by
        by_cases hi : i < n + k
        · rcases hgood i hi with ⟨b, hb⟩ | ⟨i', hi', hb⟩
          · exact Or.inl ⟨b, fun y => by simp only [val, if_pos hi]; exact hb y⟩
          · exact Or.inr ⟨hi, i', hi', fun y => by simp only [val, if_pos hi]; exact hb y⟩
        · exact Or.inl ⟨false, fun y => by simp only [val, if_neg hi]⟩
      have notVal (i : ℕ) : ¬ ∀ y, (W y).getD (n + k) false = val i y := by
        intro h
        by_cases hi : i < n + k
        · exact notAlias i hi fun y => by rw [h y]; simp only [val, if_pos hi]
        · exact notConst false fun y => by rw [h y]; simp only [val, if_neg hi]
      have build : ∃ g : Gate, (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g.inputs.length ≤ 2) ∧ ∀ y, (W y).getD (n + k) false =
            g.op.eval (g.inputs.map fun i => (N gs y).getD i false) := by
        have hgate := gateW k hk'
        obtain ⟨hop, hlen⟩ := hC _ (List.getElem_mem hk')
        generalize C.gates[k] = g at hgate hop hlen
        obtain ⟨op, ins⟩ := g
        have hg (y) : (W y).getD (n + k) false = op.eval (ins.map fun i => val i y) := hgate y
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩
        · exact absurd (fun y => hg y) (notConst (op.eval []))
        · rcases hop with rfl | rfl | rfl
          · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot]) (notVal a)
          · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot]) (notVal a)
          · rcases valCases a with ⟨b, hb⟩ | ⟨_, a', _, ha'⟩
            · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst (!b))
            · exact ⟨⟨.not, [a']⟩, by simp, fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, ha']⟩
        · rcases hop with rfl | rfl | rfl
          · rcases valCases a with ⟨b, hb⟩ | ⟨_, a', _, ha'⟩
            · cases b
              · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst false)
              · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notVal c)
            rcases valCases c with ⟨b, hb⟩ | ⟨_, c', _, hc'⟩
            · cases b
              · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst false)
              · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notVal a)
            exact ⟨⟨.and, [a', c']⟩, by simp, fun y => by
              rw [hg y]; simp [evalAnd, evalOr, evalNot, ha', hc']⟩
          · rcases valCases a with ⟨b, hb⟩ | ⟨_, a', _, ha'⟩
            · cases b
              · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notVal c)
              · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst true)
            rcases valCases c with ⟨b, hb⟩ | ⟨_, c', _, hc'⟩
            · cases b
              · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notVal a)
              · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst true)
            exact ⟨⟨.or, [a', c']⟩, by simp, fun y => by
              rw [hg y]; simp [evalAnd, evalOr, evalNot, ha', hc']⟩
          · rcases valCases a with ⟨b, hb⟩ | ⟨_, a', _, ha'⟩
            · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst (!b))
            · exact ⟨⟨.not, [a']⟩, by simp, fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, ha']⟩
        · simp at hlen
      obtain ⟨g, hgfan, hgval⟩ := build
      refine ⟨gs ++ [g], ?_, ?_, fun i hi => ?_⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with h | h
        · exact hfan g' h
        · rw [List.mem_singleton.mp h]; exact hgfan
      · rw [hfilter']; simp; omega
      · rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < (n + k) + 1 by omega) with h | h
        · rcases hgood i h with ⟨b, hb⟩ | ⟨i', hi', hb⟩
          · exact Or.inl ⟨b, hb⟩
          · exact Or.inr ⟨i', by simp; omega, fun y => by rw [keepN gs g i' hi', hb y]⟩
        · subst h
          exact Or.inr ⟨n + gs.length, by simp, fun y => by rw [newN, hgval y]⟩
  obtain ⟨gs, hfan, hcount, hgood⟩ := main C.gates.length le_rfl
  have hall : S.filter (· < C.gates.length) = S :=
    Finset.filter_true_of_mem fun j hj => (hS j hj).1
  rw [hall] at hcount
  by_cases ho : C.output < n + C.gates.length
  · rcases hgood C.output ho with ⟨b,hb⟩ | ⟨o,_,hb⟩
    · exact (nonconst b hb).elim
    · refine ⟨⟨gs,o⟩,hfan,funext (fun y => (hb y).symm),hcount⟩
  · exact (nonconst false (fun y => beyond _ _ (by rw [hWlen]; omega))).elim

theorem no_alias_or_constant {n : ℕ} {C : Circuit} (minimum : IsMinimalCircuit n C)
    (nc : nonconstant n C) {j : ℕ} (actual : j<C.gates.length) : ¬bypassable n C j := by
  intro red
  obtain ⟨D,fan,equal,cost⟩ := compress C minimum.1 nc {j} (by
    intro k hk
    cases Finset.mem_singleton.mp hk
    exact ⟨actual,red⟩)
  have := minimum.2 D fan equal
  simp only [Finset.card_singleton] at cost
  omega

#print axioms no_alias_or_constant
end CoNonredundant3825
