import PEqualNP.CoDelete4139

namespace CoFactorSupport4077
open PEqualNP.Outside.L_meta_2153_aux.CoDelete4139 (Ten petersen)
open PEqualNP.CircuitLowerBounds

def Uses (f : Ten → Bool) (i : Fin 10) : Prop :=
  ∃ a b : Ten, (∀ k, k ≠ i → a k = b k) ∧ f a ≠ f b

def starMasks : List ℕ := [116,201,402,554,773]
def base (i j : Fin 10) : Ten :=
  let n := (starMasks.find? fun m => !(m.testBit i.val || m.testBit j.val)).getD 0
  fun k => n.testBit k.val

def add (r : Ten) (i : Fin 10) : Ten := fun k => if k = i then true else r k

theorem geometry : ∀ i j : Fin 10,
    petersen (base i j) = false ∧ petersen (add (base i j) i) = true ∧
    petersen (add (base i j) j) = true := by decide +kernel

theorem untouched (r : Ten) (i : Fin 10) : ∀ k, k ≠ i → r k = add r i k := by
  intro k ne
  simp [add,ne]

theorem from_omissions (a b : Ten → Bool) (i j : Fin 10)
    (ha : ¬Uses a i) (hb : ¬Uses b j)
    (positive : ∀ x, petersen x = true → a x = true ∧ b x = true) :
    ∃ x : Ten, petersen x = false ∧ a x = true ∧ b x = true := by
  let r := base i j
  obtain ⟨bad,good₁,good₂⟩ := geometry i j
  have aeq : a r = a (add r i) :=
    Classical.byContradiction fun ne => ha ⟨r,add r i,untouched r i,ne⟩
  have beq : b r = b (add r j) :=
    Classical.byContradiction fun ne => hb ⟨r,add r j,untouched r j,ne⟩
  exact ⟨r,bad,aeq.trans (positive _ good₁).1,beq.trans (positive _ good₂).2⟩

theorem one_full (a b : Ten → Bool) (exactly : ∀ x : Ten, (a x && b x) = petersen x) :
    (∀ i, Uses a i) ∨ (∀ i, Uses b i) := by
  classical
  by_contra miss
  push_neg at miss
  obtain ⟨⟨i,hi⟩,j,hj⟩ := miss
  obtain ⟨x,hx,aa,bb⟩ := from_omissions a b i j hi hj (fun r pr =>
    by simpa only [Bool.and_eq_true] using (exactly r).trans pr)
  simpa [aa,bb,hx] using exactly x

def wire (isEdge : Bool) (C : Circuit) (j : ℕ) (x : Ten) : Bool :=
  (C.wires (List.ofFn x ++ [x 0 || if isEdge = true then x 1 else x 2])).getD j false

theorem physical (isEdge : Bool) (C : Circuit) (u v : ℕ)
    (missing₁ : ∃ i, ¬Uses (wire isEdge C u) i) (missing₂ : ∃ j, ¬Uses (wire isEdge C v) j)
    (positive : ∀ r, petersen r = true → wire isEdge C u r = true ∧ wire isEdge C v r = true) :
    ∃ r, petersen r = false ∧ wire isEdge C u r = true ∧ wire isEdge C v r = true := by
  obtain ⟨i,hi⟩ := missing₁
  obtain ⟨j,hj⟩ := missing₂
  exact from_omissions _ _ i j hi hj positive

#print axioms physical
end CoFactorSupport4077
