import PEqualNP.CoPhysical3174

namespace CoExact3174
open CoPhysical3174 CoThetaNine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def graph (x : Fin 9 → Bool) : Bool :=
  x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))

private def left (i : Nat) := i=1 ∨ i=5
private def right (i : Nat) := i=2 ∨ i=3 ∨ i=8
private def allowed (i : Nat) := i=1 ∨ i=2 ∨ i=3 ∨ i=5 ∨ i=8

private theorem classify : ∀ i j : Fin 9, allowed i.val → allowed j.val →
    ¬(left i.val ∧ left j.val) → ¬(right i.val ∧ right j.val) →
    ∃ (b : Fin 3) (flip : Bool),
      (perm flip i=1 ∧ perm flip j=mate b) ∨ (perm flip j=1 ∧ perm flip i=mate b) := by decide +kernel

private theorem preserved : ∀ (flip : Bool) (r : Input), graph (fun i => vtx (perm flip i) r)=ans r := by decide +kernel

private theorem raw_read (x : Fin 9→Bool) (i : Fin 9) : (List.ofFn x ++ [!x 0]).getD i.val false=x i := by
  rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
  simp [List.getD_eq_getElem?_getD]

private theorem bank_row (b : Fin 3) (flip : Bool) (i j : Fin 9)
    (orientation : (perm flip i=1 ∧ perm flip j=mate b) ∨ (perm flip j=1 ∧ perm flip i=mate b))
    (r : Input) : (bank b flip).map (fun w => w r)=
      let x := fun u => vtx (perm flip u) r
      let z := List.ofFn x ++ [!x 0]
      z ++ [GateOp.or.eval ([i.val,j.val].map fun k => z.getD k false)] := by
  have fixed : perm flip 0=0 := by cases flip <;> rfl
  have head : (vtx (perm flip i) r || vtx (perm flip j) r)=seed b r := by
    rcases orientation with ⟨x,y⟩|⟨x,y⟩ <;> rw [x,y] <;> simp [seed,Bool.or_comm]
  simp [bank,List.map_ofFn,Function.comp_def,negative,fixed,raw_read,GateOp.eval,List.append_assoc,head]

theorem exact_if (lower : SignedLower)
    (exclusion : ∀ (b : Fin 3) (inv : Bool) (k : Nat),k≤13 → ¬CoClean3024.Clean ans k (sources b inv)) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       ((¬∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) ∧ ¬∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro pins count members mixed C fan cap
  cases pins with
  | nil => simp at count
  | cons a more =>
    cases more with
    | nil => simp at count
    | cons b rest =>
      have empty : rest=[] := by simpa using count
      subst rest
      have A : allowed a := members a (by simp)
      have B : allowed b := members b (by simp)
      have small (u : Nat) (h : allowed u) : u<9 := by unfold allowed at h; omega
      let i : Fin 9 := ⟨a,small a A⟩
      let j : Fin 9 := ⟨b,small b B⟩
      have noL : ¬(left a ∧ left b) := by
        rintro ⟨x,y⟩
        apply mixed.1
        intro w hw
        rcases (show w=a ∨ w=b by simpa using hw) with rfl|rfl
        · exact x
        · exact y
      have noR : ¬(right a ∧ right b) := by
        rintro ⟨x,y⟩
        apply mixed.2
        intro w hw
        rcases (show w=a ∨ w=b by simpa using hw) with rfl|rfl
        · exact x
        · exact y
      obtain ⟨t,flip,orientation⟩ := classify i j A B noL noR
      by_contra! success
      have computes (r : Input) : C.eval ((bank t flip).map fun w => w r)=ans r := by
        rw [bank_row t flip i j orientation r]
        exact (success (fun u => vtx (perm flip u) r)).trans (preserved flip r)
      obtain ⟨k,hk,inv,c⟩ := extract lower t flip C fan cap computes
      exact exclusion t inv k hk c

#print axioms CoExact3174.exact_if
end CoExact3174
