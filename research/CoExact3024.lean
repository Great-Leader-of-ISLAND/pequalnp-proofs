import PEqualNP.CoNine3024Path
import PEqualNP.CoNine3024Roots

namespace CoExact3024
open CoNine3024 CoNine3024Rows CoNine3024PaidState CoNine3024Roots CoNine3024Path CoThetaNine
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

theorem exact_statement (L : SignedLower)
    (keep : Fin 11 → Bool → Nat → State → Bool) (sound : ∀p b, SoundGuard p (keep p b))
    (allRoots : ∀ (p : Fin 11) (b : Bool), b=true ∨ p=9 → Canon.run (keep p b) (geom p) 13 (Canon.order (root p b))=false) :
    ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  classical
  intro pins _ D fan small
  by_contra impossible
  push_neg at impossible
  have correct : ∀ r : Input,
      let x := fun i => vtx i r
      let z := List.ofFn x ++ [x 0 || x 2]
      D.eval (z ++ [GateOp.not.eval ((pins.map Fin.val).map fun i => z.getD i false)])=ans r := by
    intro r
    simpa only [List.map_map,Function.comp_def] using impossible (fun i => vtx i r)
  obtain ⟨k,S,limit,clean,labels,raw⟩ := CoPhysical3024.extract L pins D fan small correct
  obtain ⟨q,b,which,img⟩ := select_root L (CoPhysical3024.pivot pins) limit clean labels raw
  obtain ⟨ic,dc,gc,ac⟩ := reorder q (root q b) img (root_unique _ _) (root_sound _ _) (initial_ready q b k limit)
  have feasible := from_clean L q (keep q b) (sound q b) clean limit (Canon.order (root q b)) ic dc gc ac
  exact Bool.false_ne_true ((allRoots q b which).symm.trans (Canon.complete feasible))

#print axioms CoExact3024.exact_statement
end CoExact3024
