import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3239_371
    (project : ∀ (C : PEqualNP.MetaComplexity.BinaryCircuit) (s : Bool),
    (∀ g∈C.gates, ∃ a b : Bool, g.op=fun x y => (x==a)&&(y==b)) →
    (∀ x : Fin 9→Bool, (C.eval (List.ofFn x++[x 0||x 1,false]) != s)=((List.finRange 9).any fun u => x u && (List.finRange 9).any fun v => x v && (151120343641551963981858 : Nat).testBit (9*u.val+v.val))) →
    ∃ (j : Fin 7) (D : PEqualNP.MetaComplexity.BinaryCircuit), (j=2 ∨ j=3) ∧ D.size+3≤C.size ∧ (∀ g∈D.gates, g.op false false=false ∧ g.op true true=(g.op false true == g.op true false)) ∧ (∀ x : Fin 7→Bool, D.eval (List.ofFn x++[x 0||x j,false])=((List.finRange 7).any fun u => x u && (List.finRange 7).any fun v => x v && (2199056820780 : Nat).testBit (7*u.val+v.val))))
    (short : ∀ D : PEqualNP.MetaComplexity.BinaryCircuit, (∀ g∈D.gates, g.op false false=false ∧ g.op true true=(g.op false true == g.op true false)) → (∀ x : Fin 7→Bool, D.eval (List.ofFn x++[x 0||x 2,false])=((List.finRange 7).any fun u => x u && (List.finRange 7).any fun v => x v && (2199056820780 : Nat).testBit (7*u.val+v.val))) → 11≤D.size)
    (long : ∀ D : PEqualNP.MetaComplexity.BinaryCircuit, (∀ g∈D.gates, g.op false false=false ∧ g.op true true=(g.op false true == g.op true false)) → (∀ x : Fin 7→Bool, D.eval (List.ofFn x++[x 0||x 3,false])=((List.finRange 7).any fun u => x u && (List.finRange 7).any fun v => x v && (2199056820780 : Nat).testBit (7*u.val+v.val))) → 11≤D.size) : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[(0 : ℕ)]? = Option.some x4 → (∃ (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == Bool.false && x8 == x6) ∧ [x4.left, x4.right] ≤ [[(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.left x4.left, [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.right x4.right]) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C flag allowed _ answer
  let target : (Fin 9→Bool)→Bool := fun x => (List.finRange 9).any fun u => x u && (List.finRange 9).any fun v => x v && (151120343641551963981858 : Nat).testBit (9*u.val+v.val)
  have tab : ∀ a b c d e f g h i : Bool,
      let x : Fin 9→Bool := ![a,b,c,d,e,f,g,h,i]
      target x=(x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by decide +kernel
  have changeTarget (x : Fin 9→Bool) : target x=(x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    have eq : x=![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8] := by funext i; fin_cases i <;> rfl
    simpa only [←eq] using tab (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
  obtain ⟨j,D,side,size,normalized,hit⟩ := project C flag allowed (fun x => (answer x).trans (changeTarget x).symm)
  rcases side with rfl|rfl
  · have h := short D normalized hit
    omega
  · have h := long D normalized hit
    omega
