import PEqualNP.CoIsolatedStar3456

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CoCompile3456 CoAO3143Restriction in
theorem Co5282.project : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) (c : Fin n) (L : Finset (Fin n)),
    let Split := fun (G H : SimpleGraph (Fin n)) (c : Fin n) (L : Finset (Fin n)) =>
    L.Nonempty ∧ c ∉ L ∧ (∀ j ∈ L, G.Adj c j) ∧
    (∀ i j, G.Adj i j → (i ∈ insert c L ∨ j ∈ insert c L) →
      (i = c ∧ j ∈ L) ∨ (j = c ∧ i ∈ L)) ∧
    (∀ i j, H.Adj i j ↔ G.Adj i j ∧ i ∉ insert c L ∧ j ∉ insert c L) ∧
    ∃ i j, H.Adj i j
    let Realizes := fun (G : SimpleGraph (Fin n)) (C : Circuit) => ∀ r : Fin n → Bool,
      C.eval (List.ofFn r) = true ↔ ∃ i j, G.Adj i j ∧ r i = true ∧ r j = true
    Split G H c L → ∀ C : Circuit, Monotone2 C → Realizes G C →
    ∃ A : Circuit, Monotone2 A ∧ Realizes H A ∧ A.size + L.card + 1 ≤ C.size := by
  intro n G H c L
  dsimp only
  rintro ⟨has,apart,links,isolate,induced,rem⟩ C cm spec
  have star : IsolatedStar G.Adj c L :=
    ⟨has,apart,fun i hi => Or.inl (links i hi),isolate⟩
  let R := insert c L
  have realizes (r : Rows n) : circuitFun n C r = true ↔ edgeOn G.Adj r := spec r
  have cofactor (r : Rows n) : edgeOn G.Adj (freeze R r) ↔ edgeOn H.Adj r := by
    rw [edge_freeze]
    constructor
    · rintro ⟨i,j,ij,ri,rj⟩
      exact ⟨i,j,(induced _ _).mpr ij,ri,rj⟩
    · rintro ⟨i,j,ij,ri,rj⟩
      exact ⟨i,j,(induced _ _).mp ij,ri,rj⟩
  have nc : ¬ Constant (cut (freeze R) (circuitFun n C)) := by
    rintro ⟨b,all⟩
    obtain ⟨i,j,he⟩ := rem
    have yes := (realizes (freeze R (fun _ => true))).mpr
      ((cofactor _).mpr ⟨i,j,he,rfl,rfl⟩)
    have no : circuitFun n C (freeze R (fun _ => false)) ≠ true := by
      intro hit
      obtain ⟨u,v,_,hu,_⟩ := (cofactor _).mp ((realizes _).mp hit)
      contradiction
    have on := congrFun all (fun _ => true)
    have off := congrFun all (fun _ => false)
    change circuitFun n C (freeze R (fun _ => true)) = b at on
    change circuitFun n C (freeze R (fun _ => false)) = b at off
    exact no (off.trans (on.symm.trans yes))
  obtain ⟨A,am,_,price,rep⟩ :=
    physical_project C cm R (fun _ hi => starEssential star realizes hi) nc
  refine ⟨A,am,?_,?_⟩
  · intro r
    change circuitFun n A r = true ↔ edgeOn H.Adj r
    rw [rep]
    exact (realizes _).trans (cofactor r)
  · have card : R.card = L.card + 1 := Finset.card_insert_of_notMem apart
    rw [card] at price
    omega

#print axioms Co5282.project
