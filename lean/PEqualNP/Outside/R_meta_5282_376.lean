import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_5282_376
    (core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    let Split := fun (G H : SimpleGraph (Fin n)) (c : Fin n) (L : Finset (Fin n)) =>
    L.Nonempty ∧ c ∉ L ∧ (∀ j ∈ L, G.Adj c j) ∧
    (∀ i j, G.Adj i j → (i ∈ insert c L ∨ j ∈ insert c L) →
      (i = c ∧ j ∈ L) ∨ (j = c ∧ i ∈ L)) ∧
    (∀ i j, H.Adj i j ↔ G.Adj i j ∧ i ∉ insert c L ∧ j ∉ insert c L) ∧
    ∃ i j, H.Adj i j
    let Sparse := fun (G : SimpleGraph (Fin n)) =>
    (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) ∧
    (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    let Realizes := fun (G : SimpleGraph (Fin n)) (C : Circuit) => ∀ r : Fin n → Bool,
      C.eval (List.ofFn r) = true ↔ ∃ i j, G.Adj i j ∧ r i = true ∧ r j = true
    let Dry := fun (C : Circuit) => ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ S : Finset (Fin n), S.card ≤ 1 →
      (C.wires (List.ofFn fun i => decide (i ∈ S))).getD (n+j) false = false
    let Sol := fun (G : SimpleGraph (Fin n)) => ∃ C : Circuit, Monotone2 C ∧ Realizes G C ∧
    (∀ D : Circuit, Monotone2 D → Realizes G D → C.size ≤ D.size) ∧ Dry C
    Sparse G → (¬ ∃ H c L, Split G H c L) → Sol G)
    (project : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) (c : Fin n) (L : Finset (Fin n)),
    let Split := fun (G H : SimpleGraph (Fin n)) (c : Fin n) (L : Finset (Fin n)) =>
    L.Nonempty ∧ c ∉ L ∧ (∀ j ∈ L, G.Adj c j) ∧
    (∀ i j, G.Adj i j → (i ∈ insert c L ∨ j ∈ insert c L) →
      (i = c ∧ j ∈ L) ∨ (j = c ∧ i ∈ L)) ∧
    (∀ i j, H.Adj i j ↔ G.Adj i j ∧ i ∉ insert c L ∧ j ∉ insert c L) ∧
    ∃ i j, H.Adj i j
    let Realizes := fun (G : SimpleGraph (Fin n)) (C : Circuit) => ∀ r : Fin n → Bool,
      C.eval (List.ofFn r) = true ↔ ∃ i j, G.Adj i j ∧ r i = true ∧ r j = true
    Split G H c L → ∀ C : Circuit, Monotone2 C → Realizes G C →
    ∃ A : Circuit, Monotone2 A ∧ Realizes H A ∧ A.size + L.card + 1 ≤ C.size)
    (attach : ∀ (n : ℕ) (c : Fin n) (L : Finset (Fin n)),
    let Dry := fun (C : Circuit) => ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ S : Finset (Fin n), S.card ≤ 1 →
      (C.wires (List.ofFn fun i => decide (i ∈ S))).getD (n+j) false = false
    L.Nonempty → c ∉ L → ∀ C : Circuit, Monotone2 C → Dry C →
    (∃ r : Fin n → Bool, C.eval (List.ofFn r) = true) →
    ∃ D : Circuit, Monotone2 D ∧ Dry D ∧ D.size ≤ C.size + L.card + 1 ∧
      ∀ r : Fin n → Bool, D.eval (List.ofFn r) = true ↔
       C.eval (List.ofFn r) = true ∨ (r c = true ∧ ∃ j ∈ L, r j = true)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ (∀ (x10 : Fin x1 → Bool), x9.eval (List.ofFn x10) = x4 x10) ∧ (∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → (∀ (x12 : Fin x1 → Bool), x10.eval (List.ofFn x12) = x4 x12) → x9.size ≤ x10.size) ∧ x6 x9 := by
  classical
  intro n G inst
  dsimp only
  intro tri square
  let Split := fun (G H : SimpleGraph (Fin n)) (c : Fin n) (L : Finset (Fin n)) =>
      L.Nonempty ∧ c ∉ L ∧ (∀ j ∈ L, G.Adj c j) ∧
      (∀ i j, G.Adj i j → (i ∈ insert c L ∨ j ∈ insert c L) →
        (i = c ∧ j ∈ L) ∨ (j = c ∧ i ∈ L)) ∧
      (∀ i j, H.Adj i j ↔ G.Adj i j ∧ i ∉ insert c L ∧ j ∉ insert c L) ∧
      ∃ i j, H.Adj i j
  let Sparse := fun (G : SimpleGraph (Fin n)) =>
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) ∧
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
  let Realizes := fun (G : SimpleGraph (Fin n)) (C : Circuit) => ∀ r : Fin n → Bool,
        C.eval (List.ofFn r) = true ↔ ∃ i j, G.Adj i j ∧ r i = true ∧ r j = true
  let Dry := fun (C : Circuit) => ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
        ∀ S : Finset (Fin n), S.card ≤ 1 →
        (C.wires (List.ofFn fun i => decide (i ∈ S))).getD (n+j) false = false
  let Sol := fun (G : SimpleGraph (Fin n)) => ∃ C : Circuit, Monotone2 C ∧ Realizes G C ∧
      (∀ D : Circuit, Monotone2 D → Realizes G D → C.size ≤ D.size) ∧ Dry C
  let E := fun (K : SimpleGraph (Fin n)) =>
    Finset.univ.filter (fun z : Fin n × Fin n => K.Adj z.1 z.2)
  have solve : ∀ k, ∀ K : SimpleGraph (Fin n), (E K).card = k → Sparse K → Sol K := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro K ek hs
      by_cases nonterminal : ∃ H c L, Split K H c L
      · obtain ⟨H,c,L,decomp⟩ := nonterminal
        obtain ⟨has,apart,links,isolate,induced,existsEdge⟩ := decomp
        have sub {i j} (ij : H.Adj i j) : K.Adj i j := ((induced i j).mp ij).1
        have sparseH : Sparse H := ⟨fun a b d ab bd da => hs.1 a b d (sub ab) (sub bd) (sub da),
          fun a b d e ab bd de ea => hs.2 a b d e (sub ab) (sub bd) (sub de) (sub ea)⟩
        have fewer : (E H).card < k := by
          rw [← ek]
          apply Finset.card_lt_card
          apply lt_of_le_of_ne
          · intro z hz
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub (Finset.mem_filter.mp hz).2⟩
          · intro equal
            obtain ⟨v,hv⟩ := has
            have yes : (c,v) ∈ E K := Finset.mem_filter.mpr ⟨Finset.mem_univ _,links v hv⟩
            rw [← equal] at yes
            have bad := ((induced c v).mp (Finset.mem_filter.mp yes).2).2.1
            exact bad (Finset.mem_insert_self _ _)
        obtain ⟨B,bm,be,least,bd⟩ := ih _ fewer H rfl sparseH
        have active : ∃ r : Fin n → Bool, B.eval (List.ofFn r) = true := by
          obtain ⟨i,j,edge⟩ := existsEdge
          exact ⟨fun _ => true,(be _).mpr ⟨i,j,edge,rfl,rfl⟩⟩
        obtain ⟨D,dm,dd,upper,sim⟩ := attach n c L has apart B bm bd active
        have exactD : Realizes K D := by
          intro r
          rw [sim r,be r]
          constructor
          · rintro (⟨i,j,ij,ri,rj⟩ | ⟨rc,j,hj,rj⟩)
            · exact ⟨i,j,sub ij,ri,rj⟩
            · exact ⟨c,j,links j hj,rc,rj⟩
          · rintro ⟨i,j,ij,ri,rj⟩
            by_cases touch : i ∈ insert c L ∨ j ∈ insert c L
            · rcases isolate i j ij touch with ⟨rfl,hj⟩ | ⟨rfl,hi⟩
              · exact Or.inr ⟨ri,j,hj,rj⟩
              · exact Or.inr ⟨rj,i,hi,ri⟩
            · exact Or.inl ⟨i,j,(induced _ _).mpr ⟨ij,fun h => touch (Or.inl h),
                fun h => touch (Or.inr h)⟩,ri,rj⟩
        refine ⟨D,dm,exactD,?_,dd⟩
        intro C cm ce
        obtain ⟨A,am,ae,price⟩ := project n K H c L ⟨has,apart,links,isolate,induced,existsEdge⟩ C cm ce
        have lower := least A am ae
        omega
      · exact core n K hs nonterminal
  obtain ⟨C,cm,ce,least,cleaned⟩ := solve _ G rfl ⟨tri,square⟩
  refine ⟨C,cm,?_,?_,cleaned⟩
  · intro r
    exact Bool.eq_iff_iff.mpr ((ce r).trans (by simp))
  · intro D dm dg
    apply least D dm
    intro r
    rw [dg r]
    simp
