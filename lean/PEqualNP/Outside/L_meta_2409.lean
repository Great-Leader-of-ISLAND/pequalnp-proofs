import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2409
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

abbrev WireStep (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ j, b = n + j ∧ j < C.gates.length ∧
    (gateAt C j).op = GateOp.or ∧ a ∈ (gateAt C j).inputs

abbrev Reach (n : ℕ) (C : Circuit) := Relation.ReflTransGen (WireStep n C)

def Big {N : ℕ} (n : ℕ) (C : Circuit) (pw : Fin N → ℕ) (w : ℕ) : Prop :=
  ∃ p q, Reach n C (pw p) w ∧ Reach n C (pw q) w ∧ p ≠ q

lemma input_eq {n : ℕ} {C : Circuit} {v w : ℕ} (h : Reach n C v w) (hw : w < n) : v = w := by
  cases h with
  | refl => rfl
  | tail _ hs =>
    obtain ⟨_,j,hj,_,_,_⟩ := hs
    omega

lemma small_input {n N : ℕ} (C : Circuit) (pw : Fin N → ℕ) (inj : Function.Injective pw)
    {w : ℕ} (hw : w < n) : ¬ Big n C pw w := by
  rintro ⟨p,q,hp,hq,hn⟩
  exact hn (inj ((input_eq hp hw).trans (input_eq hq hw).symm))

-- Take the first wire on a path whose shadow contains two different points.
lemma crossing {n N : ℕ} {C : Circuit} {pw : Fin N → ℕ} {a b : ℕ}
    (path : Reach n C a b) (small : ¬ Big n C pw a) (large : Big n C pw b) :
    ∃ j v, j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
      v ∈ (gateAt C j).inputs ∧ Reach n C a v ∧ ¬ Big n C pw v ∧
      Big n C pw (n+j) ∧ Reach n C (n+j) b := by
  induction path with
  | refl => exact (small large).elim
  | @tail b c path hs ih =>
    by_cases hb : Big n C pw b
    · obtain ⟨j,v,hj,ho,hm,hp,hv,hbig,hr⟩ := ih hb
      exact ⟨j,v,hj,ho,hm,hp,hv,hbig,hr.tail hs⟩
    · obtain ⟨_,j,rfl,hj,ho,hm⟩ := hs
      exact ⟨j,b,hj,ho,hm,path,hb,large,.refl⟩

def OrSet (C : Circuit) : Set ℕ :=
  {j | j < C.gates.length ∧ (gateAt C j).op = GateOp.or}

def Own {N M : ℕ} (n : ℕ) (C : Circuit) (pw : Fin N → ℕ) (I : Fin N → Fin M → Prop)
    (e : Fin N × Fin M) (t : ℕ × Fin 2) : Prop :=
  t.1 ∈ OrSet C ∧
  Reach n C (pw e.1) ((gateAt C t.1).inputs.getD t.2.val 0) ∧
  ¬ Big n C pw ((gateAt C t.1).inputs.getD t.2.val 0) ∧
  Big n C pw (n+t.1) ∧ ∀ q, Reach n C (pw q) (n+t.1) → I q e.2

lemma own_exists {n N M : ℕ} {C : Circuit} {pw : Fin N → ℕ} {I : Fin N → Fin M → Prop}
    (ao : PEqualNP.TopForm.IsAO2 n C) (inj : Function.Injective pw)
    (bound : ∀ p, pw p < n) (e : Fin N × Fin M) {w : ℕ}
    (hr : Reach n C (pw e.1) w) (hbig : Big n C pw w)
    (line : ∀ p, Reach n C (pw p) w → I p e.2) :
    ∃ t, Own n C pw I e t := by
  obtain ⟨j,v,hj,ho,hm,hp,hs,hb,tail⟩ := crossing hr (small_input C pw inj (bound _)) hbig
  have he : gateAt C j = C.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have len : (gateAt C j).inputs.length = 2 := by rw [he]; exact ao.2.2 _ (List.getElem_mem hj)
  obtain ⟨k,hk,hv⟩ := List.mem_iff_getElem.mp hm
  have heq : (gateAt C j).inputs.getD k 0 = v := (List.getD_eq_getElem _ _ hk).trans hv
  refine ⟨(j,⟨k, by omega⟩), ⟨hj,ho⟩, ?_, ?_, hb, fun q hq => line q (hq.trans tail)⟩
  · exact heq.symm ▸ hp
  · exact heq.symm ▸ hs

lemma owner_unique {n N M : ℕ} {C : Circuit} {pw : Fin N → ℕ} {I : Fin N → Fin M → Prop}
    (lin : ∀ p q l m, p ≠ q → l ≠ m → ¬ (I p l ∧ I q l ∧ I p m ∧ I q m))
    {e f : Fin N × Fin M} {t : ℕ × Fin 2}
    (h : Own n C pw I e t) (k : Own n C pw I f t) : e = f := by
  apply Prod.ext
  · by_contra hn
    exact h.2.2.1 ⟨e.1,f.1,h.2.1,k.2.1,hn⟩
  · by_contra hn
    obtain ⟨p,q,hp,hq,hne⟩ := h.2.2.2.1
    exact lin p q _ _ hne hn ⟨h.2.2.2.2 p hp,h.2.2.2.2 q hq,k.2.2.2.2 p hp,k.2.2.2.2 q hq⟩

lemma count {n N M : ℕ} {C : Circuit} {pw : Fin N → ℕ} {I : Fin N → Fin M → Prop}
    (lin : ∀ p q l m, p ≠ q → l ≠ m → ¬ (I p l ∧ I q l ∧ I p m ∧ I q m))
    (Good : Fin N × Fin M → Prop) (owners : ∀ e, I e.1 e.2 → Good e → ∃ t, Own n C pw I e t) :
    {e : Fin N × Fin M | I e.1 e.2}.ncard ≤
      2 * (OrSet C).ncard + {e : Fin N × Fin M | I e.1 e.2 ∧ ¬ Good e}.ncard := by
  classical
  let W : Set (Fin N × Fin M) := {e | I e.1 e.2 ∧ Good e}
  let X : Set (Fin N × Fin M) := {e | I e.1 e.2 ∧ ¬ Good e}
  let tags := OrSet C ×ˢ (Set.univ : Set (Fin 2))
  have ex (e) (h : e ∈ W) := owners e h.1 h.2
  let tag (e : Fin N × Fin M) : ℕ × Fin 2 := if h : e ∈ W then (ex e h).choose else (0,0)
  have ht (e) (h : e ∈ W) : Own n C pw I e (tag e) := by simpa [tag,h] using (ex e h).choose_spec
  have finiteO : (OrSet C).Finite := (Set.finite_lt_nat C.gates.length).subset (fun _ h => h.1)
  have card := Set.ncard_le_ncard_of_injOn (s := W) (t := tags) tag
    (fun e he => ⟨(ht e he).1, Set.mem_univ _⟩)
    (fun e he f hf eq => owner_unique lin (ht e he) (eq.symm ▸ ht f hf))
    (finiteO.prod (Set.toFinite _))
  have splitSet : {e : Fin N × Fin M | I e.1 e.2} = W ∪ X := by ext e; simp [W,X]; tauto
  rw [splitSet]
  have hu := Set.ncard_union_le W X
  have tc : tags.ncard = 2 * (OrSet C).ncard := by simp [tags,Set.ncard_prod,Nat.mul_comm]
  change (W ∪ X).ncard ≤ 2 * (OrSet C).ncard + X.ncard
  omega

end PEqualNP.Outside.L_meta_2409

open PEqualNP.Outside.L_meta_2409 in
theorem PEqualNP.Outside.L_meta_2409 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 2 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ex : Fin N × Fin M | I ex.1 ex.2 ∧ ¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ex.1 ∨ g7.2 = lw ex.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ex.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ex.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ex.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ex.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard}.ncard := by
  classical
  intro n N M pw lw I C ao inj _ _ bound _ lin _ R eqR T eqT _
  subst R
  have leaves (t : ℕ) (xs : List (ℕ × ℕ)) (h : T t xs) :
      ∀ q ∈ xs, Reach n C q.2 q.1 := by
    rw [eqT] at h
    apply h (fun _ ys => ∀ q ∈ ys, Reach n C q.2 q.1)
    · intro a b _ hab q hq
      have eq : q = (b,a) := List.mem_singleton.mp hq
      subst q
      exact hab
    · intro j v ys zs _ _ _ hy hz q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hy q hq
      · exact hz q hq
  let Good : Fin N × Fin M → Prop := fun ex => ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ex.1 ∨ g7.2 = lw ex.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ex.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ex.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ex.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ex.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard
  apply count (C := C) (pw := pw) lin Good
  intro e _ h
  obtain ⟨L,hroot,_,_,_,q,hq,hlabel,htight,hcard⟩ := h
  obtain ⟨j,ys,zs,_,_,_,hy,hz,rfl⟩ := hroot
  have reach : Reach n C q.2 q.1 := by
    rcases List.mem_append.mp hq with hq | hq
    · exact leaves _ _ hy q hq
    · exact leaves _ _ hz q hq
  have big : Big n C pw q.1 := by
    obtain ⟨a,ha,b,hb,hab⟩ := (Set.one_lt_ncard (s := {r : Fin N | Reach n C (pw r) q.1})).mp hcard
    exact ⟨a,b,ha,hb,hab⟩
  exact own_exists ao inj bound e (hlabel ▸ reach) big htight
