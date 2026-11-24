import PEqualNP.CoIsolated1593
namespace CoIsolated1593
open PEqualNP.MetaComplexity

def addInputs {n : Nat} (S : Finset (Fin n)) (g : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Bool :=
  decide (∃ i∈S, x i=true) || g x

theorem addInputs_insert {n : Nat} (p : Fin n) (S : Finset (Fin n)) (g : (Fin n → Bool) → Bool) :
    addInputs (insert p S) g = fun x => x p || addInputs S g x := by
  funext x
  cases e : x p <;> simp [addInputs,e,Finset.mem_insert,or_and_right,exists_or]

theorem many_isolated_iff {n : Nat} (s : Nat) (S : Finset (Fin (n+1))) (g : (Fin (n+1) → Bool) → Bool)
    (indep : ∀ p∈S, ∀ x b, g (Function.update x p b)=g x)
    (negative : ∃ x, g x=false ∧ ∀ i∈S, x i=false)
    (positive : ∃ x, g x=true) :
    HasCircuitSize (n+1) (addInputs S g) (s+S.card) ↔ HasCircuitSize (n+1) g s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have same : addInputs ∅ g=g := by funext x; simp [addInputs]
    simp [same]
  | @insert p A fresh ih =>
    have ext (x : Fin (n+1)→Bool) (b : Bool) :
        (∃ i∈A, (Function.update x p b) i=true) ↔ (∃ i∈A, x i=true) := by
      constructor <;> rintro ⟨i,hi,e⟩ <;> refine ⟨i,hi,?_⟩
      · simpa [Function.update_of_ne (fun h : i=p => fresh (h ▸ hi))] using e
      · simpa [Function.update_of_ne (fun h : i=p => fresh (h ▸ hi))] using e
    have free (x b) : addInputs A g (Function.update x p b)=addInputs A g x := by
      simp only [addInputs,ext,indep p (Finset.mem_insert_self p A)]
    obtain ⟨u,uf,uz⟩ := negative
    obtain ⟨v,vt⟩ := positive
    have az : ∀ i∈A, u i=false := fun i hi => uz i (Finset.mem_insert_of_mem hi)
    have no : ¬∃ i∈A, u i=true := by rintro ⟨i,hi,e⟩; rw [az i hi] at e; contradiction
    have low : addInputs A g u=false := by simp [addInputs,no,uf]
    have high : addInputs A g v=true := by simp [addInputs,vt]
    have different : addInputs A g u≠addInputs A g v := by simp [low,high]
    rw [addInputs_insert,Finset.card_insert_of_notMem fresh,←Nat.add_assoc]
    apply (isolated_iff p (addInputs A g) free ⟨u,v,different⟩).trans
    exact ih (fun i hi => indep i (Finset.mem_insert_of_mem hi)) ⟨u,uf,az⟩
#print axioms CoIsolated1593.many_isolated_iff
end CoIsolated1593
