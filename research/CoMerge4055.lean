import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

namespace CoMerge4055
variable {I : Type} [DecidableEq I]
def mass (A : Finset (Finset I)) := A.biUnion id

def Budget (T : Finset (Finset I)) (n : Nat) : Prop :=
  ∀ A⊆T, (mass A).card ≤ A.card+n

theorem initial {T : Finset (Finset I)} (tiny : ∀ a∈T,a.card≤1) : Budget T 0 := by
  intro A sub
  have init : (mass A).card ≤ A.card := by
    induction A using Finset.induction_on with
    | empty => simp [mass]
    | @insert a A na ih =>
      have rest := ih (fun x hx => sub (Finset.mem_insert_of_mem hx))
      have small := tiny a (sub (Finset.mem_insert_self _ _))
      have union := Finset.card_union_le a (mass A)
      rw [Finset.card_insert_of_notMem na]
      simpa only [mass,Finset.biUnion_insert,id_eq] using (show (a∪mass A).card ≤ A.card+1 by omega)
  simpa using init

theorem add {T : Finset (Finset I)} {a b z : Finset I} {n} (before : Budget T n)
    (ha : a∈T) (hb : b∈T) (sub : z⊆a∪b) : Budget (insert z T) (n+1) := by
  intro A hA
  by_cases hz : z∈A
  · let R := A.erase z
    have hr : R⊆T := by
      intro t ht
      obtain ⟨ne,h⟩ := Finset.mem_erase.mp ht
      exact (Finset.mem_insert.mp (hA h)).resolve_left ne
    have old := before (insert a (insert b R)) (Finset.insert_subset ha (Finset.insert_subset hb hr))
    have incl : mass A ⊆ mass (insert a (insert b R)) := by
      intro i hi
      obtain ⟨t,ht,hit⟩ := Finset.mem_biUnion.mp hi
      by_cases e : t=z
      · subst t
        rcases Finset.mem_union.mp (sub hit) with h|h
        · exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_insert_self _ _,h⟩
        · exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
      · exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e,ht⟩)),hit⟩
    have ineq := Finset.card_le_card incl
    have e : R.card+1=A.card := Finset.card_erase_add_one hz
    have c := Finset.card_insert_le a (insert b R)
    have d := Finset.card_insert_le b R
    omega
  · have subT : A⊆T := by
      intro t ht
      exact (Finset.mem_insert.mp (hA ht)).resolve_left (fun eq => hz (eq ▸ ht))
    exact (before A subT).trans (by omega)

theorem single {T : Finset (Finset I)} {a : Finset I} {n} (bound : Budget T n)
    (ha : a∈T) : a.card ≤ n+1 := by
  have h := bound {a} (Finset.singleton_subset_iff.mpr ha)
  simpa [mass,Nat.add_comm] using h

end CoMerge4055
