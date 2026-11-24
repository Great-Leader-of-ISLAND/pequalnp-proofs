import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace CoUnsafePort3004
variable {V : Type} [DecidableEq V]
def Independent (edge : V→V→Prop) (S : Finset V) := ∀ a∈S,∀ b∈S,¬edge a b

theorem unsafe_partner {edge : V→V→Prop} (sym : Symmetric edge) (irr : ∀ a, ¬edge a a)
    {x : V} {bank : Finset V → Bool} (mono : ∀ A B : Finset V,A⊆B → bank A=true → bank B=true)
    (stable : ∀ J : Finset V,x∉J → bank J=true → Independent edge J → Independent edge (insert x J))
    {I S : Finset V} (small : I⊆S) (notRead : x∉S) (ok : Independent edge I) (high : bank I=true) :
    ∀ u,edge x u → ∃ v∈S,edge u v := by
  intro u incident
  by_contra! noNeighbor
  have diff : x≠u := fun eq => irr u (eq ▸ incident)
  have same : Independent edge (insert u I) := by
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with ae|ai <;> rcases Finset.mem_insert.mp hb with be|bi
    · rw [ae,be]; exact irr _
    · rw [ae]; exact noNeighbor _ (small bi)
    · rw [be]; exact fun e => noNeighbor _ (small ai) (sym e)
    · exact ok _ ai _ bi
  have away : x∉insert u I := fun h => (Finset.mem_insert.mp h).elim diff (fun hx => notRead (small hx))
  have both := stable (insert u I) away (mono _ _ (Finset.subset_insert _ _) high) same
  exact both _ (Finset.mem_insert_self _ _) _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) incident

theorem and_partner {edge : V→V→Prop} (x : V) (S : Finset V) (bank : Finset V → Bool)
    (locality : ∀ A,bank A=bank (A∩S)) (empty : bank ∅=false)
    (necessary : ∀ u,edge x u → bank {u}=true) :
    ∀ u,edge x u → u∈S := by
  intro u adj
  by_contra absent
  have eq : ({u}:Finset V)∩S=∅ := by ext i; simp; aesop
  have value := locality {u}
  rw [eq,empty,necessary u adj] at value
  contradiction

end CoUnsafePort3004
