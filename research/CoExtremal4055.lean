import Mathlib.Data.Finset.Max
import PEqualNP.CoPencil4055

namespace CoPencil4055

def Below (x y : X) := ∀ i,x i=true → y i=true
def supp (x : X) := Finset.univ.filter fun i => x i=true

set_option maxRecDepth 5000 in
theorem maximal_extension (x : X) (clean : independent x) :
    ∃ y : X, Below x y ∧ independent y ∧ ∀ z : X,independent z → Below y z → z=y := by
  classical
  let S := Finset.univ.filter (fun y : X => Below x y ∧ independent y)
  have own : x∈S := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(show Below x x from fun _ h => h),clean⟩
  obtain ⟨y,hy,big⟩ := Finset.exists_max_image S (fun y => (supp y).card) ⟨x,own⟩
  obtain ⟨up,keep⟩ := (Finset.mem_filter.mp hy).2
  refine ⟨y,up,keep,?_⟩
  intro z cz yz
  have hz : z∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(fun i h => yz i (up i h)),cz⟩
  have sub : supp y⊆supp z := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,yz i (Finset.mem_filter.mp hi).2⟩
  have eq := Finset.eq_of_subset_of_card_le sub (big z hz)
  funext i
  have iff : z i=true ↔ y i=true := by simpa only [supp,Finset.mem_filter,Finset.mem_univ,true_and] using
      (show i∈supp z ↔ i∈supp y by rw [eq])
  exact Bool.eq_iff_iff.mpr iff

theorem value_graph (rs : List CoSensitivity4055.Rule) (out : Finset Nat)
    (yes : ∀ p l,incident p l=true → value rs out (edge p l)=true)
    (no : ∀ x : X,independent x → (∀ y : X,independent y →
      (∀ i,x i=true → y i=true) → y=x) → value rs out x=false) (x : X) :
    value rs out x=true ↔ ¬ independent x := by
  constructor
  · intro accepts clean
    obtain ⟨y,grow,good,last⟩ := maximal_extension x clean
    exact Bool.noConfusion ((monotone rs out grow accepts).symm.trans (no y good last))
  · intro dirty
    unfold independent at dirty
    push_neg at dirty
    obtain ⟨p,l,inc,hp,hl⟩ := dirty
    apply monotone rs out (x:=edge p l)
    · intro i hi
      simp only [edge,decide_eq_true_eq] at hi
      rcases hi with rfl|rfl
      · simpa using hp
      · simpa using hl
    · exact yes p l inc
#print axioms value_graph
end CoPencil4055
