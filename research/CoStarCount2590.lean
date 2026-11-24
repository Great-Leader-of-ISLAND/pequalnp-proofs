import Mathlib

/-! Counting end of the Petersen monotone Karchmer--Wigderson rectangle-partition
argument. A protocol tree is not assumed; upstream L-meta-252 already gives
the formula leaf bound by a more general theorem. The semantic construction
of disjoint equal-responsibility stars from a partition is a separate input. -/
namespace CoStarCount2590

abbrev V := Fin 10
abbrev E := Fin 15

/-- Lexicographic order of the 15 positive rows used by the Petersen search. -/
def ends : E → V × V :=
  ![(0,1),(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),(3,4),(3,8),(4,9),
    (5,7),(5,8),(6,8),(6,9),(7,9)]

def star (v : V) : Finset E :=
  Finset.univ.filter fun e => (ends e).1=v ∨ (ends e).2=v

theorem degree_three : ∀ v : V, (star v).card=3 := by decide +kernel
theorem no_loops : ∀ e : E, (ends e).1 ≠ (ends e).2 := by decide +kernel

private def mark (S : Finset V) (v : V) : Nat := if v∈S then 1 else 0

private theorem mark_sum (S : Finset V) : (∑ v : V,mark S v)=S.card := by
  classical
  simp [mark,Finset.sum_boole]

private theorem sum_vertices (f : V→Nat) : (∑ v : V,f v)=
    f 0+(f 1+(f 2+(f 3+(f 4+(f 5+(f 6+(f 7+(f 8+f 9)))))))) := by
  simp [Fin.sum_univ_succ]

/-- Each five-cycle contributes at most two independent vertices; just its
five adjacency inequalities suffice, with no search over possible inputs. -/
theorem independent_le_four (S : Finset V)
    (indep : ∀ e : E, (ends e).1∈S → (ends e).2∉S) : S.card≤4 := by
  have edge (e : E) : mark S (ends e).1+mark S (ends e).2≤1 := by
    by_cases a : (ends e).1∈S
    · simp [mark,a,indep e a]
    · by_cases b : (ends e).2∈S <;> simp [mark,a,b]
  let f := mark S
  have a₁ : f 0+f 1≤1 := edge 0
  have a₂ : f 1+f 2≤1 := edge 3
  have a₃ : f 2+f 3≤1 := edge 5
  have a₄ : f 3+f 4≤1 := edge 7
  have a₅ : f 0+f 4≤1 := edge 1
  have b₁ : f 5+f 7≤1 := edge 10
  have b₂ : f 7+f 9≤1 := edge 14
  have b₃ : f 6+f 9≤1 := edge 13
  have b₄ : f 6+f 8≤1 := edge 12
  have b₅ : f 5+f 8≤1 := edge 11
  have a : f 0+f 1+f 2+f 3+f 4≤2 := by omega
  have b : f 5+f 6+f 7+f 8+f 9≤2 := by omega
  have total : (∑ v : V,f v)=S.card := mark_sum S
  rw [sum_vertices] at total
  omega

theorem alpha_attained : ∃ S : Finset V, S.card=4 ∧
    ∀ e : E, (ends e).1∈S → (ends e).2∉S := by
  refine ⟨{0,2,8,9},by decide,?_⟩
  decide +kernel

/-- A one-leaf vertex selects its entire star. Disjoint selected stars thus
imply that the one-leaf centers form an independent set. -/
theorem ones_independent (m : V→Nat) (selected : V→Finset E)
    (sub : ∀ v,selected v⊆star v)
    (full : ∀ v,m v=1 → 3≤(selected v).card)
    (dis : ∀ u v,u≠v → Disjoint (selected u) (selected v)) :
    ∀ e : E, m (ends e).1=1 → m (ends e).2≠1 := by
  have cover (v : V) (one : m v=1) : selected v=star v :=
    Finset.eq_of_subset_of_card_le (sub v) (by rw [degree_three]; exact full v one)
  intro e left right
  have useL : e∈selected (ends e).1 := by rw [cover _ left]; simp [star]
  have useR : e∈selected (ends e).2 := by rw [cover _ right]; simp [star]
  exact Finset.disjoint_left.mp (dis _ _ (no_loops e)) useL useR

theorem disjoint_budget (selected : V→Finset E)
    (dis : ∀ u v,u≠v → Disjoint (selected u) (selected v)) :
    (∑ v : V,(selected v).card)≤15 := by
  have eq : (Finset.univ.biUnion selected).card = ∑ v : V,(selected v).card :=
    Finset.card_biUnion (fun u _ v _ uv => dis u v uv)
  rw [←eq]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)

/-- Pure integer form, for front ends recording only multiplicity classes. -/
theorem count_only (n₁ n₂ n₃ leaves : Nat) (vertices : n₁+n₂+n₃=10)
    (edgePrice : 3*n₁+2*n₂≤15) (alpha : n₁≤4)
    (leafPrice : n₁+2*n₂+3*n₃≤leaves) : 21≤leaves := by omega

/-- Number of labeled pieces (in particular formula leaves) on the actual 10 vertices. The selected-star
hypothesis is required only through its cardinality at one- and two-leaf
vertices, together with containment in the actual incident edges and
global pairwise disjointness. -/
theorem leaf_count (m : V→Nat) (selected : V→Finset E)
    (positive : ∀ v, 1≤m v) (sub : ∀ v,selected v⊆star v)
    (one : ∀ v,m v=1 → 3≤(selected v).card)
    (two : ∀ v,m v=2 → 2≤(selected v).card)
    (dis : ∀ u v,u≠v → Disjoint (selected u) (selected v)) : 21≤∑ v : V,m v := by
  let S := Finset.univ.filter fun v => m v=1
  have hS (v : V) : v∈S ↔ m v=1 := by simp [S]
  have ind := ones_independent m selected sub one dis
  have alpha := independent_le_four S (fun e l r => ind e ((hS _).mp l) ((hS _).mp r))
  have pay (v : V) : 6≤2*m v+(selected v).card+mark S v := by
    have pos := positive v
    by_cases a : m v=1
    · have sel := one v a
      have member := (hS v).mpr a
      simp only [mark,member,if_true]
      omega
    · by_cases b : m v=2
      · have sel := two v b
        omega
      · omega
  have sumPay : 60≤2*(∑ v : V,m v)+(∑ v : V,(selected v).card)+S.card := by
    calc
      60 = ∑ _v : V,(6 : Nat) := by simp
      _ ≤ ∑ v : V,(2*m v+(selected v).card+mark S v) :=
        Finset.sum_le_sum fun v _ => pay v
      _ = _ := by simp only [Finset.sum_add_distrib,←Finset.mul_sum,mark_sum]
  have edgeCap := disjoint_budget selected dis
  omega

#print axioms independent_le_four
#print axioms leaf_count
end CoStarCount2590
