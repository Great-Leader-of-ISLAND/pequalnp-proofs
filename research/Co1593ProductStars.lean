import PEqualNP.Co1593StarCounting

namespace Co1593StarCounting

open Finset

variable {V : Type*} [DecidableEq V]

private theorem singleton_of_small {a : Scope V} (non : a.Nonempty) (small : a.card ≤ 1) :
    ∃ c, a={c} := by
  obtain ⟨c,hc⟩ := non
  refine ⟨c,?_⟩
  ext x
  constructor
  · intro hx
    exact Finset.mem_singleton.mpr (Finset.card_le_one.mp small hx hc)
  · intro hx
    obtain rfl := Finset.mem_singleton.mp hx
    exact hc

/-- Each product is independently oriented to valid graph edges. The middle gates may
    receive arbitrary computed OR scopes and may be repeated syntactically. -/
theorem orient_products {G : SimpleGraph V} (m : Nat)
    (girth : ∀ v (c : G.Walk v v), c.IsCycle → 7 ≤ c.length)
    (L R : Fin m → Scope V) (left : ∀ i,(L i).Nonempty) (right : ∀ i,(R i).Nonempty)
    (test : ∀ x y, G.Adj x y ↔
      ∃ i,(x∈L i ∨ y∈L i) ∧ (x∈R i ∨ y∈R i)) :
    ∃ (center : Fin m→V) (leaves : Fin m→Scope V),
      (∀ i, (L i={center i} ∧ leaves i=R i) ∨ (R i={center i} ∧ leaves i=L i)) ∧
      ∀ x y,G.Adj x y ↔ ∃ i, (x=center i ∧ y∈leaves i) ∨ (y=center i ∧ x∈leaves i) := by
  classical
  have split (i : Fin m) : ∃ c S,
      (L i={c} ∧ S=R i) ∨ (R i={c} ∧ S=L i) := by
    have safe : ∀ x∈L i,∀ y∈R i,G.Adj x y := fun x hx y hy =>
      (test x y).2 ⟨i,Or.inl hx,Or.inr hy⟩
    rcases product_has_single_side girth safe with small|small
    · obtain ⟨c,hc⟩ := singleton_of_small (left i) small
      exact ⟨c,R i,Or.inl ⟨hc,rfl⟩⟩
    · obtain ⟨c,hc⟩ := singleton_of_small (right i) small
      exact ⟨c,L i,Or.inr ⟨hc,rfl⟩⟩
  choose c S parts using split
  refine ⟨c,S,parts,?_⟩
  have dis (i : Fin m) (x : V) (a : x∈L i) (b : x∈R i) : False :=
    (G.loopless x) ((test x x).2 ⟨i,Or.inl a,Or.inl b⟩)
  intro x y
  rw [test]
  apply exists_congr
  intro i
  rcases parts i with ⟨hl,eq⟩|⟨hr,eq⟩
  · rw [eq,hl]
    simp only [Finset.mem_singleton]
    have no : c i ∉ R i := fun h => dis i _ (by rw [hl]; simp) h
    grind
  · rw [eq,hr]
    simp only [Finset.mem_singleton]
    have no : c i ∉ L i := fun h => dis i _ h (by rw [hr]; simp)
    grind

/-- A single-level representation with all AND gates live satisfies the standard exact
    graph lower bound, including any sharing of wire values inside the OR parts. -/
theorem layered_lower [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (m : Nat) (girth : ∀ v (c : G.Walk v v), c.IsCycle → 7 ≤ c.length)
    (L R : Fin m → Scope V) (left : ∀ i,(L i).Nonempty) (right : ∀ i,(R i).Nonempty)
    (test : ∀ x y,G.Adj x y ↔ ∃ i,(x∈L i ∨ y∈L i) ∧ (x∈R i ∨ y∈R i))
    {I : Finset (Scope V)} (raw : ∀ a∈I,a.card≤1)
    {gs B} (run : Build I gs B) (present : ∀ i,L i∈B ∧ R i∈B)
    {J : Finset (Scope (Fin m))} (tags : ∀ a∈J,a.card≤1)
    {top O} (topRun : Build J top O) (output : (Finset.univ : Finset (Fin m))∈O)
    (k : Nat) (cover : ∀ T : Finset V,(∀ x y,G.Adj x y → x∈T ∨ y∈T) → k≤T.card) :
    G.edgeSet.ncard+k ≤ gs.length+m+top.length+1 := by
  classical
  obtain ⟨c, S, parts, graph⟩ := orient_products m girth L R left right test
  let K := Finset.univ.image c
  let F (x : V) := Finset.univ.filter (fun i => c i=x)
  let D (x : V) := (F x).image S
  have select (i : Fin m) : S i ∈ D (c i) :=
    Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩
  have alive (x : V) (hx : x∈K) : (D x).Nonempty := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨S i,select i⟩
  have pick {x y : V} (h : y∈total (D x)) : ∃ i, c i=x ∧ y∈S i := by
    obtain ⟨a,ha,hy⟩ := Finset.mem_biUnion.mp h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨i,(Finset.mem_filter.mp hi).2,hy⟩
  have use (i : Fin m) {y : V} (hy : y∈S i) : c i ∈ K ∧ y∈total (D (c i)) :=
    ⟨Finset.mem_image_of_mem c (Finset.mem_univ _), Finset.mem_biUnion.mpr ⟨S i,select i,hy⟩⟩
  have mdl (x y : V) : G.Adj x y ↔
      (x∈K ∧ y∈total (D x)) ∨ (y∈K ∧ x∈total (D y)) := by
    rw [graph]
    constructor
    · rintro ⟨i,⟨rfl,h⟩|⟨rfl,h⟩⟩
      · exact Or.inl (use i h)
      · exact Or.inr (use i h)
    · rintro (h|h)
      · obtain ⟨i,e,hi⟩ := pick h.2
        exact ⟨i,Or.inl ⟨e.symm,hi⟩⟩
      · obtain ⟨i,e,hi⟩ := pick h.2
        exact ⟨i,Or.inr ⟨e.symm,hi⟩⟩
  have sub (x : V) (_ : x∈K) : D x ⊆ B := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    rcases parts i with h|h
    · rw [h.2]
      exact (present i).2
    · rw [h.2]
      exact (present i).1
  have allot : (∑ x ∈ K, (D x).card) ≤ m := by
    have indices : ∀ i∈(Finset.univ : Finset (Fin m)), c i∈K :=
      fun i hi => Finset.mem_image_of_mem c hi
    have hh := Finset.card_eq_sum_card_fiberwise indices
    have bounds : (∑ x ∈ K, (D x).card) ≤ ∑ x ∈ K, (F x).card :=
      Finset.sum_le_sum (fun x _ => Finset.card_image_le)
    simp only [F] at bounds
    rw [←hh] at bounds
    simpa using bounds
  have topCount := join_output_count tags topRun Finset.univ output
  exact counting_lower girth K D alive mdl raw run sub k m top.length cover allot (by simpa using topCount)

end Co1593StarCounting
