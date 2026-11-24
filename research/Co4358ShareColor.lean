import PEqualNP.Co4358ShareRectangle

namespace CoNum4358.Tiny.ShareGrid
open CoAO3143
set_option maxRecDepth 65536

theorem owned_miss {A B : Finset K} {a p n} (own : Owner (A∪B) p n a) (na : a∉B) :
    FreeCell B p n := by
  intro b mb
  apply Bool.eq_false_iff.mpr
  intro hit
  have eq := own b (Finset.mem_union_right _ mb) hit
  exact na (by simpa only [eq] using mb)

private theorem own_miss_left {A B : Finset K} {a p n} (own : Owner (A∪B) p n a) (na : a∉A) :
    FreeCell A p n := by
  intro b mb
  apply Bool.eq_false_iff.mpr
  intro hit
  have eq := own b (Finset.mem_union_left _ mb) hit
  exact na (by simpa only [eq] using mb)

private theorem free_req {A : Finset K} {p n} (no : FreeCell A p n) : Required A p n :=
  ⟨⟨n,no⟩,⟨p,no⟩⟩

theorem opposite {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    (r : Rect) (h : validRect xs r=true) : decide (r.a∈A)≠decide (r.b∈A) := by
  simp only [validRect,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨⟨⟨⟨ne,ap⟩,an⟩,bp⟩,bn⟩ := h
  have lift {p n v} (h : forced xs p n v=true) : Owner (A∪B) p n v := by rw [←same]; exact forced_owner h
  have aP := lift ap
  have aN := lift an
  have bP := lift bp
  have bN := lift bn
  intro eq
  by_cases ma : r.a∈A
  · have mb : r.b∈A := by simpa [ma] using eq.symm
    have high : A⊆A∪B := Finset.subset_union_left
    have noA : r.a∉B := fun h => Finset.disjoint_left.mp dis ma h
    have noB : r.b∉B := fun h => Finset.disjoint_left.mp dis mb h
    exact ne (no_rectangle good.2.1 good.1 r
      (free_req (owned_miss aP noA)) (owner_shrink high aP)
      (free_req (owned_miss aN noA)) (owner_shrink high aN)
      (free_req (owned_miss bP noB)) (owner_shrink high bP)
      (free_req (owned_miss bN noB)) (owner_shrink high bN))
  · have mb : r.b∉A := by simpa [ma] using eq.symm
    have high : B⊆A∪B := Finset.subset_union_right
    exact ne (no_rectangle good.2.2 (outer_covered union) r
      (own_miss_left aP ma) (owner_shrink high aP)
      (own_miss_left aN ma) (owner_shrink high aN)
      (own_miss_left bP mb) (owner_shrink high bP)
      (own_miss_left bN mb) (owner_shrink high bN))

/-- Compile a certified pair of contrary input colors, using the global rather
than local unique-cell masks. The synthetic coordinates are always rechecked. -/
def shade (xs : List K) (a b : Prof) :=
  match propose a b with
  | none => false
  | some r => r.a==a.wire && r.b==b.wire && validRect xs r

theorem shade_opposite {A B : Finset K} (dis : Disjoint A B) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true) {xs : List K} (same : xs.toFinset=A∪B)
    {a b : Prof} (ok : shade xs a b=true) : decide (a.wire∈A)≠decide (b.wire∈A) := by
  unfold shade at ok
  split at ok
  · contradiction
  · rename_i r hr
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    have neq := opposite dis good union same r ok.2
    simpa only [ok.1.1,ok.1.2] using neq

end CoNum4358.Tiny.ShareGrid
