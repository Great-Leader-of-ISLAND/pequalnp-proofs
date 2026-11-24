import PEqualNP.CoBitBlock4482
namespace CoBlockPartition4482

/-- Each pair assigns all objects to exactly one of two sublists. -/
def splits {α : Type} : List α → List (List α × List α)
  | [] => [([],[])]
  | x::xs =>
    let v := splits xs
    v.map (fun (l,r) => (x::l,r)) ++ v.map (fun (l,r) => (l,x::r))

theorem take_split {α : Type} (p : α→Bool) (xs : List α) :
    (xs.filter p,xs.filter (fun x => !(p x)))∈splits xs := by
  induction xs with
  | nil => simp [splits]
  | cons x xs ih =>
    cases hp : p x
    · simp only [List.filter_cons,hp,Bool.false_eq_true,↓reduceIte,Bool.not_false]
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨_,ih,rfl⟩
    · simp only [List.filter_cons,hp,↓reduceIte,Bool.not_true,Bool.false_eq_true]
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨_,ih,rfl⟩

/-- The least remaining list element anchors the next block. Its complementary
list has at least one object per remaining terminal. Singleton terminal blocks
are allowed without testing; this relaxation can only admit additional cases. -/
def possible {α : Type} (ok : List α→List α→Bool) : Nat → List α → List α → Bool
  | 0,todo,_ => todo.isEmpty
  | _+1,[],_ => false
  | k+1,a::xs,closed =>
    if xs.length=k then true
    else if xs.length<k then false
    else (splits xs).any fun (take,remain) =>
      decide (k≤remain.length) && ok (a::take) (closed++remain) &&
      possible ok k remain ((a::take)++closed)

theorem possible_of_owner {α γ : Type} [DecidableEq γ] (ok : List α→List α→Bool)
    (owner : α→γ) (S : Finset α) (k : Nat) (T : Finset γ)
    (size : T.card=k) (todo closed : List α)
    (lands : ∀ w∈todo, owner w∈T) (past : ∀ w∈closed, owner w∉T)
    (onto : ∀ t∈T, ∃ w∈todo, owner w=t)
    (cover : ∀ w∈S,w∈todo∨w∈closed)
    (good : ∀ t∈T, ∀ part outside : List α,
       (∀w∈part,owner w=t) → (∀w∈outside,owner w≠t) →
       (∀w∈S,w∈part∨w∈outside) → ok part outside=true) :
    possible ok k todo closed=true := by
  classical
  induction k generalizing T todo closed with
  | zero =>
    have ht : T=∅ := Finset.card_eq_zero.mp size
    cases todo with
    | nil => rfl
    | cons a xs =>
      have bad := lands a (List.mem_cons_self)
      simp [ht] at bad
  | succ k ih =>
    have count {G : Finset γ} {zs : List α} (h : ∀g∈G,∃z∈zs,owner z=g) :
        G.card≤zs.length := by
      have incl : G⊆zs.toFinset.image owner := by
        intro g mg
        obtain ⟨w,wm,e⟩ := h g mg
        exact Finset.mem_image.mpr ⟨w,List.mem_toFinset.mpr wm,e⟩
      exact (Finset.card_le_card incl).trans (Finset.card_image_le.trans List.toFinset_card_le)
    have enough := count onto
    cases todo with
    | nil => simp at enough; omega
    | cons a xs =>
      let t := owner a
      let take := xs.filter (fun x => decide (owner x=t))
      let rest := xs.filter (fun x => !(decide (owner x=t)))
      have mt : t∈T := lands a List.mem_cons_self
      have ins (w) : w∈take ↔ w∈xs ∧ owner w=t := by simp [take]
      have out (w) : w∈rest ↔ w∈xs ∧ owner w≠t := by simp [rest]
      have pa (w) (hw : w∈a::take) : owner w=t := by
        rcases List.mem_cons.mp hw with rfl|m
        · rfl
        · exact ((ins w).mp m).2
      have extn (w) (hw : w∈closed++rest) : owner w≠t := by
        rcases List.mem_append.mp hw with m|m
        · intro eq
          exact past w m (eq.symm ▸ mt)
        · exact ((out w).mp m).2
      have all (w) (hw : w∈S) : w∈a::take ∨ w∈closed++rest := by
        rcases cover w hw with m|m
        · rcases List.mem_cons.mp m with rfl|m
          · exact Or.inl List.mem_cons_self
          by_cases e : owner w=t
          · exact Or.inl (List.mem_cons_of_mem _ ((ins w).mpr ⟨m,e⟩))
          · exact Or.inr (List.mem_append_right _ ((out w).mpr ⟨m,e⟩))
        · exact Or.inr (List.mem_append_left _ m)
      have accepted := good t mt (a::take) (closed++rest) pa extn all
      have ksize : (T.erase t).card=k := by rw [Finset.card_erase_of_mem mt,size]; omega
      have remains (g) (m : g∈T.erase t) : ∃ w∈rest, owner w=g := by
        obtain ⟨ne,mg⟩ := Finset.mem_erase.mp m
        obtain ⟨w,wm,e⟩ := onto g mg
        have no : owner w≠t := fun eq => ne (e.symm.trans eq)
        rcases List.mem_cons.mp wm with rfl|wm
        · exact (no rfl).elim
        · exact ⟨w,(out w).mpr ⟨wm,no⟩,e⟩
      have next := ih (T.erase t) ksize rest ((a::take)++closed) (by
        intro w m
        obtain ⟨mw,n⟩ := (out w).mp m
        exact Finset.mem_erase.mpr ⟨n,lands w (List.mem_cons_of_mem _ mw)⟩) (by
        intro w mw hit
        rcases List.mem_append.mp mw with early|old
        · exact (Finset.mem_erase.mp hit).1 (pa w early)
        · exact past w old (Finset.mem_erase.mp hit).2) remains (by
        intro w m
        rcases all w m with assigned|q
        · exact Or.inr (List.mem_append_left _ assigned)
        rcases List.mem_append.mp q with old|untouched
        · exact Or.inr (List.mem_append_right _ old)
        · exact Or.inl untouched) (by
        intro g m
        exact good g (Finset.mem_erase.mp m).2)
      have options : (take,rest)∈splits xs := take_split _ _
      have length := count remains
      rw [ksize] at length
      simp only [possible]
      split
      · rfl
      · split
        · simp only [List.length_cons] at enough
          omega
        · exact List.any_eq_true.mpr ⟨(take,rest),options,by simp [length,accepted,next]⟩

end CoBlockPartition4482
