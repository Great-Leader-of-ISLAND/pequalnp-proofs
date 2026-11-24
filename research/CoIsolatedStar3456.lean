import PEqualNP.CoStar3456
namespace CoCompile3456
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open CoAO3143Restriction

def edgeOn {n} (E : Fin n → Fin n → Prop) (r : Rows n) : Prop :=
  ∃ i j, E i j ∧ r i=true ∧ r j=true

/-- Directed encoding of an undirected isolated star. Either orientation of its
    physical edge is allowed; the rest of the graph is completely unrestricted. -/
structure IsolatedStar {n} (E : Fin n → Fin n → Prop) (c : Fin n) (L : Finset (Fin n)) : Prop where
  nonempty : L.Nonempty
  centerOut : c∉L
  links : ∀ i ∈ L, E c i ∨ E i c
  isolate : ∀ i j, E i j → (i∈insert c L ∨ j∈insert c L) →
    (i=c ∧ j∈L) ∨ (j=c ∧ i∈L)

private theorem true_of_link {n} {E : Fin n → Fin n → Prop} {r : Rows n} {i j : Fin n}
    (h : E i j ∨ E j i) (hi : r i=true) (hj : r j=true) : edgeOn E r := by
  rcases h with h|h
  · exact ⟨i,j,h,hi,hj⟩
  · exact ⟨j,i,h,hj,hi⟩

theorem edge_freeze {n} {E : Fin n → Fin n → Prop} (R : Finset (Fin n)) (r : Rows n) :
    edgeOn E (freeze R r) ↔ edgeOn (fun i j => E i j ∧ i∉R ∧ j∉R) r := by
  constructor
  · rintro ⟨i,j,he,hi,hj⟩
    by_cases ii : i∈R
    · simp [freeze,ii] at hi
    by_cases jj : j∈R
    · simp [freeze,jj] at hj
    exact ⟨i,j,⟨he,ii,jj⟩,by simpa [freeze,ii] using hi,by simpa [freeze,jj] using hj⟩
  · rintro ⟨i,j,⟨he,ii,jj⟩,hi,hj⟩
    exact ⟨i,j,he,by simpa [freeze,ii] using hi,by simpa [freeze,jj] using hj⟩

theorem star_split {n} {E : Fin n → Fin n → Prop} {c L} (star : IsolatedStar E c L) (r : Rows n) :
    edgeOn E r ↔ edgeOn E (freeze (insert c L) r) ∨ (r c=true ∧ ∃ i∈L, r i=true) := by
  rw [edge_freeze]
  constructor
  · rintro ⟨i,j,he,hi,hj⟩
    by_cases near : i∈insert c L ∨ j∈insert c L
    · rcases star.isolate i j he near with ⟨rfl,jm⟩|⟨rfl,im⟩
      · exact Or.inr ⟨hi,j,jm,hj⟩
      · exact Or.inr ⟨hj,i,im,hi⟩
    · exact Or.inl ⟨i,j,⟨he,fun h => near (Or.inl h),fun h => near (Or.inr h)⟩,hi,hj⟩
  · rintro (⟨i,j,⟨he,_,_⟩,hi,hj⟩|⟨hc,i,hi,hb⟩)
    · exact ⟨i,j,he,hi,hj⟩
    · exact true_of_link (star.links i hi) hc hb

theorem starEssential {n} {E : Fin n → Fin n → Prop} {c L} (star : IsolatedStar E c L)
    {F : Wire (Rows n)} (spec : ∀ r, F r=true ↔ edgeOn E r) {i : Fin n}
    (hi : i∈insert c L) : Essential F i := by
  obtain ⟨j,hj,ne,link⟩ : ∃ j ∈ insert c L, j≠i ∧ (E i j ∨ E j i) := by
    rcases Finset.mem_insert.mp hi with rfl|hm
    · obtain ⟨j,hj⟩ := star.nonempty
      exact ⟨j,Finset.mem_insert_of_mem hj,fun e => star.centerOut (e ▸ hj),star.links j hj⟩
    · exact ⟨c,Finset.mem_insert_self _ _,fun e => star.centerOut (e.symm ▸ hm),(star.links i hm).symm⟩
  have nol : ¬E j j := by
    intro loop
    rcases star.isolate j j loop (Or.inl hj) with ⟨rfl,bad⟩|⟨rfl,bad⟩ <;> exact star.centerOut bad
  let two : Rows n := fun v => decide (v=i ∨ v=j)
  have yes : F two=true := (spec _).mpr (true_of_link link (by simp [two]) (by simp [two]))
  have no : F (one j) ≠ true := by
    intro v
    obtain ⟨a,b,e,ha,hb⟩ := (spec _).mp v
    have ea : a=j := of_decide_eq_true ha
    have eb : b=j := of_decide_eq_true hb
    exact nol (ea ▸ eb ▸ e)
  refine ⟨two,one j,?_,fun e => no (e ▸ yes)⟩
  intro v hv
  simp [two,one,hv]

/-- For a nonempty residual edge graph, its own normalizability is sufficient:
    the removed star introduces no singleton-positive AND in the full graph. -/
theorem isolatedStar_normalize {n} (E : Fin n → Fin n → Prop) (C : Circuit)
    (cm : Monotone2 C) (spec : ∀ r, circuitFun n C r=true ↔ edgeOn E r)
    {c L} (star : IsolatedStar E c L)
    (remaining : ∃ i j, E i j ∧ i∉insert c L ∧ j∉insert c L)
    (cleanRest : ∀ A : Circuit, Monotone2 A → ReadsBack n A →
      (∀ r, circuitFun n A r=true ↔ edgeOn (fun i j => E i j ∧ i∉insert c L ∧ j∉insert c L) r) →
      ∃ B : Circuit, Monotone2 B ∧ ReadsBack n B ∧ dry n B.gates ∧
        B.size≤A.size ∧ circuitFun n B=circuitFun n A) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ dry n D.gates ∧
      D.size≤C.size ∧ circuitFun n D=circuitFun n C := by
  let R := insert c L
  have nc : ¬Constant (cut (freeze R) (circuitFun n C)) := by
    rintro ⟨b,eq⟩
    obtain ⟨i,j,he,hi,hj⟩ := remaining
    have yes := (spec (freeze R (fun _ => true))).mpr
      ((edge_freeze R _).mpr ⟨i,j,⟨he,hi,hj⟩,rfl,rfl⟩)
    have no : circuitFun n C (freeze R (fun _ => false)) ≠ true := by
      intro h
      obtain ⟨a,b,_,ha,_⟩ := (edge_freeze R _).mp ((spec _).mp h)
      contradiction
    have et := congrFun eq (fun _ => true)
    have ef := congrFun eq (fun _ => false)
    change circuitFun n C (freeze R (fun _ => true))=b at et
    change circuitFun n C (freeze R (fun _ => false))=b at ef
    exact no (ef.trans (et.symm.trans yes))
  cases hlist : L.toList with
  | nil =>
    obtain ⟨a,ha⟩ := star.nonempty
    have hm : a ∈ L.toList := by simpa using ha
    simp [hlist] at hm
  | cons leaf ls =>
    have mem (i : Fin n) : i∈leaf::ls ↔ i∈L := by rw [←hlist]; simp
    have num : R.card=ls.length+2 := by
      have len := congrArg List.length hlist
      simp at len
      change (insert c L).card=ls.length+2
      rw [Finset.card_insert_of_notMem star.centerOut]
      omega
    apply star_recombine C cm R (fun _ hx => starEssential star spec hx) nc c leaf ls
      (fun hc => star.centerOut ((mem c).mp hc)) num
    · intro r
      apply Bool.eq_iff_iff.mpr
      rw [spec,star_split star,Bool.or_eq_true,Bool.and_eq_true]
      have hit : (r leaf || ls.any r)=true ↔ ∃ i∈L, r i=true := by
        change (leaf::ls).any r = true ↔ _
        rw [List.any_eq_true]
        exact exists_congr (fun i => and_congr (mem i) Iff.rfl)
      rw [hit]
      change (edgeOn E (freeze R r) ∨ _) ↔ (circuitFun n C (freeze R r)=true ∨ _)
      rw [spec]
    · intro A am ar av
      apply cleanRest A am ar
      intro r
      rw [av]
      change circuitFun n C (freeze R r)=true ↔ _
      rw [spec,edge_freeze]

end CoCompile3456
