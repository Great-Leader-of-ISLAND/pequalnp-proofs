import PEqualNP.Co4358ShareRectangle

namespace CoNum4358.Tiny.ShareGrid
open CoAO3143
set_option maxRecDepth 65536

def estimateProduct (used : Nat) :=
  let u := fullMask ^^^ used
  let high := columnMask<<<6
  let low := fullMask ^^^ high
  let p := ((u ||| ((u&&&low)+low)) &&& high)>>>6
  let z := u ||| (u>>>7)
  let z := z ||| (z>>>14)
  let z := z ||| (z>>>28)
  p*(z%128)

def uncoveredProduct (left right prod : Nat) :=
  let missing := prod &&& (fullMask ^^^ left)
  if missing==0 then false else
    let i := missing.log2
    let p := Fin.ofNat 8 (i/7)
    let n := Fin.ofNat 7 i
    productBit right p n && noBit left p n

theorem product_no {A B : Finset K} {xs ys : List K} (left : A⊆xs.toFinset) (right : B⊆ys.toFinset)
    (guarantee : Covered A (Required B)) (mask : Nat) : uncoveredProduct (cov xs) (cov ys) mask=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  unfold uncoveredProduct at h
  dsimp only at h
  split at h
  · contradiction
  · rw [Bool.and_eq_true] at h
    obtain ⟨hp,hn⟩ := h
    obtain ⟨w,hw,yes⟩ := guarantee _ _ (required_shrink right (productBit_required hp))
    exact Bool.false_ne_true ((noBit_free hn w (left hw)).symm.trans yes)

/-- Projection and firstHit propose a contradiction. rectBit rechecks the
four exact cells and the owner's identity in the larger candidate side. -/
def localRect (xs : List K) (mask : Nat) (dom : Fin 8→Fin 7→Bool) :=
  let only := Corners.exclusive xs &&& mask
  (firstHit (xs.map fun a => prof a only)).any (rectBit xs dom)

theorem local_no {X : Finset K} {xs : List K} (sub : X⊆xs.toFinset)
    {D : Fin 8→Fin 7→Prop} (apart : Compatible X D) (cover : Covered X D)
    {dom : Fin 8→Fin 7→Bool} (valid : ∀p n,dom p n=true → D p n) (mask : Nat) :
    localRect xs mask dom=false := by
  unfold localRect
  dsimp only
  generalize firstHit _ = hint
  cases hint with
  | none => rfl
  | some r => exact rectBit_false sub apart cover valid r

def partialBlock (left right : List K) :=
  let ca := cov left
  let cb := cov right
  let p := estimateProduct cb
  uncoveredProduct ca cb p || localRect left p (productBit cb) ||
    localRect right (fullMask ^^^ ca) (noBit ca)

theorem partial_no {A B : Finset K} {xs ys : List K} (left : A⊆xs.toFinset) (right : B⊆ys.toFinset)
    (good : Feasible A B) (union : ∀p n,∃w∈A∪B,directed w p n=true) :
    partialBlock xs ys=false := by
  have pa := product_no left right good.1 (estimateProduct (cov ys))
  have pb := local_no left good.2.1 good.1 (fun _ _ h => required_shrink right (productBit_required h))
    (estimateProduct (cov ys))
  have pc := local_no right good.2.2 (outer_covered union) (fun _ _ h => free_shrink left (noBit_free h))
    (fullMask ^^^ cov xs)
  simp only [partialBlock,pa,pb,pc,Bool.false_or]

def possible : List K → List K → List K → Bool
  | a,b,[] => !a.isEmpty && !(partialBlock a b)
  | a,b,h::rs =>
    !(partialBlock (a++h::rs) (b++h::rs)) &&
      (possible (h::a) b rs || possible a (h::b) rs)

theorem possible_yes {A B : Finset K} (na : A.Nonempty) (good : Feasible A B)
    (union : ∀p n,∃w∈A∪B,directed w p n=true)
    (left right rest : List K) (al : A⊆(left++rest).toFinset) (br : B⊆(right++rest).toFinset)
    (dis : Disjoint A B) : possible left right rest=true := by
  induction rest generalizing left right with
  | nil =>
    simp only [List.append_nil] at al br
    have lne : left≠[] := by
      obtain ⟨a,ha⟩ := na
      intro e
      have bad := al ha
      simp [e] at bad
    simp [possible,lne,partial_no al br good union]
  | cons h rs ih =>
    have ok := partial_no al br good union
    simp only [possible,ok,Bool.not_false,Bool.true_and,Bool.or_eq_true]
    by_cases ha : h∈A
    · left
      apply ih (h::left) right
      · intro x hx
        have old := al hx
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at old ⊢
        tauto
      · intro x hx
        have old := br hx
        have ne : x≠h := by
          intro eq
          exact Finset.disjoint_left.mp dis ha (by simpa only [eq] using hx)
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at old ⊢
        tauto
    · right
      apply ih left (h::right)
      · intro x hx
        have old := al hx
        have ne : x≠h := fun eq => ha (by simpa only [eq] using hx)
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at old ⊢
        tauto
      · intro x hx
        have old := br hx
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at old ⊢
        tauto

theorem reports_one (xs : List K) (p : Fin 8) (n : Fin 7) :
    (unionSep false (xs.map wide)).getLsbD (p.val*7+n.val)=true ↔
      ∃a∈xs,directed a p n=true := by
  induction xs with
  | nil => simp [unionSep]
  | cons a xs ih =>
    simp only [List.map_cons,unionSep,BitVec.getLsbD_or,joint_bit,Bool.or_eq_true,ih,List.mem_cons]
    constructor
    · rintro (h|⟨b,hb,byes⟩)
      · exact ⟨a,.inl rfl,h⟩
      · exact ⟨b,.inr hb,byes⟩
    · rintro ⟨b,(ba|bs),yes⟩
      · subst b; exact .inl yes
      · exact .inr ⟨b,bs,yes⟩

theorem single_possible {k : Nat} {xs : List K} (live : Live k 0 (xs.map wide).toFinset)
    (size : xs.toFinset.card=k) : possible [] [] xs=true := by
  have eq : (xs.map wide).toFinset=up xs.toFinset := by ext w; simp [up]
  have l : Live k 0 (up xs.toFinset) := by rw [←eq]; exact live
  obtain ⟨a,sub,ne,feasible⟩ := tight_plus_one l size
  have full : a∪(xs.toFinset\a)=xs.toFinset := by
    ext x
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro (ha|⟨hx,_⟩)
      · exact sub ha
      · exact hx
    · intro hx
      by_cases ha : x∈a
      · exact .inl ha
      · exact .inr ⟨hx,ha⟩
  have cov : unionSep false (xs.map wide)=top := live_cover live rfl
  have dis : Disjoint a (xs.toFinset\a) := by
    rw [Finset.disjoint_left]
    intro x ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  apply possible_yes ne feasible _ [] [] xs (by simpa using sub) (by simpa using (Finset.sdiff_subset : xs.toFinset\a⊆xs.toFinset)) dis
  intro p n
  rw [full]
  have bd : p.val*7+n.val<160 := by omega
  have bit : (unionSep false (xs.map wide)).getLsbD (p.val*7+n.val)=true := by
    rw [cov]; simp only [top,BitVec.getLsbD_allOnes,bd,decide_true]
  obtain ⟨w,hw,yes⟩ := (reports_one xs p n).mp bit
  exact ⟨w,List.mem_toFinset.mpr hw,yes⟩

#print axioms possible_yes
#print axioms single_possible
end CoNum4358.Tiny.ShareGrid
