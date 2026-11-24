import PEqualNP.Co4358ShareGrid
import PEqualNP.Co4358FastCorners

namespace CoNum4358.Tiny.ShareGrid
open CoAO3143
set_option maxRecDepth 65536

def Covered (X : Finset K) (D : Fin 8 → Fin 7 → Prop) :=
  ∀p n,D p n → ∃w∈X,directed w p n=true

theorem outer_covered {A B : Finset K} (all : ∀p n,∃w∈A∪B,directed w p n=true) :
    Covered B (FreeCell A) := by
  intro p n miss
  obtain ⟨a,am,hit⟩ := all p n
  refine ⟨a,(Finset.mem_union.mp am).resolve_left ?_,hit⟩
  intro ha
  exact Bool.false_ne_true ((miss a ha).symm.trans hit)

private theorem two_linked {R : K→K→Prop} {a b : K} (edge : R a b) :
    Linked R ({a,b} : Finset K) := by
  intro c mono x hx y hy
  have eq := mono a (by simp) b (by simp) edge
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with xa|xb <;> rcases hy with ya|yb <;> simp_all only

/-- On a viable local domain, two distinct locally forced leaves cannot
share both a positive input row and a negative input column. -/
theorem no_rectangle {X : Finset K} {D : Fin 8→Fin 7→Prop}
    (apart : Compatible X D) (cover : Covered X D) (r : Rect)
    (pA : D r.p r.m₁) (aP : Owner X r.p r.m₁ r.a)
    (nA : D r.q₁ r.n) (aN : Owner X r.q₁ r.n r.a)
    (pB : D r.p r.m₂) (bP : Owner X r.p r.m₂ r.b)
    (nB : D r.q₂ r.n) (bN : Owner X r.q₂ r.n r.b) : r.a=r.b := by
  have exists_owner (p n a) (h : D p n) (o : Owner X p n a) : a∈X := by
    obtain ⟨w,hw,yes⟩ := cover _ _ h
    simpa only [o w hw yes] using hw
  have ma := exists_owner _ _ _ pA aP
  have mb := exists_owner _ _ _ pB bP
  have sub : ({r.a,r.b} : Finset K)⊆X := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    obtain hv|hv := hv
    · simpa only [hv] using ma
    · simpa only [hv] using mb
  apply apart _ sub _ _ (by simp) _ (by simp)
  intro d
  apply two_linked
  cases d
  · exact ⟨r.n,r.q₁,r.q₂,nA,aN,nB,bN⟩
  · exact ⟨r.p,r.m₁,r.m₂,pA,aP,pB,bP⟩

theorem free_shrink {X Y : Finset K} (sub : X⊆Y) {p n} (h : FreeCell Y p n) :
    FreeCell X p n := fun a ha => h a (sub ha)

theorem required_shrink {X Y : Finset K} (sub : X⊆Y) {p n} (h : Required Y p n) :
    Required X p n := by
  obtain ⟨⟨m,hm⟩,⟨q,hq⟩⟩ := h
  exact ⟨⟨m,free_shrink sub hm⟩,⟨q,free_shrink sub hq⟩⟩

theorem owner_shrink {X Y : Finset K} (sub : X⊆Y) {p n a} (h : Owner Y p n a) :
    Owner X p n a := fun b hb => h b (sub hb)

def cov (xs : List K) := (Corners.counts xs).1
def noBit (s : Nat) (p : Fin 8) (n : Fin 7) := !s.testBit (p.val*7+n.val)

theorem noBit_free {xs : List K} {p n} (h : noBit (cov xs) p n=true) : FreeCell xs.toFinset p n := by
  intro a ha
  apply Bool.eq_false_iff.mpr
  intro yes
  have sep := Corners.seen (List.mem_toFinset.mp ha) (p.val*7+n.val) (by rwa [Masks.cells_bit])
  have no : (cov xs).testBit (p.val*7+n.val)=false := Bool.not_eq_true'.mp h
  exact Bool.false_ne_true (no.symm.trans sep)

/-- The bit arithmetic proposes two witnesses. Their membership in the true
pair domain is checked using the actual row/column coordinates. -/
def productBit (s : Nat) (p : Fin 8) (n : Fin 7) : Bool :=
  let uncovered := fullMask ^^^ s
  let m := Fin.ofNat 7 (((uncovered >>> (p.val*7)) &&& 127).log2)
  let q := Fin.ofNat 8 (((uncovered &&& (columnMask <<< n.val)).log2)/7)
  noBit s p m && noBit s q n

theorem productBit_required {xs : List K} {p n} (h : productBit (cov xs) p n=true) :
    Required xs.toFinset p n := by
  let mask := fullMask ^^^ cov xs
  let m := Fin.ofNat 7 (((mask >>> (p.val*7)) &&& 127).log2)
  let q := Fin.ofNat 8 (((mask &&& (columnMask <<< n.val)).log2)/7)
  change (noBit (cov xs) p m && noBit (cov xs) q n)=true at h
  obtain ⟨hp,hn⟩ := Bool.and_eq_true.mp h
  exact ⟨⟨m,noBit_free hp⟩,⟨q,noBit_free hn⟩⟩

theorem forced_owner {xs : List K} {p n a} (h : forced xs p n a=true) :
    Owner xs.toFinset p n a := by
  intro b hb yes
  have eq := List.all_eq_true.mp h b (List.mem_toFinset.mp hb)
  obtain ⟨hp,hn⟩ := Bool.and_eq_true.mp yes
  have no := Bool.not_eq_true'.mp hn
  simpa [hp,no] using eq

def rectBit (xs : List K) (dom : Fin 8→Fin 7→Bool) (r : Rect) :=
  validRect xs r && dom r.p r.m₁ && dom r.q₁ r.n && dom r.p r.m₂ && dom r.q₂ r.n

theorem rectBit_false {X : Finset K} {xs : List K} (sub : X⊆xs.toFinset)
    {D : Fin 8→Fin 7→Prop} (apart : Compatible X D) (cover : Covered X D)
    {dom : Fin 8→Fin 7→Bool} (valid : ∀p n, dom p n=true → D p n) (r : Rect) :
    rectBit xs dom r=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [rectBit,validRect,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ne,ap⟩,an⟩,bp⟩,bn⟩,pa⟩,na⟩,pb⟩,nb⟩ := h
  exact ne (no_rectangle apart cover r (valid _ _ pa) (owner_shrink sub (forced_owner ap))
    (valid _ _ na) (owner_shrink sub (forced_owner an))
    (valid _ _ pb) (owner_shrink sub (forced_owner bp))
    (valid _ _ nb) (owner_shrink sub (forced_owner bn)))

#print axioms rectBit_false
end CoNum4358.Tiny.ShareGrid
