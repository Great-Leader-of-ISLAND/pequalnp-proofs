import Mathlib
import PEqualNP.CoThetaNineTriple

namespace CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

noncomputable def readerSet {ρ : Type} (gs : List (TraceGate ρ)) (p : ρ → Bool) :
    Finset (TraceGate ρ) := by classical exact gs.toFinset.filter (fun g => reads g p)

theorem mem_readerSet {ρ : Type} {gs : List (TraceGate ρ)} {p : ρ → Bool}
    {g : TraceGate ρ} : g ∈ readerSet gs p ↔ g ∈ gs ∧ reads g p := by
  classical
  simp [readerSet]

/-- For the nonedge head, p has two readers including a head that does not read q.
Any gate reading both raw inputs masks q on one slice, forcing its second reader. -/
theorem three_readers_separate_head {α : Type} [DecidableEq α] (P Q : Finset α)
    (twoP : 2 ≤ P.card) (someQ : Q.Nonempty) (head : ∃ g ∈ P, g ∉ Q)
    (shared : ∀ g ∈ P, g ∈ Q → 2 ≤ Q.card) : 3 ≤ (P ∪ Q).card := by
  classical
  by_cases both : ∃ g ∈ P, g ∈ Q
  · obtain ⟨g,hg,hq⟩ := both
    obtain ⟨h,hp,hn⟩ := head
    have sub : insert h Q ⊆ P ∪ Q := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_union_left _ hp
      · exact Finset.mem_union_right _ hv
    have hc := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem hn] at hc
    have low := shared g hg hq
    omega
  · obtain ⟨q,hq⟩ := someQ
    have out : q ∉ P := fun hp => both ⟨q,hp,hq⟩
    have sub : insert q P ⊆ P ∪ Q := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_union_right _ hq
      · exact Finset.mem_union_left _ hv
    have hc := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem out] at hc
    omega

/-- Path in the given semantic trace, through reads of actual gate operands. -/
inductive UsePath {ρ : Type} (gs : List (TraceGate ρ)) :
    (ρ → Bool) → (ρ → Bool) → Prop
  | stop {w} : UsePath gs w w
  | through {w out} (g : TraceGate ρ) (mem : g ∈ gs) (input : reads g w)
      (rest : UsePath gs g.value out) : UsePath gs w out

private theorem two_reads_zero {ρ σ : Type} (lift : σ → ρ)
    {g : TraceGate ρ} {w p : ρ → Bool} (ne : w ≠ p) (hw : reads g w) (hp : reads g p)
    (zw : restrict lift w = absentBit) (zp : restrict lift p = absentBit) :
    restrict lift g.value = absentBit := by
  apply two_zero_propagate
  · rcases hw with h|h <;> rcases hp with h'|h'
    · exact (ne (h.symm.trans h')).elim
    · exact (congrArg (restrict lift) h).trans zw
    · exact (congrArg (restrict lift) h').trans zp
    · exact (ne (h.symm.trans h')).elim
  · rcases hw with h|h <;> rcases hp with h'|h'
    · exact (ne (h.symm.trans h')).elim
    · exact (congrArg (restrict lift) h').trans zp
    · exact (congrArg (restrict lift) h).trans zw
    · exact (ne (h.symm.trans h')).elim

/-- A path starting at a projected-zero signal and ending at a nonzero target
must lose another gate outside the two raw-reader sets. Freshness is only needed
for exact raw-function aliases along the path, because a semantic reader records
values rather than pin indices. -/
theorem extra_loss_on_path {ρ σ : Type} (lift : σ → ρ) {gs : List (TraceGate ρ)}
    {p q z out : ρ → Bool} (zp : restrict lift p = absentBit) (zq : restrict lift q = absentBit)
    (aliasFree : ∀ g ∈ gs, g.value ≠ p ∧ g.value ≠ q)
    (path : UsePath gs z out) (zz : restrict lift z = absentBit)
    (distinct : z ≠ p ∧ z ≠ q) (ends : restrict lift out ≠ absentBit) :
    ∃ g ∈ gs, ¬reads g p ∧ ¬reads g q ∧ disappears lift g := by
  induction path with
  | stop => exact (ends zz).elim
  | @through w out g hg hw more ih =>
    by_cases hp : reads g p
    · exact ih (two_reads_zero lift distinct.1 hw hp zz zp) (aliasFree g hg) ends
    by_cases hq : reads g q
    · exact ih (two_reads_zero lift distinct.2 hw hq zz zq) (aliasFree g hg) ends
    exact ⟨g,hg,hp,hq,reading_zero_disappears lift zz hw⟩

private noncomputable def lostList {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ)) :
    List (TraceGate ρ) := by classical exact gs.filter (fun g => decide (disappears lift g))

private theorem lost_length {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ)) :
    (lostList lift gs).length = saved lift gs := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [lostList,saved,h,lostList] at ih ⊢ <;> omega

theorem four_saved_raw_head {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ))
    (p q : ρ → Bool) (zp : restrict lift p = absentBit) (zq : restrict lift q = absentBit)
    (three : 3 ≤ (readerSet gs p ∪ readerSet gs q).card)
    (extra : ∃ g ∈ gs, ¬reads g p ∧ ¬reads g q ∧ disappears lift g) :
    4 ≤ saved lift gs := by
  classical
  obtain ⟨g,hg,hp,hq,hd⟩ := extra
  let A := readerSet gs p ∪ readerSet gs q
  have hout : g ∉ A := by
    intro h
    rcases Finset.mem_union.mp h with h|h
    · exact hp (mem_readerSet.mp h).2
    · exact hq (mem_readerSet.mp h).2
  have sub : insert g A ⊆ (lostList lift gs).toFinset := by
    intro v hv
    have hv' : v∈gs ∧ disappears lift v := by
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact ⟨hg,hd⟩
      · rcases Finset.mem_union.mp hv with h|h
        · obtain ⟨hm,hr⟩ := mem_readerSet.mp h
          exact ⟨hm,reading_zero_disappears lift zp hr⟩
        · obtain ⟨hm,hr⟩ := mem_readerSet.mp h
          exact ⟨hm,reading_zero_disappears lift zq hr⟩
    simpa [lostList] using hv'
  have bound := (Finset.card_le_card sub).trans (List.toFinset_card_le _)
  rw [Finset.card_insert_of_notMem hout,lost_length] at bound
  change 3 ≤ A.card at three
  omega

end CoThetaFreeCore

namespace CoThetaFreeCore

theorem UsePath.trans {ρ : Type} {chain : List (TraceGate ρ)} {a b c : ρ → Bool}
    (first : UsePath chain a b) (last : UsePath chain b c) : UsePath chain a c := by
  induction first with
  | stop => exact last
  | through g hg hr _ ih => exact .through g hg hr (ih last)

/-- Recompute every wire not reachable from z, completely omitting the source z
itself. The returned signed binary program has at most the old suffix cost. -/
theorem omit_path_scan {ρ : Type} (chain : List (TraceGate ρ)) (z : ρ → Bool)
    (gs : List (TraceGate ρ)) (sub : ∀ g∈gs, g∈chain)
    {raw start pool : List (ρ → Bool)} {b : Nat}
    (reg : registered start gs) (pre : Free raw b pool)
    (known : ∀ w∈start, ¬UsePath chain z w → w∈pool) :
    ∃ j ys, j ≤ b+gs.length ∧ Free raw j ys ∧
      ∀ w∈traceWires start gs, ¬UsePath chain z w → w∈ys := by
  induction gs generalizing start pool b with
  | nil => exact ⟨b,pool,by simp,pre,known⟩
  | cons g gs ih =>
    obtain ⟨hl,hr,rest⟩ := reg
    have hg := sub g List.mem_cons_self
    have tail (v) (hv : v∈gs) := sub v (List.mem_cons_of_mem _ hv)
    by_cases path : UsePath chain z g.value
    · have carry : ∀ w∈g.value::start, ¬UsePath chain z w → w∈pool := by
        intro w hw hn
        rcases List.mem_cons.mp hw with rfl|hw
        · exact (hn path).elim
        · exact known _ hw hn
      obtain ⟨j,ys,hj,run,avail⟩ := ih tail rest pre carry
      exact ⟨j,ys,by simp; omega,run,avail⟩
    · have pl : ¬UsePath chain z g.left := fun p =>
        path (p.trans (.through g hg (Or.inl rfl) .stop))
      have pr : ¬UsePath chain z g.right := fun p =>
        path (p.trans (.through g hg (Or.inr rfl) .stop))
      have next : Free raw (b+1) (g.value::pool) :=
        .binary pre g.kind (known _ hl pl) (known _ hr pr)
      have carry : ∀ w∈g.value::start, ¬UsePath chain z w → w∈g.value::pool := by
        intro w hw hn
        rcases List.mem_cons.mp hw with rfl|hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (known _ hw hn)
      obtain ⟨j,ys,hj,run,avail⟩ := ih tail rest next carry
      exact ⟨j,ys,by simp; omega,run,avail⟩

theorem omit_dead_head {ρ : Type} (raw : List (ρ → Bool))
    (gs : List (TraceGate ρ)) (z target : ρ → Bool)
    (reg : registered (z::raw) gs) (out : target∈traceWires (z::raw) gs)
    (dead : ¬UsePath gs z target) :
    ∃ j ys, j ≤ gs.length ∧ Free raw j ys ∧ target∈ys := by
  have known (w) (hw : w∈z::raw) (hn : ¬UsePath gs z w) : w∈raw := by
    rcases List.mem_cons.mp hw with rfl|hw
    · exact (hn .stop).elim
    · exact hw
  obtain ⟨j,ys,hj,run,avail⟩ := omit_path_scan gs z gs (fun _ h => h) reg (Free.start (raw:=raw)) known
  exact ⟨j,ys,by simpa using hj,run,avail _ out dead⟩

end CoThetaFreeCore

namespace CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

private theorem masked_setting {ρ : Type} (g : TraceGate ρ) (p : ρ → Bool) (hp : reads g p) :
    ∃ b : Bool, ∀ r s, p r=b → p s=b → g.value r = g.value s := by
  obtain ⟨k,l,r⟩ := g
  rcases hp with h|h
  · change l=p at h
    subst l
    have valid : ∀ k : Kind, ∃ b : Bool, ∀ a c : Bool, applyKind k b a = applyKind k b c := by
      intro j
      cases j <;> decide
    obtain ⟨b,f⟩ := valid k
    exact ⟨b,fun x y hx hy => by simp only [TraceGate.value,hx,hy]; exact f _ _⟩
  · change r=p at h
    subst r
    have valid : ∀ k : Kind, ∃ b : Bool, ∀ a c : Bool, applyKind k a b = applyKind k c b := by
      intro j
      cases j <;> decide
    obtain ⟨b,f⟩ := valid k
    exact ⟨b,fun x y hx hy => by simp only [TraceGate.value,hx,hy]; exact f _ _⟩

/-- Instantiate this for p=0, q=4, head=(0 AND 3). The geometric data use just
one masked row pair at the head and two row pairs for q, one per setting of p. -/
theorem nonedge_head_dichotomy {ρ σ : Type} (lift : σ → ρ)
    (raw : List (ρ → Bool)) (head : TraceGate ρ) (gs : List (TraceGate ρ))
    (p q out : ρ → Bool)
    (reg : registered raw (head::gs)) (solves : out∈traceWires raw (head::gs))
    (hrp : reads head p) (hrq : ¬reads head q)
    (outp : out≠p) (outq : out≠q)
    (pTest : ∃ r s, agreeOutside (·=p) r s raw ∧ out r≠out s ∧ head.value r=head.value s)
    (qTest : ∀ b : Bool, ∃ r s, agreeOutside (·=q) r s raw ∧ out r≠out s ∧ p r=b ∧ p s=b)
    (zp : restrict lift p=absentBit) (zq : restrict lift q=absentBit)
    (zh : restrict lift head.value=absentBit) (endNZ : restrict lift out≠absentBit)
    (headNew : head.value≠p ∧ head.value≠q)
    (fresh : ∀ g∈gs, g.value≠p ∧ g.value≠q) :
    (∃ j ys, j ≤ gs.length ∧ Free raw j ys ∧ out∈ys) ∨ 4 ≤ saved lift (head::gs) := by
  classical
  by_cases alive : UsePath gs head.value out
  case neg =>
    exact Or.inl (omit_dead_head raw gs head.value out reg.2.2 solves alive)
  case pos =>
    right
    apply four_saved_raw_head lift (head::gs) p q zp zq
    · apply three_readers_separate_head
      · obtain ⟨r,s,hs,hd,hm⟩ := pTest
        obtain ⟨g,hg,hp,ne⟩ := second_reader p r s head reg hs solves outp hd hm
        apply Finset.one_lt_card.mpr
        exact ⟨g,mem_readerSet.mpr ⟨hg,hp⟩,head,mem_readerSet.mpr ⟨List.mem_cons_self,hrp⟩,ne⟩
      · obtain ⟨r,s,hs,hd,_,_⟩ := qTest false
        obtain ⟨g,hg,read,_⟩ := reader_witness (·=q) r s reg hs solves outq hd
        exact ⟨g,mem_readerSet.mpr ⟨hg,read⟩⟩
      · exact ⟨head,mem_readerSet.mpr ⟨List.mem_cons_self,hrp⟩,fun h => hrq (mem_readerSet.mp h).2⟩
      · intro g hgP hgQ
        obtain ⟨b,hm⟩ := masked_setting g p (mem_readerSet.mp hgP).2
        obtain ⟨r,s,hs,hd,hpR,hpS⟩ := qTest b
        obtain ⟨other,hOther,readsQ,ne⟩ := second_reader q r s g reg hs solves outq hd (hm r s hpR hpS)
        apply Finset.one_lt_card.mpr
        exact ⟨other,mem_readerSet.mpr ⟨hOther,readsQ⟩,g,hgQ,ne⟩
    · obtain ⟨g,hg,hp,hq,hd⟩ := extra_loss_on_path lift zp zq fresh alive zh headNew endNZ
      exact ⟨g,List.mem_cons_of_mem _ hg,hp,hq,hd⟩

end CoThetaFreeCore

namespace CoThetaNine
open CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

def slice04 (r : Fin 128) : Input := row (CoPetersenThetaGeometry.plant 0 r.val)
def or04 : TraceGate Input := ⟨.disj,vtx 0,vtx 4⟩
def and03 : TraceGate Input := ⟨.conj,vtx 0,vtx 3⟩

def fixedHeadResult (gate : TraceGate Input) (gs : List (TraceGate Input)) : Prop :=
  (∃ n ys, n ≤ gs.length ∧ Free vertices n ys ∧ ans∈ys) ∨
  ∃ ts, ts.length≤gs.length ∧ sufficient vertices ans (gate::ts) ∧ 4≤saved slice04 (gate::ts)

private theorem threeSet {gs : List (TraceGate Input)} {p q : Input→Bool}
    (h : ThreeReaders (fun g => reads g p ∨ reads g q) gs) :
    3 ≤ (readerSet gs p ∪ readerSet gs q).card := by
  classical
  obtain ⟨a,ha,b,hb,c,hc,ra,rb,rc,ab,ac,bc⟩ := h
  let S := readerSet gs p ∪ readerSet gs q
  have ins (g : TraceGate Input) (hg : g∈gs) (hr : reads g p ∨ reads g q) : g∈S := by
    rcases hr with r|r
    · exact Finset.mem_union_left _ (mem_readerSet.mpr ⟨hg,r⟩)
    · exact Finset.mem_union_right _ (mem_readerSet.mpr ⟨hg,r⟩)
  have sub : ({a,b,c} : Finset (TraceGate Input)) ⊆ S := by
    intro g hg
    simp only [Finset.mem_insert,Finset.mem_singleton] at hg
    rcases hg with rfl|rfl|rfl
    · exact ins _ ha ra
    · exact ins _ hb rb
    · exact ins _ hc rc
  have bound := Finset.card_le_card sub
  simpa [Finset.card_insert_of_notMem,ab,ac,bc,S] using bound

private theorem fixedHead04 {gate : TraceGate Input} (gs : List (TraceGate Input))
    {j : Fin 9} (different : (0 : Fin 9) ≠ j) (hp : reads gate (vtx 0))
    (hj : reads gate (vtx j)) (headZero : restrict slice04 gate.value = absentBit)
    (headDistinct : gate.value ≠ vtx 0 ∧ gate.value ≠ vtx 4)
    (correct : sufficient vertices ans (gate::gs)) : fixedHeadResult gate gs := by
  classical
  have init : sufficient (gate.value::vertices) ans gs := ⟨correct.1.2.2,correct.2⟩
  obtain ⟨ts,⟨reg,out⟩,fresh,le,_⟩ := simplify_trace gs init
  have well : registered vertices (gate::ts) := ⟨correct.1.1,correct.1.2.1,reg⟩
  have result : ans∈traceWires vertices (gate::ts) := out
  by_cases live : UsePath ts gate.value ans
  · have rz (i : Fin 9) : vtx i∈vertices :=
      List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have pz : restrict slice04 (vtx 0)=absentBit := by
      funext y
      exact (by decide +kernel : ∀ y : Fin 128, vtx 0 (slice04 y)=false) y
    have qz : restrict slice04 (vtx 4)=absentBit := by
      funext y
      exact (by decide +kernel : ∀ y : Fin 128, vtx 4 (slice04 y)=false) y
    have nz : restrict slice04 ans ≠ absentBit := by
      intro e
      exact (by decide : ans (slice04 5) ≠ false) (congrFun e (5 : Fin 128))
    have aliases (g : TraceGate Input) (hg : g∈ts) : g.value≠vtx 0 ∧ g.value≠vtx 4 := by
      have h := fresh_outputs fresh g hg
      exact ⟨fun e => h (List.mem_cons_of_mem _ (e ▸ rz 0)),
             fun e => h (List.mem_cons_of_mem _ (e ▸ rz 4))⟩
    obtain ⟨x,hx,rx,neq⟩ := another_raw_reader different (gate::ts) gate hp hj well result
    have three := three_for_pair 0 well result
      (Or.inl ⟨gate,List.mem_cons_self,x,hx,hp,rx,neq.symm⟩)
    obtain ⟨g,mem,hp',hq',van⟩ := extra_loss_on_path slice04 pz qz aliases live headZero headDistinct nz
    exact Or.inr ⟨ts,le,⟨well,result⟩,four_saved_raw_head slice04 _ _ _ pz qz (threeSet three)
       ⟨g,List.mem_cons_of_mem _ mem,hp',hq',van⟩⟩
  · obtain ⟨n,ws,hn,run,mem⟩ := omit_dead_head vertices ts gate.value ans reg out live
    exact Or.inl ⟨n,ws,hn.trans le,run,mem⟩

theorem fixed_or04 (gs : List (TraceGate Input)) (h : sufficient vertices ans (or04::gs)) :
    fixedHeadResult or04 gs := by
  apply fixedHead04 gs (j:=4) (by decide) (Or.inl rfl) (Or.inr rfl) _ _ h
  · funext y
    exact (by decide +kernel : ∀ y : Fin 128, or04.value (slice04 y)=false) y
  · exact ⟨fun e => (by decide : or04.value (row 16) ≠ vtx 0 (row 16)) (congrFun e (row 16)),
           fun e => (by decide : or04.value (row 1) ≠ vtx 4 (row 1)) (congrFun e (row 1))⟩

theorem fixed_and03 (gs : List (TraceGate Input)) (h : sufficient vertices ans (and03::gs)) :
    fixedHeadResult and03 gs := by
  apply fixedHead04 gs (j:=3) (by decide) (Or.inl rfl) (Or.inr rfl) _ _ h
  · funext y
    exact (by decide +kernel : ∀ y : Fin 128, and03.value (slice04 y)=false) y
  · exact ⟨fun e => (by decide : and03.value (row 1) ≠ vtx 0 (row 1)) (congrFun e (row 1)),
           fun e => (by decide : and03.value (row 16) ≠ vtx 4 (row 16)) (congrFun e (row 16))⟩

end CoThetaNine
