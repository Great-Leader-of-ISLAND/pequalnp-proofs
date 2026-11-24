import PEqualNP.Co5339Pad
import PEqualNP.CoThinCross2008

namespace Co5339Fiber

noncomputable section
open Classical

variable {N q s : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def negative (y : Side N) : Side N := fun p => decide (¬∃l,I p l ∧ y l=true)

def positive (out : Set (Input N)) := ∀p l,I p l → (atom p,atom l)∈out
def correctNegative (q : ℕ) (out : Set (Input N)) :=
  ∀y : Side N,Fintype.card {l // y l=true}≤q → (negative I y,y)∉out

def clean (W : ℕ → Set (Input N)) (o s : ℕ) : Set (Fin N × Fin N) :=
  {e | I e.1 e.2 ∧ ∃j<s,W (N+N+j)⊆W o ∧ (atom e.1,atom e.2)∈W (N+N+j) ∧
    ∃a b,max a b<N+N+j ∧ W (N+N+j)=W a∩W b ∧ ∃P L : Set (Side N),W a=P×ˢSet.univ ∧ W b=Set.univ×ˢL}

theorem padded_sparse_spec {W : ℕ → Set (Input N)} {o : ℕ} (fits : q<N) (base : Bases W)
    (hq : 0<q) (pos : positive I (W o)) (neg : correctNegative I q (W o)) :
    positive I (padded q W (slot N q o)) ∧ correctNegative I q (padded q W (slot N q o)) := by
  rw [pad_slot base]
  constructor
  · intro p l inc
    have card : Fintype.card {j // atom l j=true}≤q := by simpa [atom] using hq
    change raiseInputs N q (atom p,atom l) ∈ W o
    rw [sparse_raise fits _ _ card]
    exact pos p l inc
  · intro y hy
    change raiseInputs N q (negative I y,y)∉W o
    rw [sparse_raise fits _ _ hy]
    exact neg y hy

theorem no_clean {W : ℕ → Set (Input N)} {o : ℕ} (fits : q<N) (base : Bases W)
    (old : ∀i<s,LegalAt W (N+N+i)) (hq : 0<q)
    (neg : correctNegative I q (padded q W (slot N q o))) :
    clean I (padded q W) (slot N q o) (q+N+s)=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨_,j,hj,inside,hit,a,b,_,op,P,L,pa,lb⟩ := he
  have rect : padded q W (N+N+j)=P×ˢL := by
    rw [op,pa,lb]
    ext v
    simp
  have card : Fintype.card {r // atom e.2 r=true}≤q := by simpa [atom] using hq
  exact fiber_no_clean _ _ (pad_gate_fiber fits base old hj) inside P L rect e.1 e.2 _ (neg _ card) hit

/-- Each of the other N-1 points lies on one of the lines through p, and each line contributes q other points. -/
theorem point_count {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0<q) (hN : N=q^2+q+1)
    (deg : ∀l,Fintype.card {p // I p l}=q+1)
    (joined : ∀p r,p≠r → ∃!l,I p l ∧ I r l) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card=q+1 := by
  classical
  let ls := CoThinCross2008.lines I p
  let rest := fun l => (CoThinCross2008.pts I l).erase p
  have cardline (l) : (CoThinCross2008.pts I l).card=q+1 := by simpa [CoThinCross2008.pts,Fintype.card_subtype] using deg l
  have each (l) (hl : l∈ls) : (rest l).card=q := by
    have mem : p∈CoThinCross2008.pts I l := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
    simp [rest,Finset.card_erase_of_mem mem,cardline]
  have cover : Finset.univ.erase p ⊆ ls.biUnion rest := by
    intro r hr
    have rp := (Finset.mem_erase.mp hr).1
    obtain ⟨l,hl,_⟩ := joined r p rp
    refine Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.2⟩,?_⟩
    exact Finset.mem_erase.mpr ⟨rp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.1⟩⟩
  have count : N-1 ≤ ls.card*q := by
    calc N-1 = (Finset.univ.erase p).card := by simp
         _ ≤ (ls.biUnion rest).card := Finset.card_le_card cover
         _ ≤ ∑l∈ls,(rest l).card := Finset.card_biUnion_le
         _ = ∑_l∈ls,q := Finset.sum_congr rfl each
         _ = ls.card*q := by simp
  have le := CoThinCross2008.point_degree I hq hN cardline joined p
  change ls.card=q+1
  change ls.card≤q+1 at le
  have lower : q+1≤ls.card := by
    by_contra h
    have bad : ls.card≤q := by omega
    have m := Nat.mul_le_mul_right q bad
    have n : 0<N := by omega
    have e : N-1+1=N := by omega
    nlinarith
  omega

theorem price151 (q N s : ℕ) (large : 100<q) (plane : N=q^2+q+1)
    (essential : N+N≤s+1) (paddedPrice : N*q≤100*(q+N+s)) : N*q≤151*s := by
  have sq := Nat.mul_le_mul_right q (by omega : 101≤q)
  nlinarith

end
end Co5339Fiber
