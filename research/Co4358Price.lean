import PEqualNP.Co4358Cone
import PEqualNP.CoPhysical4358

namespace CoNum4358.KWPrice
open CoAO3143 CoThetaFreeCore CoThetaNine

def pRow : Fin 8 → SmallInput := ![9,5,24,33,6,96,18,66]
def nRow : Fin 7 → SmallInput := ![76,81,84,44,52,3,42]
def below (r s : SmallInput) : Prop := ∀ j : Fin 7, raw7 j r = true → raw7 j s = true
local instance (r s : SmallInput) : Decidable (below r s) := by unfold below; infer_instance
def rising (f : SmallInput → Bool) := ∀ r s, below r s → f r = true → f s = true

def fits (w : Sig) (f : SmallInput → Bool) : Prop :=
  (∀ p : Fin 8, f (pRow p) = w.1.getLsbD (7*p.val)) ∧
  (∀ n : Fin 7, f (nRow n) = w.2.getLsbD n.val)

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem boundary : ∀ r : SmallInput,
    (ans7 r = true → ∃ p : Fin 8, below (pRow p) r) ∧
    (ans7 r = false → ∃ n : Fin 7, below r (nRow n)) := by decide +kernel

theorem unique (f : SmallInput → Bool) (hf : rising f) (eq : fits CoAO3143.target f) :
    f = ans7 := by
  funext r
  obtain ⟨pos,neg⟩ := boundary r
  cases h : ans7 r with
  | true =>
    obtain ⟨p,le⟩ := pos h
    have i : 7*p.val < 160 := by have := p.isLt; omega
    have on := eq.1 p
    change f (pRow p) = (BitVec.allOnes 160).getLsbD (7 * p.val) at on
    simp only [BitVec.getLsbD_allOnes,i,decide_true] at on
    exact hf _ _ le on
  | false =>
    obtain ⟨n,le⟩ := neg h
    have off := eq.2 n
    simp [CoAO3143.target] at off
    cases val : f r with
    | false => rfl
    | true => exact Bool.noConfusion ((hf _ _ le val).symm.trans off)

private theorem rise_op (b : Bool) (f g : SmallInput → Bool) (hf : rising f) (hg : rising g) :
    rising (fun i => base b (f i) (g i)) := by
  intro r s le h
  have x := hf r s le
  have y := hg r s le
  cases e₁ : f r <;> cases e₂ : f s <;> cases e₃ : g r <;> cases e₄ : g s <;>
    cases b <;> simp_all [base]

private theorem fit_op (b : Bool) {u v : Sig} {f g : SmallInput → Bool} (hf : fits u f)
    (hg : fits v g) : fits (bin b u v) (fun i => base b (f i) (g i)) := by
  constructor
  · intro i
    cases b <;> simp only [base,bin,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_or,
      BitVec.getLsbD_and,hf.1 i,hg.1 i]
  · intro i
    cases b <;> simp only [base,bin,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_or,
      BitVec.getLsbD_and,hf.2 i,hg.2 i]

def model (fs : List (SmallInput → Bool)) (w : Sig) :=
  ∃ f∈fs, rising f ∧ fits w f

private theorem keep {fs f w} (h : model fs w) : model (f::fs) w := by
  obtain ⟨g,hg,r,e⟩ := h
  exact ⟨g,List.mem_cons_of_mem _ hg,r,e⟩

private theorem cfit : fits zero (fun _ => false) ∧ fits one (fun _ => true) := by
  unfold fits
  decide +kernel

private theorem inputs : ∀ i : Fin 7, fits (rawKW.getD i.val zero) (raw i) := by
  unfold fits
  decide +kernel

private theorem reflect_run {k ws} (r : Run rawKW k ws) :
    ∃ fs, Ordinary seed k fs ∧ ∀ w, OK ws w → model fs w := by
  induction r with
  | start =>
    refine ⟨seed,Ordinary.start,?_⟩
    intro w hw
    rcases hw with rfl|rfl|m
    · exact ⟨_,constants false,fun _ _ _ => id,cfit.1⟩
    · exact ⟨_,constants true,fun _ _ _ => id,cfit.2⟩
    · obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp m
      have lim : i<7 := by simpa only [show rawKW.length=7 by decide] using hi
      let j : Fin 7 := ⟨i,lim⟩
      have e : rawKW.getD j.val zero = w := by
        change rawKW.getD i zero=w
        simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using eq
      exact ⟨raw j,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨j,rfl⟩)),
        fun x y le h => le (ren j) h, e ▸ inputs j⟩
  | @add k bank a b pre d ha hb ih =>
    obtain ⟨fs,prog,lookup⟩ := ih
    obtain ⟨f,mf,rf,ef⟩ := lookup _ ha
    obtain ⟨g,mg,rg,eg⟩ := lookup _ hb
    refine ⟨_,Ordinary.binary prog d mf mg,?_⟩
    intro w hw
    rcases hw with eq|eq|m
    · exact keep (lookup _ (Or.inl eq))
    · exact keep (lookup _ (Or.inr (Or.inl eq)))
    · rcases List.mem_cons.mp m with rfl|old
      · exact ⟨_,List.mem_cons_self,rise_op _ _ _ rf rg,fit_op _ ef eg⟩
      · exact keep (lookup _ (Or.inr (Or.inr old)))

theorem lower (price : SignedLower) : Price rawKW 11 := by
  intro k ws run goal
  obtain ⟨fs,prog,lookup⟩ := reflect_run run
  obtain ⟨f,m,r,e⟩ := lookup _ goal
  have eq := unique f r e
  obtain ⟨zs,hz,all⟩ := normalized prog
  have mem := all _ m
  rw [eq] at mem
  have z : norm (0 : SmallInput) ans7=ans7 := by
    have b : ans7 0=false := by decide +kernel
    funext u
    simp [CoThetaFreeCore.norm,phase,b]
  rw [z] at mem
  exact price hz mem

#print axioms lower
end CoNum4358.KWPrice
