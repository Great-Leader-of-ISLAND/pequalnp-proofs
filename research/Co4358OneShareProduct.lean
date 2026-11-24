import PEqualNP.Co4358OneShare

namespace CoAO3143.OneShare
open ProtocolProof
open Cotree (leftChoice)

def F.pick (z : Sig) (p n : Row) : F → Option Sig
  | .atom a => some a
  | .port => none
  | .fork d l r => if leftChoice d (l.val z) p n then l.pick z p n else r.pick z p n

theorem pick_mem (e : F) (z : Sig) (p n : Row) {a : Sig} (eq : e.pick z p n=some a) :
    a∈e.vars := by
  induction e with
  | atom u => simpa [F.pick,F.vars,eq_comm] using eq
  | port => contradiction
  | fork d l r ih jh =>
    simp only [F.pick] at eq
    change a∈l.vars++r.vars
    split at eq
    · exact List.mem_append_left _ (ih eq)
    · exact List.mem_append_right _ (jh eq)

def selected (z : Sig) : Option Sig → Sig
  | none => z
  | some a => a

private theorem bop (s d : Bool) (r : Row) (a b : Sig) :
    bit s r (bin d a b) = if d then bit s r a || bit s r b else bit s r a && bit s r b := by
  cases s <;> cases d <;> simp [bit,bin,BitVec.getLsbD_or,BitVec.getLsbD_and]

theorem pick_valid (e : F) (z : Sig) (p n : Row) (yes : separates p n (e.val z)) :
    separates p n (selected z (e.pick z p n)) := by
  induction e with
  | atom _ => exact yes
  | port => exact yes
  | fork d l r ih jh =>
    obtain ⟨hp,hn⟩ := yes
    change bit true p (bin d (l.val z) (r.val z))=true at hp
    change bit false n (bin d (l.val z) (r.val z))=false at hn
    rw [bop] at hp hn
    cases d <;> cases pl : bit true p (l.val z) <;> cases nl : bit false n (l.val z) <;>
      simp only [F.pick,leftChoice,Bool.false_eq_true,↓reduceIte,pl,nl,Bool.not_false,Bool.not_true] <;>
      first | exact ih (by simp_all [separates]) | exact jh (by simp_all [separates])

theorem target_always (p n : Row) : separates p n target := by
  constructor
  · change (BitVec.allOnes 160).getLsbD p.val=true
    rw [BitVec.getLsbD_allOnes]
    simp only [p.isLt,decide_true]
  · simp [bit,target]

def Miss (X : Finset Sig) (p n : Row) := ∀a∈X,¬separates p n a
def Factor.inside {S} (f : Factor S) := f.inner.vars.toFinset
def Factor.outside {S} (f : Factor S) := f.outer.vars.toFinset

theorem closed_input (e : F) (no : e.ports=0) : e.vars.toFinset.Nonempty := by
  induction e with
  | atom a => exact ⟨a,by simp [F.vars]⟩
  | port => simp [F.ports] at no
  | fork d l r ih jh =>
    change l.ports+r.ports=0 at no
    obtain ⟨a,ha⟩ := ih (by omega)
    exact ⟨a,List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp ha))⟩

theorem partition {S} (f : Factor S) : f.inside ∪ f.outside=S ∧ Disjoint f.inside f.outside := by
  constructor
  · simpa [Factor.inside,Factor.outside] using f.sources
  · rw [Finset.disjoint_left]
    have dis := List.disjoint_left.mp (List.disjoint_of_nodup_append f.distinct)
    intro a ha hb
    exact dis (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)

theorem inside_requires {S} (f : Factor S) (p n : Row) (no : Miss f.outside p n) :
    separates p n (f.inner.val zero) := by
  let z := f.inner.val zero
  have yes : separates p n (f.outer.val z) := by rw [show f.outer.val z=target from f.value]; exact target_always p n
  have step := pick_valid f.outer z p n yes
  cases eq : f.outer.pick z p n with
  | none => simpa [eq,selected] using step
  | some a =>
    have mem : a∈f.outside := List.mem_toFinset.mpr (pick_mem _ _ _ _ eq)
    exact False.elim (no a mem (by simpa [eq,selected] using step))

theorem inside_cross {S} (f : Factor S) {p p' n n' : Row}
    (hp : Miss f.outside p n') (hn : Miss f.outside p' n) :
    separates p n (f.inner.val zero) :=
  ⟨(inside_requires f p n' hp).1,(inside_requires f p' n hn).2⟩

theorem inside_answer {S} (f : Factor S) {p n : Row} (yes : separates p n (f.inner.val zero)) :
    ∃ a∈f.inside, f.inner.pick zero p n=some a ∧ separates p n a := by
  have data := pick_valid f.inner zero p n yes
  cases eq : f.inner.pick zero p n with
  | none =>
    have no : separates p n zero := by simpa [eq,selected] using data
    exact False.elim (by simpa [separates,bit,zero] using no)
  | some a => exact ⟨a,List.mem_toFinset.mpr (pick_mem _ _ _ _ eq),rfl,by simpa [eq,selected] using data⟩

theorem outside_answer {S} (f : Factor S) {p n : Row} (no : Miss f.inside p n) :
    ∃ a∈f.outside, f.outer.pick (f.inner.val zero) p n=some a ∧ separates p n a := by
  let z := f.inner.val zero
  have yes : separates p n (f.outer.val z) := by rw [show f.outer.val z=target from f.value]; exact target_always p n
  have data := pick_valid f.outer z p n yes
  cases eq : f.outer.pick z p n with
  | none =>
    have zin : separates p n (f.inner.val zero) := by simpa [eq,selected,z] using data
    obtain ⟨a,ha,_,valid⟩ := inside_answer f zin
    exact False.elim (no a ha valid)
  | some a => exact ⟨a,List.mem_toFinset.mpr (pick_mem _ _ _ _ eq),rfl,by simpa [eq,selected] using data⟩

end CoAO3143.OneShare
