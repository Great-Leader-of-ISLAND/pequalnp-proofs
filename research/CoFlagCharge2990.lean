import Mathlib

namespace CoFlagCharge2990

def takeBit (left a b : Bool) : Bool := if left then a else b
def connective (isOr a b : Bool) : Bool := if isOr then a || b else a && b

/-- One successful extension lights the first input of some previously
all-false upper AND. Source indices 0,...,base-1 are arbitrary shared
functions on the input; each higher gate reads earlier indices only. -/
theorem new_charge (base g : Nat) (left right : Fin g→Nat) (isOr sel : Fin g→Bool)
    (ltL : ∀ j, left j<base+j.val) (ltR : ∀ j, right j<base+j.val)
    (old real approx : Nat→Bool)
    (growing : ∀ i, old i=true → real i=true)
    (sameRaw : ∀ i, i<base → approx i=real i)
    (fixed : ∀ j, isOr j=false → (old (left j) && old (right j))=false →
      takeBit (sel j) (old (left j)) (old (right j))=false)
    (normal : ∀ j, real (base+j.val)=connective (isOr j) (real (left j)) (real (right j)))
    (clause : ∀ j, approx (base+j.val)=
        if isOr j then approx (left j) || approx (right j)
        else takeBit (sel j) (approx (left j)) (approx (right j)))
    (error : ∃ i, i<base+g ∧ approx i≠real i) :
    ∃ j, isOr j=false ∧ old (left j)=false ∧ old (right j)=false ∧
      takeBit (sel j) (real (left j)) (real (right j))=true ∧
      (real (left j) && real (right j))=false := by
  classical
  let k := Nat.find error
  have hk : k<base+g ∧ approx k≠real k := Nat.find_spec error
  have earlier (i : Nat) (less : i<k) : approx i=real i := by
    by_contra h
    exact (Nat.find_min error less) ⟨by omega,h⟩
  have large : base≤k := by
    by_contra! small
    exact hk.2 (sameRaw k small)
  let j : Fin g := ⟨k-base,by omega⟩
  have addr : base+j.val=k := by dsimp [j]; omega
  have l := earlier (left j) (by simpa only [addr] using ltL j)
  have r := earlier (right j) (by simpa only [addr] using ltR j)
  have ne := hk.2
  rw [←addr,clause,normal,l,r] at ne
  refine ⟨j,?_⟩
  have selOld := fixed j
  have gL := growing (left j)
  have gR := growing (right j)
  cases d : isOr j <;> cases c : sel j <;>
    cases a : old (left j) <;> cases b : old (right j) <;>
    cases u : real (left j) <;> cases v : real (right j) <;>
    simp_all [takeBit,connective]

def touched {g : Nat} (left right : Fin g→Nat) (isOr : Fin g→Bool) (v : Nat→Bool) :
    Finset (Fin g) :=
  Finset.univ.filter fun j => isOr j=false ∧ (v (left j)=true ∨ v (right j)=true)

theorem charge_increases {g : Nat} (left right : Fin g→Nat) (isOr sel : Fin g→Bool)
    (old real : Nat→Bool) (grows : ∀ i, old i=true → real i=true)
    (existsNew : ∃ j, isOr j=false ∧ old (left j)=false ∧ old (right j)=false ∧
      takeBit (sel j) (real (left j)) (real (right j))=true ∧
      (real (left j) && real (right j))=false) :
    (touched left right isOr old).card < (touched left right isOr real).card := by
  classical
  obtain ⟨j,kind,a,b,chosen,_⟩ := existsNew
  have newBit : real (left j)=true ∨ real (right j)=true := by
    cases h : sel j
    · exact Or.inr (by simpa [takeBit,h] using chosen)
    · exact Or.inl (by simpa [takeBit,h] using chosen)
  have before : j∉touched left right isOr old := by simp [touched,a,b]
  have after : j∈touched left right isOr real := by simp [touched,kind,newBit]
  have sub : touched left right isOr old ⊆ touched left right isOr real := by
    intro i hi
    simp only [touched,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    exact ⟨hi.1,hi.2.elim (fun h => Or.inl (grows _ h)) (fun h => Or.inr (grows _ h))⟩
  have ins : insert j (touched left right isOr old) ⊆ touched left right isOr real := by
    intro i h
    rcases Finset.mem_insert.mp h with rfl|e
    · exact after
    · exact sub e
  have sz := Finset.card_le_card ins
  rw [Finset.card_insert_of_notMem before] at sz
  omega

#print axioms new_charge
#print axioms charge_increases
end CoFlagCharge2990
