import PEqualNP.CoLive3825
import PEqualNP.CoLocalGate3825

namespace CoEscape3825
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoNonredundant3825 CoNearReaders3825 CoLocalGate3825

theorem used {n : ℕ} {C : Circuit} (minimum : IsMinimalCircuit n C) (nc : nonconstant n C)
    {j : ℕ} (actual : j < C.size) :
    C.output=n+j ∨ ∃ k < C.size,j < k ∧ n+j∈(atPos C k).inputs := by
  classical
  have hj : j < C.gates.length := actual
  let front := C.gates.take j
  let tail := C.gates.drop (j+1)
  have len : front.length=j := by simp [front,Nat.min_eq_left hj.le]
  have cs : Circuit.mk (front++C.gates[j]::tail) C.output=C := by
    cases C
    simp [front,tail]
  have live := CoLive3825.used_or_output n C.output front tail C.gates[j]
    (by simpa only [cs] using minimum) (by simpa only [cs] using nc)
  rw [len] at live
  rcases live with last | ⟨g,hg,read⟩
  · exact Or.inl last
  · obtain ⟨a,ha⟩ := List.mem_iff_getElem?.mp hg
    have hit : C.gates[j+1+a]?=some g := by simpa [tail,List.getElem?_drop,Nat.add_comm] using ha
    have hk := (List.getElem?_eq_some_iff.mp hit).1
    have eq : atPos C (j+1+a)=g := by simp [atPos,NestedCover.gateAt,List.getD_eq_getElem?_getD,hit]
    exact Or.inr ⟨j+1+a,hk,by omega,by simpa only [eq] using read⟩

theorem escape {C : Circuit} (min : IsMinimalCircuit 9 C) (nc : nonconstant 9 C)
    (back : NestedCover.ReadsBack 9 C)
    (arity : ∀ i < C.gates.length,(atPos C i).op=.not → (atPos C i).inputs.length=1)
    (v : Fin 9) (notroot : ∀ j∈special C v,C.output≠9+j) : escapes C v := by
  classical
  intro j hj
  obtain ⟨raw,op⟩ := Finset.mem_filter.mp hj
  obtain ⟨bounds,pin⟩ := Finset.mem_filter.mp raw
  have pos : j < C.size := Finset.mem_range.mp bounds
  rcases used min nc pos with eq|⟨k,hk,early,child⟩
  · exact (notroot j hj eq).elim
  · have miss : v.val∉(atPos C k).inputs :=
      fun bad => no_common min nc back arity v early hk pin op ⟨bad,child⟩
    refine ⟨k,Finset.mem_sdiff.mpr ⟨?_,?_⟩,early,child⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,Or.inr ⟨j,early,pin,op,child⟩⟩
    · exact fun mem => miss (Finset.mem_filter.mp mem).2

#print axioms escape
end CoEscape3825
