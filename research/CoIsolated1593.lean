import PEqualNP.Outside.L_meta_1737

namespace CoIsolated1593

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1737

/-- Append a gate reading the previous output as it was addressed before appending. -/
theorem add_or_input {n s : Nat} {g : (Fin n → Bool) → Bool} (p : Fin n)
    (h : HasCircuitSize n g s) : HasCircuitSize n (fun x => x p || g x) (s+1) := by
  obtain ⟨C,fan,cap,out⟩ := h
  let a : Gate := ⟨.or,[p.val,C.output]⟩
  let D : Circuit := ⟨C.gates++[a],n+C.size⟩
  refine ⟨D,?_,?_,?_⟩
  · intro v hv
    change v∈C.gates++[a] at hv
    rcases List.mem_append.mp hv with prev|last
    · exact fan v prev
    · have eq : v=a := List.mem_singleton.mp last
      subst v
      simp [a]
  · change (C.gates ++ [a]).length ≤ s + 1
    simpa [Circuit.size] using Nat.add_le_add_right cap 1
  · intro x
    let v := wiresFrom C.gates (List.ofFn x)
    have len : v.length=n+C.size := by simp [v,length_wiresFrom,Circuit.size]
    have vp : v.getD p.val false = x p := by
      rw [show v.getD p.val false = (List.ofFn x).getD p.val false from
            getD_wiresFrom _ _ _ (by simpa using p.isLt)]
      rw [List.getD_eq_getElem _ _ (by simpa using p.isLt)]
      simp
    have vo : v.getD C.output false = g x := out x
    change (wiresFrom (C.gates++[a]) (List.ofFn x)).getD (n+C.size) false = _
    rw [wiresFrom_append]
    change (wiresFrom [a] v).getD (n+C.size) false = _
    rw [←len]
    simp [wiresFrom,a,GateOp.eval,getD_snoc_eq,vp,vo]

/-- A nonconstant Boolean function independent of p costs exactly one more
gate when disjoined with raw input p. No monotonicity of the circuit is needed. -/
theorem isolated_iff {n s : Nat} (p : Fin (n+1)) (g : (Fin (n+1) → Bool) → Bool)
    (indep : ∀ x b, g (Function.update x p b)=g x)
    (nonconst : ∃ x y, g x≠g y) :
    HasCircuitSize (n+1) (fun x => x p || g x) (s+1) ↔ HasCircuitSize (n+1) g s := by
  constructor
  · intro cost
    obtain ⟨u,v,ne⟩ := nonconst
    have zero : ∃ x, g x=false := by
      cases hu : g u with
      | false => exact ⟨u,hu⟩
      | true =>
        cases hv : g v with
        | false => exact ⟨v,hv⟩
        | true => exact (ne (hu.trans hv.symm)).elim
    obtain ⟨r,hr⟩ := zero
    let f : (Fin (n+1) → Bool) → Bool := fun x => x p || g x
    have cut (x) : f (Function.update x p false) = g x := by simp [f,indep]
    have dep : ∃ x, f (Function.update x p (!x p)) ≠ f x := by
      refine ⟨Function.update r p false, ?_⟩
      simp [f,indep,hr]
    have hnc : ∃ x y, f (Function.update x p false) ≠ f (Function.update y p false) :=
      ⟨u,v,by rwa [cut,cut]⟩
    have lower := one_gate_at n f p false s dep hnc cost
    simpa only [cut] using lower
  · exact add_or_input p

#print axioms CoIsolated1593.isolated_iff
end CoIsolated1593
