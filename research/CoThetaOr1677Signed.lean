import PEqualNP.CoThetaOr1677Physical

namespace CoThetaOr1677
open CoThetaNine CoThetaFreeCore CoThetaPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def starting : List (SmallInput→Bool) := absentBit::(fun _ => true)::raw

private theorem knownNorm : ∀ w∈starting.map (norm (0 : SmallInput)),w∈vertices7 := by
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  rcases List.mem_cons.mp hv with rfl|hv
  · exact List.mem_cons_self
  rcases List.mem_cons.mp hv with rfl|hv
  · exact List.mem_cons_self
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  have zero : ∀ j : Fin 7,raw7 j 0=false := by decide
  have fixed : norm (0 : SmallInput) (raw7 i)=raw7 i := by
    funext r
    simp [CoThetaFreeCore.norm,phase,zero]
  rw [fixed]
  exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

private theorem transfer {s t : List (SmallInput→Bool)} {n xs} (pre : Free s n xs)
    (initial : ∀ w∈s,w∈t) : ∃ ys,Free t n ys ∧ ∀ w∈xs,w∈ys := by
  induction pre with
  | start => exact ⟨_,Free.start,initial⟩
  | @binary n xs a b pre kind ha hb ih =>
    obtain ⟨ys,built,sub⟩ := ih
    refine ⟨_,Free.binary built kind (sub a ha) (sub b hb),?_⟩
    intro w h
    rcases List.mem_cons.mp h with rfl|old
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub _ old)

/-- Every NOT is allowed for free by this binary lower bound. -/
theorem signed_binary (lower : SignedLower) (C : Circuit) (fan : FanInTwo C)
    (correct : readWord C.gates C.output=ans7) : 11 ≤ (C.gates.map boolCost).sum := by
  let fs := C.gates.map gateForm
  let result := (CoThetaFreeCore.execute fs raw).getD C.output absentBit
  have word : result=ans7 := by
    funext r
    have h := congrArg (fun w : List Bool => w.getD C.output false)
      (CoThetaPhysical.circuit_rows C fan raw r)
    change ((CoThetaFreeCore.execute fs raw).map (fun f => f r)).getD C.output false = _ at h
    have read : ((CoThetaFreeCore.execute fs raw).map (fun f => f r)).getD C.output false=result r := by
      simp only [result,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases (CoThetaFreeCore.execute fs raw)[C.output]? <;> rfl
    rw [read] at h
    have withRaw : raw.map (fun f => f r)=List.ofFn (fun i : Fin 7 => raw7 i r) := by
      simp [raw,List.map_ofFn]
    rw [withRaw] at h
    exact h.trans (congrFun correct r)
  have hit : result∈CoThetaFreeCore.execute fs raw := by
    cases e : (CoThetaFreeCore.execute fs raw)[C.output]? with
    | none =>
      have empty : result=absentBit := by simp [result,List.getD_eq_getElem?_getD,e]
      have z := congrFun (word.symm.trans empty) (5 : SmallInput)
      exact ((by decide : ans7 (5 : SmallInput) ≠ absentBit (5 : SmallInput)) z).elim
    | some a =>
      have eq : result=a := by simp [result,List.getD_eq_getElem?_getD,e]
      rw [eq]
      exact List.mem_of_getElem? e
  have cs (b : Bool) : (fun _ : SmallInput => b) ∈ starting := by
    cases b
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨xs,prog,cover⟩ := pins_to_program fs raw starting starting 0 Ordinary.start cs
    (fun u h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  obtain ⟨ys,signed,sub⟩ := simulate_all_wires (0 : SmallInput) prog
  obtain ⟨zs,run,sub2⟩ := transfer signed knownNorm
  have target := sub2 _ (sub _ (cover _ hit))
  have normTarget : norm (0 : SmallInput) ans7=ans7 := by
    have z : ans7 0 = false := by decide
    funext r
    simp [CoThetaFreeCore.norm,phase,z]
  rw [word,normTarget] at target
  have k := lower run target
  have lim := cost_le_binary C.gates
  change 11 ≤ 0 + cost (C.gates.map gateForm) at k
  omega

private theorem cost_upper (xs : List Gate) : (xs.map boolCost).sum ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons h t ih =>
    have one : boolCost h ≤ 1 := by cases h with | mk d p => cases d <;> decide
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

private theorem cost_strict (xs : List Gate) (neg : ∃ g∈xs,g.op=.not) :
    (xs.map boolCost).sum < xs.length := by
  induction xs with
  | nil => simpa using neg
  | cons h t ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    by_cases here : h.op=.not
    · have z : boolCost h=0 := by simp [boolCost,here]
      have le := cost_upper t
      omega
    · obtain ⟨g,hg,notGate⟩ := neg
      have tail := (List.mem_cons.mp hg).resolve_left (fun eq => here (eq ▸ notGate))
      have ne := ih ⟨g,tail,notGate⟩
      have one : boolCost h ≤ 1 := by cases h with | mk d p => cases d <;> decide
      omega

/-- A paid NOT cannot occur in an eleven-total-gate implementation of the
theta. In the remaining monotone case the forced OR requires the twelfth gate. -/
theorem raw_any (lower : SignedLower) (C : Circuit) (fan : FanInTwo C) (marked : Nat)
    (correct : readWord C.gates C.output=ans7) (witness : readWord C.gates marked=seed45) :
    12 ≤ C.gates.length := by
  classical
  by_cases neg : ∃ g∈C.gates,g.op=.not
  · have paid := cost_strict C.gates neg
    have pos := signed_binary lower C fan correct
    omega
  · apply raw_price C.gates C.output marked _ correct witness
    intro g hg
    obtain ⟨h,cap⟩ := fan g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    exact ⟨h.elim Or.inl (fun z => Or.inr (z.resolve_right (fun n => neg ⟨g,hg,n⟩))),cap⟩

#print axioms raw_any
end CoThetaOr1677
