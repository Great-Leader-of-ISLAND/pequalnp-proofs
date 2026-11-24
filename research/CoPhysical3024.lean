import PEqualNP.CoClean3024
import PEqualNP.CoAllRaw3024
import PEqualNP.CoHead3024

namespace CoPhysical3024
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoThetaNine CoHead3024 CoAO3143Restriction CoAllRaw3024

def pivot (pins : List (Fin 11)) : Fin 11 := pins.head?.getD 10

private theorem pin_value (pins : List (Fin 11)) :
    secondNot (pins.map Fin.val) = inverse (pivot pins) := by
  cases pins with
  | nil => rfl
  | cons p ps =>
    funext r
    have hh : ∀ (p : Fin 11) (r : Input),
        (!(firstBank.getD p.val CoThetaFreeCore.absentBit r)) = inverse p r := by decide +kernel
    exact hh p r

private theorem initial_label (pins : List (Fin 11)) {w} (h : w∈rawBank (pins.map Fin.val)) :
    ∃ j : Fin 13, w=label (pivot pins) j := by
  rcases List.mem_append.mp h with fst|inv
  · rcases List.mem_append.mp fst with r|q
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp r
      exact ⟨⟨i.val,by omega⟩,by simp [label,i.isLt]⟩
    · obtain rfl := List.mem_singleton.mp q
      exact ⟨9,rfl⟩
  · obtain rfl := List.mem_singleton.mp inv
    exact ⟨10,pin_value pins⟩

theorem extract (lower : SignedLower) (pins : List (Fin 11)) (D : Circuit) (fan : FanInTwo D)
    (small : D.size≤13)
    (correct : ∀ r : Input, let x := fun i => vtx i r
      let z := List.ofFn x ++ [x 0 || x 2]
      D.eval (z ++ [GateOp.not.eval ((pins.map Fin.val).map fun i => z.getD i false)])=ans r) :
    ∃ k S, k≤13 ∧ CoClean3024.Clean ans k S ∧
      (∀ w∈S, ∃ j : Fin 13, w=label (pivot pins) j) ∧ ∀ i : Fin 9, vtx i∈S := by
  classical
  let raw := rawBank (pins.map Fin.val)
  let U := CoAO3143Restriction.circuitWires D.gates raw
  let out := U.getD D.output (con false)
  have truth : out=ans := by
    funext r
    have ev := congrArg (fun z : List Bool => z.getD D.output false)
      (CoAO3143Restriction.circuit_rows D.gates raw r)
    change (U.map (fun w => w r)).getD D.output false=D.eval (raw.map fun w => w r) at ev
    have read : (U.map (fun w => w r)).getD D.output false=out r := by
      simp only [out,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases U[D.output]? <;> rfl
    rw [read] at ev
    change out r=D.eval ((rawBank (pins.map Fin.val)).map fun w => w r) at ev
    rw [CoHead3024.raw_eq] at ev
    exact ev.trans (correct r)
  have nc : ¬Constant ans := by
    rintro ⟨b,e⟩
    have a := congrFun e (row 0)
    have u := congrFun e (row 3)
    have h0 : ans (row 0)=false := by decide
    have h3 : ans (row 3)=true := by decide
    change ans _=b at a u
    exact Bool.false_ne_true (h0.symm.trans (a.trans (u.symm.trans h3)))
  have hit : ans∈U ∨ Constant ans := by
    cases e : U[D.output]? with
    | none =>
      right
      exact ⟨false,truth.symm.trans (by simp [out,List.getD_eq_getElem?_getD,e])⟩
    | some w =>
      left
      have ee : out=w := by simp [out,List.getD_eq_getElem?_getD,e]
      exact (truth.symm.trans ee).symm ▸ List.mem_of_getElem? e
  have no := (exact_binary lower (pins.map Fin.val) D fan small correct).2.2
  have legal (g) (hg : g∈D.gates) : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
    obtain ⟨h,hgates⟩ := fan g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    exact ⟨h.elim Or.inl (fun hh => Or.inr (hh.resolve_right (no g hg))),hgates⟩
  obtain ⟨k,S,cap,clean,src⟩ := CoClean3024.extract ans D.gates raw legal hit
  have sub (w) (hw : w∈S) : ∃ j : Fin 13, w=label (pivot pins) j :=
    initial_label pins ((src w hw).resolve_right (CoClean3024.inputs_vary clean nc w hw))
  exact ⟨k,S,cap.trans small,clean,sub,all_raw (pivot pins) (CoClean3024.toCone clean) sub⟩

#print axioms CoPhysical3024.extract
end CoPhysical3024
