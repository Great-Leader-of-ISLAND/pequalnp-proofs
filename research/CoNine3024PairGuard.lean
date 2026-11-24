import PEqualNP.CoNine3024CotreeCells
import PEqualNP.CoNine3024PairProgram

namespace CoNine3024PairGuard
open CoAO3143Restriction CoThetaNine CoNine3024 CoNine3024Rows CoNine3024CotreeCells

private theorem owns_spec {p ws c a} (h : owns p ws c a=true) : used p c ∧ Only ws c a := by
  unfold owns at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨mask,others⟩ := h
  refine ⟨mask,?_⟩
  intro w hw bit
  have b := List.all_eq_true.mp others w hw
  simpa only [bit,Bool.not_true,Bool.false_or,beq_iff_eq] using b

theorem verify_false (p : Fin 11) {k S} (run : Cone ans k S) (tight : S.card=k+1)
    (ws : List Atom) (good : ∀w∈ws,Good p w) (cover : ∀ w∈S,∃u∈ws,value u=w)
    (h : Hint) : verify p ws h=false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  simp only [verify,Bool.and_eq_true,bne_iff_ne,beq_iff_eq] at hit
  obtain ⟨⟨⟨⟨⟨⟨different,positive⟩,negative⟩,r₁⟩,r₂⟩,n₁⟩,n₂⟩ := hit
  obtain ⟨hr₁,ar₁⟩ := owns_spec r₁
  obtain ⟨hr₂,ar₂⟩ := owns_spec r₂
  obtain ⟨hn₁,an₁⟩ := owns_spec n₁
  obtain ⟨hn₂,an₂⟩ := owns_spec n₂
  have pos : prow p h.r₂=prow p h.r₁ := by simp only [prow,positive]
  have neg : nrow p h.n₂=nrow p h.n₁ := by simp only [nrow,negative]
  exact different (shared_cell_pair p run tight good cover hr₁ hr₂ hn₁ hn₂ pos neg ar₁ ar₂ an₁ an₂)

theorem keep_correct (p : Fin 11) (s : State) {k cap S} (ck : k≤cap) (run : Cone ans k S)
    (width : S.card≤k+1) (imgs : (s.wires.map value).toFinset=S)
    (nd : (s.wires.map value).Nodup) (good : ∀w∈s.wires,Good p w) : keep p cap s=true := by
  classical
  by_cases tight : s.wires.length=cap+1
  · have n := List.toFinset_card_of_nodup nd
    rw [imgs,List.length_map] at n
    have b : S.card=k+1 := by omega
    have cov (w) (hw : w∈S) : ∃u∈s.wires,value u=w :=
      List.mem_map.mp (List.mem_toFinset.mp (imgs.symm ▸ hw))
    cases h : hint p s.wires with
    | none => simp [keep,h]
    | some c => simp [keep,h,verify_false p run b _ good cov c]
  · simp [keep,tight]

#print axioms CoNine3024PairGuard.keep_correct
end CoNine3024PairGuard
