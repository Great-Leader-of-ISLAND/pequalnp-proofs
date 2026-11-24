import PEqualNP.CoNine3024CanonTable
import PEqualNP.CoNine3024PairGuard

namespace CoNine3024.Canon
open CoAO3143Restriction CoThetaNine CoNine3024Rows

/-- The untrusted table can supply any hint, for any wire order. Each proposed
four-cell obstruction is tested against the physical cone with its full row labels. -/
theorem guided_correct (p : Fin 11) (ask : Oracle) (s : State) {k cap S}
    (ck : k≤cap) (phys : Cone ans k S) (width : S.card≤k+1)
    (imgs : (s.wires.map value).toFinset=S) (nd : (s.wires.map value).Nodup)
    (good : ∀ w∈s.wires,Good p w) : guided p ask cap s=true := by
  classical
  by_cases tight : s.wires.length=cap+1
  · have n := List.toFinset_card_of_nodup nd
    rw [imgs,List.length_map] at n
    have b : S.card=k+1 := by omega
    have cov (w) (hw : w∈S) : ∃u∈s.wires,value u=w :=
      List.mem_map.mp (List.mem_toFinset.mp (imgs.symm ▸ hw))
    cases found : ask cap s with
    | none => simp [guided,found]
    | some c => simp [guided,found,CoNine3024PairGuard.verify_false p phys b _ good cov c]
  · simp [guided,tight]

end CoNine3024.Canon
