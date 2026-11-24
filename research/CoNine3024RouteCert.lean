import PEqualNP.CoExact3024
import PEqualNP.CoNine3024CanonTable
import PEqualNP.CoNine3024PairGuard

namespace CoNine3024RouteCert
open CoNine3024 CoNine3024Path CoNine3024Transition CoNine3024PairGuard

theorem price_guard (p : Fin 11) : SoundGuard p (keep p) := by
  intro k cap S s ck c im nd gd
  exact keep_correct p s ck c (card_le c) im nd gd
theorem guided_sound (p : Fin 11) (ask : Canon.Oracle) : SoundGuard p (Canon.guided p ask) := by
  classical
  intro k cap S s ck c im nd gd
  have n := List.toFinset_card_of_nodup nd
  rw [im,List.length_map] at n
  have width := card_le c
  have cov (w) (hw : w∈S) : ∃u∈s.wires,CoNine3024Rows.value u=w :=
    List.mem_map.mp (List.mem_toFinset.mp (im.symm ▸ hw))
  by_cases tight : s.wires.length=cap+1
  · have eq : S.card=k+1 := by omega
    cases h : ask cap s with
    | none => simp [Canon.guided,h]
    | some t => simp [Canon.guided,h,verify_false p c eq _ gd cov t]
  · simp [Canon.guided,tight]

#print axioms CoNine3024RouteCert.price_guard
end CoNine3024RouteCert
