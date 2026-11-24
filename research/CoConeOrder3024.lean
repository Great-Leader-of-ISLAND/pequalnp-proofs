import PEqualNP.CoAO3143Restriction

namespace CoConeOrder3024
open CoAO3143Restriction
noncomputable section
local instance {α : Type} : DecidableEq (Wire α) := Classical.decEq _

theorem ordered {α : Type} {out : Wire α} {k S} (h : Cone out k S) (r s : α)
    (step : ∀ w∈S, w r=true → w s=true) (yes : out r=true) : out s=true := by
  induction h with
  | stop => exact step _ (by simp) yes
  | @gate k U d a b fresh tail ih =>
    apply ih
    intro w hw hit
    rcases Finset.mem_insert.mp hw with rfl|old
    · have ha := step a (Finset.mem_insert_self _ _)
      have hb := step b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      cases d <;> simp only [op,Bool.false_eq_true,↓reduceIte,Bool.and_eq_true,Bool.or_eq_true] at hit ⊢
      · exact ⟨ha hit.1,hb hit.2⟩
      · exact hit.imp ha hb
    · exact step w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old)) hit

end
end CoConeOrder3024
