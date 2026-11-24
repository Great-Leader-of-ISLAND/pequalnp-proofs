import PEqualNP.CoNine3024Budget
import PEqualNP.CoFrontier3024Seed

namespace CoFrontier3024Counts
open CoNine3024 CoNine3024Budget CoThetaNine CoThetaFreeCore CoAO3143Restriction

noncomputable section
local instance {α : Type} : DecidableEq (Wire α) := Classical.decEq _
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Distinct full truth tables correspond to distinct sources of the suffix.
    Their fixed flags therefore count precisely the loss term in the cone bound. -/
theorem tally_losses {α : Type} (den : Atom→Wire α) (lift : SmallInput→α)
    (d : Atom→Counts) (j : Fin 9) (ws : List Atom) (nd : (ws.map den).Nodup)
    (flags : ∀ w∈ws,d w j=if Constant (cut lift (den w)) then 1 else 0) :
    tally d ws j=losses lift (ws.map den).toFinset := by
  classical
  induction ws with
  | nil => simp [tally,losses]
  | cons w ws ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp nd
    have rec' := ih nd (fun v hv => flags v (List.mem_cons_of_mem _ hv))
    unfold losses at rec' ⊢
    have absent : den w∉(ws.map den).toFinset.filter (fun v => Constant (cut lift v)) := by
      intro mem
      exact fresh (by simpa using (Finset.mem_filter.mp mem).1)
    simp only [tally,flags w List.mem_cons_self,rec',List.map_cons,List.toFinset_cons,Finset.filter_insert]
    by_cases e : Constant (cut lift (den w))
    · simp [e,Finset.card_insert_of_notMem absent,Nat.add_comm]
    · simp [e]

/-- This is the search's guard, with its encoded counters obtained from nine
    independently projected signed prefixes of the same suffix. -/
theorem safe_semantic (L : SignedLower) (s : State) (den : Atom→Wire Input)
    (c : Counts) (d : Atom→Counts) (spent : s.spent=pack c)
    (fixed : ∀w∈s.wires,w.fixed=pack (d w)) (nd : (s.wires.map den).Nodup)
    (flags : ∀ (j : Fin 9) w, w∈s.wires → d w j=if Constant (cut (CoThetaCuts3024.plant j) (den w)) then 1 else 0)
    {k : Nat} (run : Cone ans k (s.wires.map den).toFinset)
    (pre : ∀ j : Fin 9, ∃ h pool, Free vertices7 h pool ∧ h+c j+k≤14 ∧
      ∀ w∈(s.wires.map den).toFinset, norm 0 (cut (CoThetaCuts3024.plant j) w)∈pool) :
    safe s=true := by
  apply safe_of_counts s c d spent fixed
  intro j
  rw [tally_losses den _ d j s.wires nd (flags j)]
  obtain ⟨h,pool,prog,clock,hold⟩ := pre j
  exact CoFrontier3024Seed.available_three L j run prog hold (c j) clock

#print axioms CoFrontier3024Counts.safe_semantic
end
end CoFrontier3024Counts
