import PEqualNP.CoBudget3825Base

namespace PEqualNP.Outside.L_meta_2153_aux.CoOneCut3825
open CoThetaFreeCore CoThetaNine

theorem one_more (cert : SignedLower)
    {R : Type} (slice : SmallInput → R) (raw : List (R → Bool)) (out wire : R → Bool)
    (zero : restrict slice wire = absentBit)
    (inputs : ∀ a ∈ raw, restrict slice a ∈ vertices7)
    (image : restrict slice out = ans7)
    (r s : R) (agree : agreeOutside (· = wire) r s raw)
    (different : out r ≠ out s) (notLiteral : out ≠ wire)
    (gs : List (TraceGate R)) (ok : sufficient raw out gs) : 12 ≤ gs.length := by
  classical
  obtain ⟨g,hg,read,_⟩ := reader_witness (· = wire) r s ok.1 agree ok.2 notLiteral different
  have dead := reading_zero_disappears slice zero (show reads g wire from read)
  have member : g ∈ vanishing slice gs := by simp [vanishing,hg,dead]
  have nonzero : 1 ≤ saved slice gs := by
    rw [saved_eq_length]
    exact length_of_cover [g] _ (by simp) (by simpa using member)
  obtain ⟨ws,run,use⟩ := restrict_trace slice gs ok.1
    (Free.start (raw:=vertices7)) List.mem_cons_self inputs
  have take := use out ok.2
  rw [image] at take
  have price : 11 ≤ remaining slice gs := by simpa only [Nat.zero_add] using cert run take
  have total := accounted slice gs
  omega

def deleted (j : Fin 6) (swap : Bool) : Fin 9 := if swap then eqp j else ep j
def mate (j : Fin 6) (swap : Bool) : Fin 9 := if swap then ep j else eqp j
def clearBit (i : Fin 9) (r : Input) : Input := row (r.val &&& (511 ^^^ (1 <<< i.val)))
def rawCut (i : Fin 9) := vertices.map (restrict (clearBit i))
def goalCut (i : Fin 9) := restrict (clearBit i) ans

def refVertex (j : Fin 6) (swap : Bool) : ℕ :=
  if swap then CoPetersenThetaGeometry.outerNeighbor j else CoPetersenThetaGeometry.shortNeighbor j
def refRow (j : Fin 6) (swap addMate : Bool) : Input :=
  row ((1 <<< refVertex j swap) ||| (if addMate then 1 <<< (mate j swap).val else 0))

set_option maxHeartbeats 2000000 in
theorem geometry : ∀ (j : Fin 6) (sw : Bool),
    (∀ t : SmallInput, clearBit (deleted j sw) (sliceLift j t) = sliceLift j t) ∧
    (∀ t : SmallInput, vtx (mate j sw) (sliceLift j t) = false) ∧
    goalCut (deleted j sw) (refRow j sw false) ≠ goalCut (deleted j sw) (refRow j sw true) ∧
    (∀ i : Fin 9, i ≠ mate j sw →
      vtx i (clearBit (deleted j sw) (refRow j sw false)) =
      vtx i (clearBit (deleted j sw) (refRow j sw true))) ∧
    goalCut (deleted j sw) (row (1 <<< (mate j sw).val)) ≠
      vtx (mate j sw) (clearBit (deleted j sw) (row (1 <<< (mate j sw).val))) := by
  decide +kernel

theorem twelve (cert : SignedLower) (j : Fin 6) (sw : Bool) (gs : List (TraceGate Input))
    (ok : sufficient (rawCut (deleted j sw)) (goalCut (deleted j sw)) gs) : 12 ≤ gs.length := by
  let v := deleted j sw
  let w := mate j sw
  obtain ⟨keep,gone,diff,fix,lit⟩ := geometry j sw
  have same (f : Input → Bool) :
      restrict (sliceLift j) (restrict (clearBit v) f) = restrict (sliceLift j) f := by
    funext r
    exact congrArg f (keep r)
  refine one_more cert (sliceLift j) (rawCut v) (goalCut v) (restrict (clearBit v) (vtx w))
    ?_ ?_ ?_ (refRow j sw false) (refRow j sw true) ?_ diff ?_ gs ok
  · rw [same]
    exact funext gone
  · intro f hf
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hf
    rw [same]
    exact slice_known j a ha
  · unfold goalCut
    rw [same]
    exact funext (fun r => (slice7_values j r).1)
  · intro f hf ne
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hf
    rcases List.mem_cons.mp ha with rfl|h
    · rfl
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    apply fix i
    intro e
    exact ne (by rw [show i = w from e])
  · intro e
    exact lit (congrFun e _)
end PEqualNP.Outside.L_meta_2153_aux.CoOneCut3825
