import PEqualNP.CoPortEdgeRows4482
import PEqualNP.CoBlockSlots4482
import PEqualNP.CoImplicitBlock4482
import PEqualNP.CoSmallTail4482
namespace CoActualTight4482
open CoPortRoots4482 CoPortTrace4482 CoPortCut4482 CoTightBlocks4482
open CoBitBlock4482 CoBlockIntervals4482 CoPortEdgeRows4482 CoBlockSlots4482

/-- The self-generating interval certificate excludes an actual remaining
physical AND/OR path, with the canonical slots identified by an equivalence. -/
theorem implicit_excludes {S : Finset W} {k n : Nat} (tight : S.card=6+k)
    (ordered : ∀w∈S,Ordered w)
    (e : Fin n ≃ ↥S) (vals : Fin n→Mark) (same : ∀i,vals i=mark (e i).val)
    (core : Finset (Fin n)) (many : 6<core.card)
    (inc : Fin n → BitVec (2^n))
    (digits : ∀i (j : Fin (2^n)), (inc i).getLsbD j.val=j.val.testBit i.val)
    (must : BitVec (2^n)) (need : ∀ j : Fin (2^n),
      (members j).card+5≤S.card → 2≤((members j)∩core).card → must.getLsbD j.val=true)
    (fuel : Nat) (accepted : CoImplicitBlock4482.check
      (List.ofFn (fun i => (⟨vals i,inc i⟩ : Col (2^n)))) fuel must=true) :
    ¬Path join (cleanCut model label 6) k S := by
  intro path
  obtain ⟨T,st,sz,⟨B⟩⟩ := partition cell model.applyJoin 6 (fun _ h => h.1) path tight
  obtain ⟨pairs,valid⟩ := CoImplicitBlock4482.check_sound _ _ _ accepted
  have cols : vals=(fun i => mark (e i).val) := funext same
  rw [cols] at valid
  apply impossible B lower upper mark positive negative (fun i w hw => ordered w hw i)
    (terminal_dist T st) e core (by omega) inc digits must _ pairs valid
  intro j bound a
  apply need j _ a
  simpa [sz] using bound

/-- A width-seven or width-eight tight frontier can instead be replayed
directly, including all gate polarities and all pairs of surviving inputs. -/
theorem small_excludes {S : Finset W} {k : Nat} (tight : S.card=6+k)
    (ws : List W) (haveAll : ∀w∈S,w∈ws)
    (rejected : CoSmallTail4482.solve k (ws.map mark)=false) :
    ¬Path join (cleanCut model label 6) k S := by
  intro path
  have h := CoSmallTail4482.physical mark mark_gate 6 (fun _ st => st.1)
    terminal_mark path tight ws haveAll
  rw [rejected] at h
  contradiction

#print axioms implicit_excludes
#print axioms small_excludes
end CoActualTight4482
