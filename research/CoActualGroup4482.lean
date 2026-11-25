import PEqualNP.CoActualTight4482
import PEqualNP.CoGroupBlock4482
namespace CoActualGroup4482
open CoPortRoots4482 CoPortTrace4482 CoPortCut4482 CoTightBlocks4482
open CoBitBlock4482 CoBlockIntervals4482 CoPortEdgeRows4482 CoBlockSlots4482
open CoGroupBlock4482

/-- Different physical prefixes share one numerical terminal obstruction
provided the three bounds on each live Mark are checked for this member. -/
theorem group_excludes {S : Finset W} {k n : Nat} (tight : S.card=6+k)
    (ordered : ∀w∈S,Ordered w)
    (e : Fin n ≃ ↥S) (vals : Fin n→Mark) (same : ∀i,vals i=mark (e i).val)
    (big : Fin n→Box) (bounded : ∀i,fits (big i) (vals i)=true)
    (core : Finset (Fin n)) (many : 6<core.card)
    (inc : Fin n→BitVec (2^n))
    (digits : ∀i (j : Fin (2^n)), (inc i).getLsbD j.val=j.val.testBit i.val)
    (must : BitVec (2^n)) (need : ∀ j : Fin (2^n),
      (members j).card+5≤S.card → 2≤((members j)∩core).card → must.getLsbD j.val=true)
    (fuel : Nat) (accepted : checkGroup
      (List.ofFn (fun i => (⟨big i,inc i⟩ : BCol (2^n)))) fuel must=true) :
    ¬Path join (cleanCut model label 6) k S := by
  intro path
  obtain ⟨T,st,sz,⟨B⟩⟩ := partition cell model.applyJoin 6 (fun _ h => h.1) path tight
  obtain ⟨pairs,valid⟩ := for_member (List.ofFn (fun i : Fin n => i)) big vals inc
    (fun i _ => bounded i) fuel must (by simpa only [List.map_ofFn,Function.comp_def] using accepted)
  have cols : vals=(fun i => mark (e i).val) := funext same
  simp only [List.map_ofFn,Function.comp_def,cols] at valid
  apply impossible B lower upper mark positive negative (fun i w hw => ordered w hw i)
    (terminal_dist T st) e core (by omega) inc digits must _ pairs valid
  intro j bound a
  apply need j _ a
  simpa [sz] using bound

#print axioms group_excludes
end CoActualGroup4482
