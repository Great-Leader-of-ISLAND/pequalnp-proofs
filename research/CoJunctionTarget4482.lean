import PEqualNP.CoJunctionLogical4482
import PEqualNP.CoPortWhole4482
namespace CoJunctionTarget4482
open CoJunctionLogical4482 CoPortRoots4482 CoPortFrontier4482 CoPortTrace4482 CoPortCut4482

/-- Each root can be certified separately; internal and tight rows use
the generic routing and terminal certificates, respectively. -/
structure Certificate (I : Type) (rootWords : Finset W) where
  table : I → Record
  root : I
  ceiling : 7 ≤ (table root).budget
  starting : (stateWords (table root)).toFinset=rootWords
  authenticAt : ∀ s, authentic (table s).bank
  above : ∀ s,6 < (stateWords (table s)).toFinset.card
  classified : ∀ s, ((stateWords (table s)).toFinset.card=6+(table s).budget ∧
      ¬Path join (cleanCut model label 6) (table s).budget (stateWords (table s)).toFinset)
    ∨ Routed table (table s)

theorem exclude {I : Type} {S : Finset W} (c : Certificate I S)
    {k : Nat} (hk : k ≤ 7) : ¬Path join (cleanCut model label 6) k S := by
  intro path
  apply closes c.table c.authenticAt c.above c.classified 7 c.root c.ceiling
  exact ⟨k,hk,c.starting.symm ▸ path⟩

/-- Exactly the premise of CoPortRoots4482.conditional. The first state
uses nine raw variables; the second state has the additional OR(0,2). -/
theorem both {I J : Type} (ordinary : Certificate I raws.toFinset)
    (preset : Certificate J init.toFinset) :
    ∀ k ≤ 7, ¬ Path join (cleanCut model label 6) k raws.toFinset ∧
      ¬ Path join (cleanCut model label 6) k init.toFinset := by
  intro k hk
  exact ⟨exclude ordinary hk,exclude preset hk⟩

#print axioms both
end CoJunctionTarget4482
