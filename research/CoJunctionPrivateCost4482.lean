import PEqualNP.CoJunctionCost4482
namespace CoJunctionPrivateCost4482
open CoJunctionCost4482 CoBitBlock4482

abbrev Annotated := Pin × Bits

/-- Numeric version of the per-pin tests. Each wire's exclusivity is
precomputed, so each pair uses four scalar intersections for all 8 moves. -/
def choices (ws : List Annotated) (k : Nat) : List Choice :=
  let n := ws.length
  (List.range n).flatMap fun i => (List.range n).flatMap fun j =>
    if i≥j then [] else
    let a := ws.getD i ((0,(0,0)),0)
    let b := ws.getD j ((0,(0,0)),0)
    [false,true].flatMap fun d =>
      let full := wireGate d a.1.1 b.1.1
      if ws.any (fun w => w.1.1==full) then [] else
      let da := (a.2 &&& (if d then b.1.2.2 else ~~~b.1.2.1)) == 0
      let db := (b.2 &&& (if d then a.1.2.2 else ~~~a.1.2.1)) == 0
      (List.range 4).filterMap fun drop =>
        let left := drop.testBit 0
        let right := drop.testBit 1
        let width := n+1-(if left then 1 else 0)-(if right then 1 else 0)
        if width≤6+(k-1) ∧ (!left || da)=true ∧ (!right || db)=true
          then some ⟨i,j,d,drop⟩ else none

end CoJunctionPrivateCost4482
