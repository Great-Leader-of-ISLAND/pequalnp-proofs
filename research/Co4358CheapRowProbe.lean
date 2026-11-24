import PEqualNP.Co4358EdgeProbe
import PEqualNP.Co4358OriginalWords
namespace CoNum4358.CheapRows
open EdgeProbe (bins guess)
open CoAO3143
open IntCornerGround (W sig cells bare make pay fullMask cap isGoal matched rectBound remaining table Table)
open IntCornerGround.Fast (retain)
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def sameRow (k j q : Nat) (ws : List Nat) :=
  let t := WordRows.Original.tier k
  let row := WordRows.row t j
  decide (j<t.total) && row.1==q && ws.isPerm row.2

def post (k q : Nat) (lookup : Nat→Nat) (move : Nat) (ws : List Nat) :=
  cap ws true && cap ws false &&
    (if k==0 then ws.any isGoal else !(rectBound k (ws.map sig) || sameRow k (lookup move) q ws))

def gate (k q : Nat) (lookup : Nat→Nat) (ws rest : List Nat) (a b code rm ca cb : Nat) (d : Bool) :=
  let z := make d a b
  let fee := pay d a b
  decide (fee≤q) && sig z != 0 && sig z != 32767 && !(bare.contains (sig z)) &&
    !(ws.any fun w => sig w==sig z) &&
    (let mask := rm ||| cells (sig z)
     options.any fun ka => options.any fun kb =>
       decide (1+rest.length+ka.toNat+kb.toNat≤k+1) &&
       (let fringe := z :: retain a b ka kb rest
        let m := (if ka then ca else 0) ||| (if kb then cb else 0) ||| mask
        (m &&& fullMask)==fullMask && post k (q-fee) lookup (code+4*d.toNat+2*ka.toNat+kb.toNat) fringe))

def entry (k i : Nat) :=
  let r := WordRows.row (WordRows.Original.tier (k+1)) i
  let ws := r.2
  let score := guess (bins (k*8192+i))
  decide (ws.map sig).Nodup &&
    !(scanPairs (fun a b =>
      let code := 8*(16*ws.idxOf a+ws.idxOf b)
      let rest := remaining ws a b false false
      let mask := rest.foldl (fun n w => n ||| cells (sig w)) 0
      options.any (gate k r.1 score ws rest a b code mask (cells (sig a)) (cells (sig b)))) ws)

set_option profiler true
set_option profiler.threshold 35
theorem p3 : Memo.allAt (entry 2) 0 8=true := by decide +kernel
theorem p7 : Memo.allAt (entry 6) 0 8=true := by decide +kernel
theorem p9 : Memo.allAt (entry 8) 0 8=true := by decide +kernel
theorem p11 : entry 10 0=true := by decide +kernel
end CoNum4358.CheapRows
