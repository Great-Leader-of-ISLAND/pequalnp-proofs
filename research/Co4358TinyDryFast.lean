import PEqualNP.Co4358TinyDry
namespace CoNum4358.Dry.Fast
open CoAO3143
open Tiny (K W bare make pay)
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def retain (a b : W) (ka kb : Bool) (rest : List W) : List W :=
  let r := if kb then b::rest else rest
  if ka then a::r else r

def possible (ws : List W) (mask : Nat) :=
  if mask==fullMask then true else
    let i := (fullMask ^^^ mask).log2
    ws.any fun w => directed w.1 (Fin.ofNat 8 (i/7)) (Fin.ofNat 7 i)

def finish (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false &&
    (if k==0 then ws.any isGoal else !(matched T q ws || rectBound k (ws.map Prod.fst)))

def tryGate (k q : Nat) (T : Table) (ws rest : List W) (a b : W)
    (restMask ca cb : Nat) (d : Bool) :=
  let z := make d a b
  let payNow := pay d a b
  decide (payNow≤q) && z.1 != 0 && z.1 != 32767 && !(bare.contains z.1) &&
    !(ws.any fun w => w.1==z.1) &&
    (let base := restMask ||| cells z.1
     options.any fun ka => options.any fun kb =>
       decide (1+rest.length+ka.toNat+kb.toNat≤k+1) &&
       (let fringe := z::retain a b ka kb rest
        let mask := (if ka then ca else 0) ||| (if kb then cb else 0) ||| base
        possible fringe mask && finish k (q-payNow) T fringe))

def node (k q : Nat) (T : Table) (ws : List W) :=
  decide (ws.map Prod.fst).Nodup &&
  !(scanPairs (fun a b =>
    let rest := remaining ws a b false false
    let mask := rest.foldl (fun n w => n ||| cells w.1) 0
    options.any (tryGate k q T ws rest a b mask (cells a.1) (cells b.1))) ws)

def entry (k i : Nat) : Bool :=
  let r := (table (k+1)).row i
  node k r.1 (table k) r.2

theorem p3 : CoAO3143.Memo.allAt (entry 2) 0 8=true := by decide +kernel
theorem p7 : CoAO3143.Memo.allAt (entry 6) 0 8=true := by decide +kernel
theorem p9 : CoAO3143.Memo.allAt (entry 8) 0 8=true := by decide +kernel
theorem p11 : entry 10 0=true := by decide +kernel
end CoNum4358.Dry.Fast
