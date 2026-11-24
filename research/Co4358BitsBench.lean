import PEqualNP.Co4358JumpBench

namespace CoNum4358.Tiny.ShareGrid.Forest

open CoAO3143

def maskEdges : List Prof → List (K×K)
  | [] => []
  | a::r => (r.filterMap (fun b => if Corners.pair a b then some (a.wire,b.wire) else none))++maskEdges r

inductive Bundle where
  | empty
  | more (left right total : Nat) (leftUsed rightUsed : Bool) (tail : Bundle)

def Bundle.total : Bundle → Nat
  | .empty => 0
  | .more _ _ u _ _ _ => u

def bundle : List Block → Bundle
  | [] => .empty
  | g::gs =>
    let rest := bundle gs
    let l := cov g.lhs
    let r := cov g.rhs
    .more l r (l ||| (r ||| rest.total)) (!g.lhs.isEmpty) (!g.rhs.isEmpty) rest

def ground : Bundle → Nat → Nat → Bool → Bool
  | .empty,a,b,used => used && !(uncoveredProduct a b (estimateProduct b))
  | .more x y u cx cy tail,a,b,used =>
    let ca := a ||| u
    let cb := b ||| u
    !(uncoveredProduct ca cb (estimateProduct cb)) &&
      (ground tail (x|||a) (y|||b) (cx||used) || ground tail (y|||a) (x|||b) (cy||used))

def quickPossible (xs : List K) :=
  let unique := Corners.exclusive xs
  let pairs := maskEdges (xs.map fun x => prof x unique)
  (compile pairs (seed xs)).any (fun ls => ground (bundle (blocks ls)) 0 0 false)

structure Indicator where
  wire : K
  rows : Nat
  cols : Nat

def rowSpread (u : Nat) :=
  let x := u ||| (u>>>1)
  let y := x ||| (x>>>2)
  (y ||| (y>>>3)) &&& columnMask &&& fullMask

def colSpread (u : Nat) :=
  let x := u ||| (u>>>7)
  let y := x ||| (x>>>14)
  (y ||| (y>>>28)) &&& 127

def indicator (only : Nat) (w : K) :=
  let u := cells w &&& only
  Indicator.mk w (rowSpread u) (colSpread u)

def contrary (a b : Indicator) :=
  a.wire != b.wire && (a.rows &&& b.rows) != 0 && (a.cols &&& b.cols) != 0

def simpleEdges : List Indicator → List (K×K)
  | [] => []
  | a::r => (r.filterMap (fun b => if contrary a b then some (a.wire,b.wire) else none))++simpleEdges r

def cheapPossible (xs : List K) :=
  let unique := Corners.exclusive xs
  let pairs := simpleEdges (xs.map (indicator unique))
  (compile pairs (seed xs)).any (fun ls => ground (bundle (blocks ls)) 0 0 false)


end CoNum4358.Tiny.ShareGrid.Forest

namespace CoNum4358.Tiny.QuickBench

open ShareGrid.Forest

def finish (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false && (if k==0 then ws.any isGoal else
    !(Corners.limit k (ws.map Prod.fst) || matched T q ws ||
      (ws.length==k && !(cheapPossible (ws.map Prod.fst)))))

def test (k i : Nat) :=
  let r := FastJumpBench.row (k+1) i
  MaskFast.nodeWith finish k r.1 (FastJumpBench.fastTable (k+1) i k) r.2

set_option maxRecDepth 65536

set_option maxHeartbeats 0

set_option profiler true

set_option profiler.threshold 25

theorem sample1 : cheapPossible [1956,5700,7442,8715,22568,22829,24784]=false := by decide +kernel

theorem sample2 : cheapPossible [6116,7442,8715,13903,18725,22568,24784]=false := by decide +kernel

theorem sample3 : cheapPossible [208,1952,5700,7442,8715,18693,22568]=true := by decide +kernel

theorem sample4 : cheapPossible [6116,7442,8715,13903,18693,22568,24816]=true := by decide +kernel

theorem sample5 : cheapPossible [1952,5700,7442,8715,9739,18693,22568,24784]=false := by decide +kernel

theorem sample6 : cheapPossible [1952,5700,7442,8715,18693,19717,22568,24784]=false := by decide +kernel

theorem sample7 : cheapPossible [1952,5700,7442,8182,8715,18693,22568,24784]=true := by decide +kernel

theorem sample8 : cheapPossible [5700,6116,7442,8715,18693,22568,24784,24816]=true := by decide +kernel

theorem sample9 : cheapPossible [1024,1536,1952,5700,7442,8715,18693,22568,24784]=false := by decide +kernel

theorem sample10 : cheapPossible [1536,1952,5700,7442,7954,8715,18693,22568,24784]=false := by decide +kernel

theorem sample11 : cheapPossible [1952,5700,6116,7442,8022,8715,18693,22568,24784]=true := by decide +kernel

theorem sample12 : cheapPossible [1952,5700,6116,7442,8114,8715,18693,22568,24784]=true := by decide +kernel

theorem k7 : test 6 0=true := by decide +kernel

theorem k8 : test 7 0=true := by decide +kernel

theorem k9 : test 8 0=true := by decide +kernel

theorem k11 : test 10 0=true := by decide +kernel

end CoNum4358.Tiny.QuickBench

