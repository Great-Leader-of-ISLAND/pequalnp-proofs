import PEqualNP.CoAO3143Bridge
namespace CoAO3143

def rootPairs : List Sig → List (Sig × Sig)
  | [] => []
  | a :: xs => (xs.map fun b => (a,b)) ++ rootPairs xs

private theorem scan_root (f : Sig → Sig → Bool) (ws : List Sig) :
    scanPairs f ws = (rootPairs ws).any (fun u => f u.1 u.2) := by
  induction ws with
  | nil => rfl
  | cons a xs ih => simp [scanPairs,rootPairs,ih,List.any_map,Function.comp_def]

def rootTry (ws : List Sig) (ab : Sig × Sig) :=
  slowBinary 11 0 (search 11 0) ws (coverage false ws) ab.1 ab.2

def rootBucket (ws : List Sig) (i : Nat) := ((rootPairs ws)[i]?).any (rootTry ws)

theorem root_from_buckets (ws : List Sig) (width : ws.length ≤ 9) (properStart : ws ≠ [target])
    (h : ∀ i < (rootPairs ws).length, rootBucket ws i=false) : search 12 0 ws=false := by
  have failures : (rootPairs ws).any (rootTry ws)=false := by
    apply Bool.eq_false_iff.mpr
    intro hy
    obtain ⟨p,hp,good⟩ := List.any_eq_true.mp hy
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hp
    have bad := h i hi
    simp [rootBucket,List.getElem?_eq_getElem hi,good] at bad
  have pairs : scanPairs (slowBinary 11 0 (search 11 0) ws (coverage false ws)) ws = false := by
    rw [scan_root]
    exact failures
  have h13 : ws.length ≠ 13 := by omega
  have small : ¬(0>11+1 ∨ ws.length>11+1-0+1) := by omega
  change stepTest 11 0 ws (search 11 (0-1)) (search 11 0)=false
  simp [stepTest,binaryMoves,small,h13,properStart,pairs]
end CoAO3143
