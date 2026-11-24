import PEqualNP.CoAO3143Roots
import PEqualNP.CoAO3143Buckets

namespace CoAO3143.Seven
def raw : List Sig := [(0xfc07f0000000000007f01fc000000000001fc07f,0x264c993264c993264c993264c993264c993264c9),(0x3ffffe03f800003f80fffff80fe00000fe03fff,0x8912244891224489122448912244891224489122),(0x3f800000000fe00000fe000000003f800003f80,0x74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d),(0x3fff01fc0000000000fffc07f0000000,0x1c3870e1c3870e1c3870e1c3870e1c3870e1c387),(0xfc000fffc000000007f0003fff000000001fc000,0x58b162c58b162c58b162c58b162c58b162c58b16),(0x1fff800000000000007ffe00000,0x62c58b162c58b162c58b162c58b162c58b162c58),(0xffffffffe000000003ffffffff800000000,0x83060c183060c183060c183060c183060c183060)]
def signed := raw ++ [neg (raw.getD 1 zero)]
def vertex (i : Fin 7) : Sig := raw.getD i.val zero
def ghost := neg (vertex 1)
def F (x : Fin 7→Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 5) || (x 4 && x 6) || (x 3 && x 6)

set_option maxRecDepth 8192 in
theorem starts : initialForms signed raw=true := by decide +kernel

set_option maxRecDepth 8192 in
theorem actual_labels : ∀ (p : Bool) (r : Row), F (fun i => bit p r (vertex i))=p := by decide +kernel

def tryRoot (k : Nat) (ws : List Sig) (ab : Sig×Sig) :=
  slowBinary k 0 (search k 0) ws (coverage false ws) ab.1 ab.2
def bucket (k : Nat) (ws : List Sig) (i : Nat) := ((rootPairs ws)[i]?).any (tryRoot k ws)

theorem eight_distinct : signed.Nodup := by decide +kernel
theorem raw_distinct : raw.Nodup := by decide +kernel
end CoAO3143.Seven
