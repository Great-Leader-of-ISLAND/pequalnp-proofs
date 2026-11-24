import PEqualNP.CoRoot3174
import PEqualNP.CoNine3024PaidState
import PEqualNP.CoNine3024Path

namespace CoRootGeometry3174
open CoNine3024 CoNine3024Rows CoNine3024Budget CoNine3024PaidState
open CoAO3143Restriction CoThetaFreeCore CoThetaNine
noncomputable section
local instance : DecidableEq (Wire Input) := Classical.decEq _

def combined (b : Fin 3) : Wire Input := op true (vtx 1) (vtx (CoRoot3174.other b))
def invert : Wire Input := fun r => !(vtx 0 r)

theorem head_value (b : Fin 3) (inv : Bool) :
    value (CoRoot3174.head b inv)=combined b := by
  unfold CoRoot3174.head combined
  rw [operation_value,raw_value,raw_value]

theorem invert_value : value (inverseAtom 0)=invert := inverse_value 0 (by decide)

theorem images (b : Fin 3) (inv : Bool) :
    ((CoRoot3174.root b inv).wires.map value) =
    ((List.ofFn vtx ++ [combined b]) ++ (if inv then [invert] else [])) := by
  have raws (p : Fin 11) : (List.ofFn (rootAtom p)).map value=List.ofFn vtx := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact raw_value p i
  cases inv <;> simp [CoRoot3174.root,CoRoot3174.mode,raw_value,head_value,invert_value]

theorem good (b : Fin 3) (inv : Bool) :
    ∀ a∈(CoRoot3174.root b inv).wires, Good (CoRoot3174.mode inv) a := by
  intro a ha
  rcases List.mem_append.mp ha with old|negative
  · rcases List.mem_append.mp old with src|hd
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp src
      exact root_good _ _
    · obtain rfl := List.mem_singleton.mp hd
      exact operation_good _ true (root_good _ _) (root_good _ _)
  · cases inv
    · simp at negative
    · obtain rfl := List.mem_singleton.mp negative
      exact inverse_good _

private theorem map_nd (ws : List Atom) (nd : (ws.map Atom.full).Nodup) : (ws.map value).Nodup := by
  induction ws with
  | nil => simp
  | cons a as ih =>
    obtain ⟨nf,tail⟩ := List.nodup_cons.mp nd
    refine List.nodup_cons.mpr ⟨?_,ih tail⟩
    intro hit
    obtain ⟨t,ht,eq⟩ := List.mem_map.mp hit
    exact nf (List.mem_map.mpr ⟨t,ht,(CoNine3024Transition.full_eq _ _).mpr eq⟩)

set_option maxRecDepth 8192 in
private theorem distinct : ∀ (b : Fin 3) (inv : Bool),
    ((CoRoot3174.root b inv).wires.map Atom.full).Nodup := by decide +kernel

theorem unique (b : Fin 3) (inv : Bool) :
    ((CoRoot3174.root b inv).wires.map value).Nodup := map_nd _ (distinct b inv)

theorem initial (b : Fin 3) (inv : Bool) {k : Nat} (lim : k≤13) :
    Accounts (CoRoot3174.root b inv) k := by
  let p := CoRoot3174.mode inv
  let m := CoRoot3174.other b
  let A := rootAtom p 1
  let B := rootAtom p m
  refine ⟨fun j => max (digit A j) (digit B j),?_,?_⟩
  · change A.fixed ||| B.fixed = _
    rw [packed_good (root_good p 1),packed_good (root_good p m)]
    exact pack_or _ _ (digit_bound A) (digit_bound B)
  · intro j
    let f := CoThetaCuts3024.plant j
    have raw := CoFrontier3024Seed.raw_nine j
    have valA : value A=vtx 1 := raw_value p 1
    have valB : value B=vtx m := raw_value p m
    obtain ⟨n,ws,prog,charge,keep,out⟩ :=
      CoFrontier3024Seed.advance Free.start true (cut f (vtx 1)) (cut f (vtx m))
        (raw 1) (raw m) (digit A j) (digit B j)
        (digit_bound A _) (digit_bound B _)
        (valA ▸ digit_correct A j) (valB ▸ digit_correct B j)
    refine ⟨n,ws,prog,?_,?_⟩
    · change n + max (digit A j) (digit B j) + k ≤ 14
      omega
    intro w hw
    have hit : value w∈(CoRoot3174.root b inv).wires.map value := List.mem_map.mpr ⟨_,hw,rfl⟩
    rw [images] at hit
    rcases List.mem_append.mp hit with old|neg
    · rcases List.mem_append.mp old with coord|hd
      · obtain ⟨i,e⟩ := List.mem_ofFn.mp coord
        rw [←e]
        exact keep _ (raw i)
      · rw [List.mem_singleton.mp hd]
        exact out
    · cases inv with
      | false => simp at neg
      | true =>
        rw [List.mem_singleton.mp neg]
        exact CoFrontier3024Price.neg_known (keep _ (raw 0))

#print axioms initial
end
end CoRootGeometry3174
