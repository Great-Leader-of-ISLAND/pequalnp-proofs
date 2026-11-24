import PEqualNP.CoPaid3143
namespace CoThetaCuts3024
open CoThetaNine CoThetaFreeCore

def embedding (j : Fin 9) : Fin 7 → Fin 9 := ![![2,8,3,1,6,7,5],![3,5,8,2,7,4,0],![0,8,5,1,6,4,3],![1,5,0,2,7,6,8],![2,5,7,1,0,3,8],![1,8,6,0,5,2,3],![1,3,2,0,4,6,8],![0,3,4,1,2,5,8],![0,2,1,4,3,5,7]] j
def coordinate (j : Fin 9) : Fin 9 → Option (Fin 7) := ![![none,some 3,some 0,some 2,none,some 6,some 4,some 5,some 1],![some 6,none,some 3,some 0,some 5,some 1,none,some 4,some 2],![some 0,some 3,none,some 6,some 5,some 2,some 4,none,some 1],![some 2,some 0,some 3,none,none,some 1,some 5,some 4,some 6],![some 4,some 3,some 0,some 5,none,some 1,none,some 2,some 6],![some 3,some 0,some 5,some 6,none,some 4,some 2,none,some 1],![some 3,some 0,some 2,some 1,some 4,none,some 5,none,some 6],![some 0,some 3,some 4,some 1,some 2,some 5,none,none,some 6],![some 0,some 2,some 1,some 4,some 3,some 5,none,some 6,none]] j
def plant (j : Fin 9) (r : SmallInput) : Input :=
  row ((List.ofFn (fun i : Fin 7 => if raw7 i r then (1:Nat) <<< (embedding j i).val else 0)).sum)

set_option maxRecDepth 8192 in
theorem label : ∀(j : Fin 9) (r : SmallInput), ans (plant j r)=ans7 r := by decide +kernel

set_option maxRecDepth 8192 in
theorem column : ∀ (j : Fin 9) (i : Fin 9) (r : SmallInput),
    vtx i (plant j r)=match coordinate j i with | none => false | some t => raw7 t r := by decide +kernel

theorem known (j : Fin 9) : ∀ w ∈ vertices, restrict (plant j) w ∈ vertices7 := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl|hw
  · exact List.mem_cons_self
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  cases e : coordinate j i with
  | none =>
    have h : restrict (plant j) (vtx i)=absentBit := by
      funext r
      change vtx i (plant j r)=false
      simpa [e] using column j i r
    rw [h]
    exact List.mem_cons_self
  | some t =>
    have h : restrict (plant j) (vtx i)=raw7 t := by
      funext r
      change vtx i (plant j r)=raw7 t r
      simpa [e] using column j i r
    rw [h]
    exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨t,rfl⟩)

/-- A putative fourteen-binary-gate run may lose at most three gates on each of
    the nine theta restrictions. Registered traces need no read-once condition. -/
theorem all_cuts (price : SignedLower) (j : Fin 9) {gs : List (TraceGate Input)}
    (ok : sufficient vertices ans gs) (length : gs.length≤14) : saved (plant j) gs≤3 := by
  obtain ⟨ws,run,hold⟩ := restrict_trace (plant j) gs ok.1 (Free.start (raw:=vertices7))
    List.mem_cons_self (known j)
  have out := hold ans ok.2
  have solved : restrict (plant j) ans=ans7 := funext (label j)
  rw [solved] at out
  have low := price run out
  have accounted' := accounted (plant j) gs
  omega
#print axioms CoThetaCuts3024.all_cuts
end CoThetaCuts3024
