import PEqualNP.CoAO3143Restriction
import PEqualNP.CoAO3143SevenData
import PEqualNP.CoPaid3143

namespace CoAO3143Restriction
open CoThetaNine CoThetaFreeCore

abbrev Small := Fin 7 → Bool
def plain : List (Wire Small) := (List.ofFn (fun i : Fin 7 => fun x : Small => x i))++[con true,con false]
def renumber : Fin 7 → Fin 7 := ![3,0,2,6,4,5,1]
def embed (r : SmallInput) (i : Fin 7) := raw7 (renumber i) r

private theorem free_build {α β : Type} {fs ws : List (Wire α)} {n : Nat} (b : Build fs n ws)
    (f : β→α) (e : β) (seed : List (Wire β))
    (known : ∀ v∈fs, norm e (cut f v)∈seed) :
    ∃ ys, Free seed n ys ∧ ∀ w∈ws,norm e (cut f w)∈ys := by
  induction b with
  | start => exact ⟨seed,Free.start,known⟩
  | @gate k w before d a b ha hb ih =>
    obtain ⟨vs,run,hold⟩ := ih
    let c := normalizedKind d (a (f e)) (b (f e))
    let prog := Free.binary run c (hold a ha) (hold b hb)
    refine ⟨_,prog,?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | old
    · change norm e (fun r => base d ((cut f a) r) ((cut f b) r)) ∈ _
      rw [normalize_binary]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hold z old)

private theorem plain_known : ∀ v∈plain, norm (0 : SmallInput) (cut embed v)∈vertices7 := by
  intro v hv
  rcases List.mem_append.mp hv with raw | const
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp raw
    have eq : norm (0 : SmallInput) (cut embed (fun x : Small => x i))=raw7 (renumber i) := by
      funext r
      have zero : raw7 (renumber i) 0=false := by simp [raw7]
      simp [cut,embed,norm,phase,zero]
    rw [eq]
    exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨_,rfl⟩)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at const
    rcases const with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_self

/-- Concrete seven-vertex price, in the positive straight-line model used
    after restriction. Renumbering goes back to the signed theta theorem. -/
theorem seven_price (lower : SignedLower) {n : Nat} {ws : List (Wire Small)}
    (build : Build plain n ws) (output : CoAO3143.Seven.F ∈ ws) : 11≤n := by
  obtain ⟨vs,free,hold⟩ := free_build build embed 0 vertices7 plain_known
  have label : ∀ r, CoAO3143.Seven.F (embed r)=ans7 r := by decide +kernel
  have z : ans7 0=false := by decide +kernel
  have eq : norm (0 : SmallInput) (cut embed CoAO3143.Seven.F)=ans7 := by
    funext r
    simp [norm,cut,label,z,phase]
  exact lower free (eq ▸ hold _ output)

end CoAO3143Restriction
