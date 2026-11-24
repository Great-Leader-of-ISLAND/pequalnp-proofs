import PEqualNP.CoThetaSeed3024

namespace CoThetaOr1677
open CoAO3143Restriction CoThetaNine PEqualNP.CircuitLowerBounds

def raw : List (Wire SmallInput) := List.ofFn raw7
def sources : List (Wire SmallInput) := raw ++ [con false,con true]
def seed45 : Wire SmallInput := op true (raw7 4) (raw7 5)

def flipPoint (r : SmallInput) : SmallInput :=
  let d := fun j : Nat => if r.val.testBit j then 1 else 0
  ⟨(d 1 + 2*d 0 + 4*d 2 + 8*d 4 + 16*d 3 + 32*d 6 + 64*d 5) % 128,Nat.mod_lt _ (by decide)⟩

private theorem relabel : (∀ i : Fin 7, ∃ j : Fin 7,
    ∀ r,raw7 i (flipPoint r)=raw7 j r) ∧
    (∀ r,ans7 (flipPoint r)=ans7 r) ∧
    (∀ r,seed45 (flipPoint r)=CoThetaSeed3024.seed36 r) := by
  decide +kernel

private theorem distinctSeed : seed45 ∉ sources := by
  intro present
  rcases List.mem_append.mp present with var|value
  · obtain ⟨i,eq⟩ := List.mem_ofFn.mp var
    have unique : ∀ j : Fin 7, ∃ r, raw7 j r ≠ seed45 r := by decide +kernel
    obtain ⟨r,neq⟩ := unique i
    exact neq (congrFun eq r)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at value
    rcases value with eq|eq
    · have fail := congrFun eq (16 : SmallInput)
      exact (by decide : seed45 (16 : SmallInput) ≠ con false (16 : SmallInput)) fail
    · have fail := congrFun eq (0 : SmallInput)
      exact (by decide : seed45 (0 : SmallInput) ≠ con true (0 : SmallInput)) fail

private theorem supplied (w) (m : w ∈ sources) : cut flipPoint w ∈ CoThetaSeed3024.bank := by
  rcases List.mem_append.mp m with var|value
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp var
    obtain ⟨j,hj⟩ := relabel.1 i
    have same : cut flipPoint (raw7 i)=raw7 j := funext hj
    rw [same]
    exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at value
    rcases value with rfl|rfl <;> simp [cut,con,CoThetaSeed3024.bank]

private theorem replay {n ws} (run : Build sources n ws) :
    ∃ m ys, Build CoThetaSeed3024.bank m ys ∧
      (∀ w∈ws,cut flipPoint w∈ys) ∧ (m ≤ n) ∧ (seed45∈ws → m<n) ∧
      cut flipPoint seed45∈ys := by
  induction run with
  | start =>
    have ready : cut flipPoint seed45=CoThetaSeed3024.seed36 := funext relabel.2.2
    exact ⟨0,CoThetaSeed3024.bank,Build.start,supplied,Nat.le_refl _,fun h => (distinctSeed h).elim,
      by rw [ready]; simp [CoThetaSeed3024.bank]⟩
  | @gate k xs pre d a b ha hb ih =>
    obtain ⟨m,ys,build,keep,cost,saved,ready⟩ := ih
    by_cases hit : op d a b=seed45
    · refine ⟨m,ys,build,?_,by omega,fun _ => by omega,ready⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl|old
      · rwa [hit]
      · exact keep w old
    · let z := op d (cut flipPoint a) (cut flipPoint b)
      refine ⟨m+1,z::ys,Build.gate build d _ _ (keep a ha) (keep b hb),?_,by omega,?_,List.mem_cons_of_mem _ ready⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl|old
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (keep w old)
      · intro h
        have old := (List.mem_cons.mp h).resolve_left (fun e => hit e.symm)
        have strict := saved old
        omega

/-- The OR may appear anywhere, can be shared, or can be unused by the output. -/
theorem paid_marked_or {n ws} (run : Build sources n ws)
    (out : ans7∈ws) (marked : seed45∈ws) : 12≤n := by
  obtain ⟨m,ys,built,keep,_,saved,_⟩ := replay run
  have same : cut flipPoint ans7=ans7 := funext relabel.2.1
  have output := keep _ out
  rw [same] at output
  have lb := CoThetaSeed3024.price built output
  have strict := saved marked
  omega

end CoThetaOr1677
