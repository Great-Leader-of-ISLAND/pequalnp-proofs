import PEqualNP.Co2683Stage
import PEqualNP.Co2683Theta

namespace PEqualNP.Research.SignStage
open PEqualNP.Outside.L_meta_1667 (edge)
open CoThetaFreeCore CoThetaNine
theorem frontier (m : Nat) (op : Fin m → Bool) (a b : Fin m → Nat × Bool) (out : Nat × Bool)
    (S : Finset Nat) (v : (Fin 9 → Bool) → Nat → Bool)
    (before : ∀ i, (a i).1 < 10+i.val ∧ (b i).1 < 10+i.val)
    (output : out.1 < 10+m)
    (perm : let ok := fun t : Nat × Bool => t.2=true → t.1=0 ∨ t.1=9 ∨ t.1∈S
            ok out ∧ ∀ i, ok (a i) ∧ ok (b i))
    (vars : ∀ x (i : Fin 9), v x i.val = x i)
    (z : ∀ x, v x 9=false)
    (step : ∀ x i, (v x (10+i.val)) =
       if op i then ((v x (a i).1 ^^ (a i).2) && (v x (b i).1 ^^ (b i).2))
       else ((v x (a i).1 ^^ (a i).2) || (v x (b i).1 ^^ (b i).2)))
    (limit : m+S.card≤14)
    (computed : ∀ x, (v x out.1 ^^ out.2) = edge x) :
    m+S.card=14 ∧ 0∉S ∧ 9∉S ∧
      (CoThetaBits.certifiedSearch 10 CoThetaBits.raw=false → m=14 ∧ S=∅) := by
  classical
  have permission : let ok := fun t : Nat × Bool => t.2=true → t.1=0 ∨ t.1=9 ∨ t.1∈S.erase 9
                    ok out ∧ ∀ i, ok (a i) ∧ ok (b i) := by
    have patch (t : Nat × Bool) (h : t.2=true → t.1=0 ∨ t.1=9 ∨ t.1∈S) (s : t.2=true) :
        t.1=0 ∨ t.1=9 ∨ t.1∈S.erase 9 := by
      rcases h s with z|n|mem
      · exact Or.inl z
      · exact Or.inr (Or.inl n)
      · by_cases e : t.1=9
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (Finset.mem_erase.mpr ⟨e,mem⟩))
    exact ⟨patch _ perm.1,fun i => ⟨patch _ (perm.2 i).1,patch _ (perm.2 i).2⟩⟩
  have h := priced m op a b out (S.erase 9) v before output permission vars z step computed
  have cap := Finset.card_insert_le 0 (S.erase 9)
  have sub := Finset.card_le_card (Finset.erase_subset 9 S)
  have noNine : 9∉S := by
    intro hz
    have cut := Finset.card_erase_lt_of_mem hz
    omega
  have noZero : 0∉S := by
    intro zero
    have inside : 0∈S.erase 9 := Finset.mem_erase.mpr ⟨by decide,zero⟩
    rw [Finset.insert_eq_of_mem inside] at h
    omega
  refine ⟨by omega,noZero,noNine,?_⟩
  intro cert
  let f (j : Nat) (r : Input) := v (fun i => vtx i r) j
  have root (j : Nat) (hj : j<10) : f j∈vertices := by
    by_cases l : j<9
    · let i : Fin 9 := ⟨j,l⟩
      have eq : f j = vtx i := funext (fun r => vars _ i)
      rw [eq]
      exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    · obtain rfl : j=9 := by omega
      have eq : f 9=absentBit := funext (fun r => z _)
      rw [eq]
      exact List.mem_cons_self
  have gates (i : Fin m) : f (10+i.val) = fun r =>
      base (!(op i)) (SignTheta.signed f (a i) r) (SignTheta.signed f (b i) r) := by
    funext r
    have h := step (fun j => vtx j r) i
    cases o : op i <;> simpa [f,base,SignTheta.signed,o] using h
  have target : SignTheta.signed f out=ans := funext (fun r => computed (fun i => vtx i r))
  have bound := SignTheta.tight cert f m a b (fun i => !(op i)) out root before output gates target
  exact ⟨by omega,Finset.card_eq_zero.mp (by omega)⟩
end PEqualNP.Research.SignStage
