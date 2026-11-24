import PEqualNP.CoSharedAnd
namespace PEqualNP.Research.SharedCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1672.Main1672

theorem targetRows (C : Circuit) (ws : List Sig) (allValid : ∀ a ∈ ws, Valid a) (h : FanInTwo C)
    (rows : ∀ (s : Bool) (i : Fin 414), C.eval (ws.map (bit s i)) = s) :
    target ∈ execute C.gates ws := by
  let w := execute C.gates ws
  have hwv : ∀ a ∈ w, Valid a := execute_valid C.gates ws allValid
  have hproj (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates ws).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ allValid (fun g hg => (h g hg).1)]
    exact rows s i
  have hvout : Valid (w.getD C.output zero) := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro i
      rw [target, testBit_top]
      by_cases hi : i < 414
      · simpa [bit, hi] using hproj true ⟨i, hi⟩
      · rw [hvout.1 i (by omega)]; simp [hi]
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 414
      · simpa [bit, target] using hproj false ⟨i, hi⟩
      · rw [hvout.2 i (by omega), target]; exact (Nat.zero_testBit i).symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

theorem tail_lower (D : Circuit) (hfan : FanInTwo D) (a b : Sig) (av : Valid a) (bv : Valid b)
    (rows : ∀ (s : Bool) (i : Fin 414),
      D.eval ((raw ++ [a,b]).map (bit s i)) = s)
    (hbound : ∀ {k t : Nat} {S : Finset Sig}, Live k t S → (∀ c ∈ S, c ∈ raw ++ [a,b]) → 14 ≤ k) :
    14 ≤ D.size := by
  have hv : ∀ c ∈ raw ++ [a,b], Valid c := by
    intro c hc
    rcases List.mem_append.mp hc with r | r
    · exact raw_valid _ r
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at r
      rcases r with rfl | rfl
      · exact av
      · exact bv
  obtain ⟨k,t,S,hk,live,sub⟩ := extract D.gates _ hv hfan (targetRows D _ hv hfan rows)
  exact (hbound live sub).trans hk

theorem two_ands (i j r : Fin 9) (hi : ¬ (i.val = 4 ∨ i.val = 6 ∨ i.val = 7))
    (D : Circuit) (hfan : FanInTwo D)
    (he : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x i && x j,x i && x r]) = edgeF x) :
    14 ≤ D.size := by
  let v (p : Fin 9) := raw.getD p.val zero
  have vr (p : Fin 9) : v p ∈ raw := by
    change raw.getD p.val zero ∈ raw
    rw [← raw_id]
    exact List.mem_ofFn.mpr ⟨p,rfl⟩
  apply tail_lower D hfan (bin false (v i) (v j)) (bin false (v i) (v r))
    (valid_bin (raw_valid _ (vr _)) (raw_valid _ (vr _)))
    (valid_bin (raw_valid _ (vr _)) (raw_valid _ (vr _)))
  · intro s k
    have h := he (sample s k)
    rw [sample_list,sample_ok] at h
    simpa [List.map_append,bit_bin,v,sample] using h
  · intro k t S l h
    exact SharedAnd.and_pair i hi l _ _ (vr _) (vr _) h

theorem and_not (i j : Fin 9) (hi : ¬ (i.val = 4 ∨ i.val = 6 ∨ i.val = 7))
    (D : Circuit) (hfan : FanInTwo D)
    (he : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x i && x j,!x i]) = edgeF x) :
    14 ≤ D.size := by
  let v (p : Fin 9) := raw.getD p.val zero
  have vr (p : Fin 9) : v p ∈ raw := by
    change raw.getD p.val zero ∈ raw
    rw [← raw_id]
    exact List.mem_ofFn.mpr ⟨p,rfl⟩
  apply tail_lower D hfan (bin false (v i) (v j)) (neg (v i))
    (valid_bin (raw_valid _ (vr _)) (raw_valid _ (vr _))) (valid_neg (raw_valid _ (vr _)))
  · intro s k
    have h := he (sample s k)
    rw [sample_list,sample_ok] at h
    simpa [List.map_append,bit_bin,bit_neg s k (raw_valid _ (vr i)),v,sample] using h
  · intro k t S l h
    exact SharedAnd.and_then_invert i hi l _ (vr _) h

end PEqualNP.Research.SharedCircuit
