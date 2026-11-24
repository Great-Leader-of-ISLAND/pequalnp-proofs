import PEqualNP.Outside.L_meta_1672
namespace PEqualNP.Research.NonedgeMono
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

def head (x : Fin 9 → Bool) : Bool := x 0 && x 3

def edges : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

def pair (e : Fin 9 × Fin 9) (i : Fin 9) : Bool := decide (i = e.1 ∨ i = e.2)

theorem edge_witness {x : Fin 9 → Bool} (hx : edgeF x = true) :
    ∃ y : Fin 9 → Bool, (∀ i, y i = true → x i = true) ∧ edgeF y = true ∧ head y = false := by
  have ex : edges.any (fun e => x e.1 && x e.2) = true := by
    simpa [edgeF,edges,Bool.or_assoc] using hx
  obtain ⟨p,hp,ht⟩ := List.any_eq_true.mp ex
  have concrete : ∀ e ∈ edges, edgeF (pair e) = true ∧ head (pair e) = false := by decide +kernel
  refine ⟨pair p,?_,concrete _ hp⟩
  intro i h
  have hb := Bool.and_eq_true_iff.mp ht
  rcases of_decide_eq_true h with eq | eq
  · simpa [eq] using hb.1
  · simpa [eq] using hb.2

def tailF (D : Circuit) (x : Fin 9 → Bool) (b : Bool) := D.eval (List.ofFn x ++ [b])

theorem erase_head (D : Circuit)
    (rawMono : ∀ x y, (∀ i, x i = true → y i = true) → tailF D x false = true → tailF D y false = true)
    (headMono : ∀ x, tailF D x false = true → tailF D x (head x) = true)
    (realizes : ∀ x, tailF D x (head x) = edgeF x) : ∀ x, tailF D x false = edgeF x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    exact (realizes x) ▸ headMono x h
  · intro h
    obtain ⟨y,le,yes,no⟩ := edge_witness h
    have atY := (realizes y).trans yes
    rw [no] at atY
    exact rawMono y x le atY

theorem lower (D : Circuit) (fan : FanInTwo D)
    (zeroSlot : ∀ x : Fin 9 → Bool, tailF D x false = edgeF x) : 15 ≤ D.size := by
  let w := raw ++ [zero]
  have hw : ∀ a ∈ w, Valid a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact raw_valid _ ha
    · obtain rfl := List.mem_singleton.mp ha
      exact valid_zero
  have proj (s : Bool) (i : Fin 414) : D.eval (w.map (bit s i)) = s := by
    have eq := zeroSlot (sample s i)
    rw [tailF,sample_list,sample_ok] at eq
    simpa [w,bit_zero] using eq
  obtain ⟨k,t,S,hk,hl,sub⟩ := extract D.gates w hw fan (targetRows D w hw fan proj)
  have hs : ∀ z ∈ S, z ∈ raw := by
    intro z hz
    rcases List.mem_append.mp (sub z hz) with h | h
    · exact h
    · obtain rfl := List.mem_singleton.mp h
      exact ((live_proper hl _ hz).2.1 rfl).elim
  have eq := necessary hl hs
  subst S
  by_contra h
  change ¬ 15 ≤ D.gates.length at h
  have h14 : k ≤ 14 := by omega
  have size := live_size hl
  rw [List.toFinset_card_of_nodup raw_nd] at size
  have len : raw.length = 9 := rfl
  exact rootImpossible t (by omega) k h14 raw.toFinset rootTag rootWires_rep
    (restrict_live hl (rootTag_ok h14))

end PEqualNP.Research.NonedgeMono
