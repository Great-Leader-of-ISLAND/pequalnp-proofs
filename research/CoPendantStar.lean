import PEqualNP.Outside.L_meta_1737

namespace CoPendantStar

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1737 (gate_elim_at one_gate_at)

def star {n : ℕ} (f : (Fin n → Bool) → Bool) (v u w : Fin n) (x : Fin n → Bool) : Bool :=
  f x || (x u && (x v || x w))

def half {n : ℕ} (f : (Fin n → Bool) → Bool) (v u : Fin n) (b : Bool) (x : Fin n → Bool) : Bool :=
  f x || (x u && (x v || b))

theorem arm_lower {n k s : ℕ} {f : (Fin (n+1) → Bool) → Bool}
    (v u w : Fin (n+1)) (vu : v≠u) (vw : v≠w) (uw : u≠w)
    (oldU : ∀ x b, f (Function.update x u b) = f x)
    (oldW : ∀ x b, f (Function.update x w b) = f x)
    (empty : f (fun _ => false) = false)
    (single : f (Function.update (fun _ => false) v true) = false)
    (nc : ∃ x y, f x ≠ f y)
    (positive : 0 < k) (lower : ∀ size, HasCircuitSize (n+1) f size → k ≤ size)
    (original : HasCircuitSize (n+1) (star f v u w) s) : k + 3 ≤ s := by
  classical
  have wfix (b : Bool) (x : Fin (n+1) → Bool) :
      star f v u w (Function.update x w b) = half f v u b x := by
    simp [star,half,oldW,Function.update_of_ne uw,Function.update_of_ne vw]
  have uoff (b : Bool) (x : Fin (n+1) → Bool) :
      half f v u b (Function.update x u false) = f x := by
    simp [half,oldU]
  have depW : ∃ x, star f v u w (Function.update x w (!x w)) ≠ star f v u w x := by
    refine ⟨Function.update (fun _ => false) u true,?_⟩
    simp [star,oldU,oldW,empty,Function.update_of_ne vu,Function.update_of_ne vw,Function.update_of_ne uw,Function.update_of_ne uw.symm]
  have activeW (b : Bool) : ∃ x y, star f v u w (Function.update x w b) ≠
      star f v u w (Function.update y w b) := by
    obtain ⟨x,y,ne⟩ := nc
    exact ⟨Function.update x u false,Function.update y u false,by simpa only [wfix,uoff] using ne⟩
  obtain ⟨b,t,budget,circuit⟩ := gate_elim_at n (star f v u w) w s depW activeW original
  have eqW : (fun x => star f v u w (Function.update x w b))=half f v u b := funext (wfix b)
  rw [eqW] at circuit
  have depU : ∃ x, half f v u b (Function.update x u (!x u)) ≠ half f v u b x := by
    refine ⟨Function.update (fun _ => false) v true,?_⟩
    simp [half,oldU,single,Function.update_of_ne vu,Function.update_of_ne vu.symm]
  have actU : ∃ x y, half f v u b (Function.update x u false) ≠
      half f v u b (Function.update y u false) := by
    obtain ⟨x,y,ne⟩ := nc
    exact ⟨x,y,by simpa only [uoff] using ne⟩
  have eqU : (fun x => half f v u b (Function.update x u false))=f := funext (uoff b)
  cases t with
  | zero =>
    obtain ⟨C,ok,le,ev⟩ := circuit
    have larger : HasCircuitSize (n+1) (half f v u b) (0+1) := ⟨C,ok,by omega,ev⟩
    have reduced := one_gate_at n (half f v u b) u false 0 depU actU larger
    rw [eqU] at reduced
    have := lower 0 reduced
    omega
  | succ j =>
    have reduced := one_gate_at n (half f v u b) u false j depU actU circuit
    rw [eqU] at reduced
    have := lower j reduced
    omega

end CoPendantStar
