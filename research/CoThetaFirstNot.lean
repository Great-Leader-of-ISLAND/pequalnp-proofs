import PEqualNP.Outside.L_meta_517

/- The public theta frontier theorem is due to L-meta-517.  The extension along
   x ↦ (x, ¬xⱼ) below handles a supplied first inverter, including an unused
   input, unused gates, noncanonical pins and invalid outputs. -/
namespace CoThetaFirstNot
open Live514 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def extend (j : Fin 7) (x : Fin 7 → Bool) : Fin 8 → Bool := Fin.snoc x (!(x j))

def pack (j : Fin 7) (a : BFn 8) := encL (fun x => a (extend j x)) rows517

def columns (j : Fin 7) : List Nat :=
  (List.ofFn fun i : Fin 8 => fun x : Fin 8 → Bool => x i).map (pack j)

/-- An actual tail of fan-in at most two gives a live run of at most its
    length even though its eighth supplied literal depends on the first seven. -/
theorem tail_run (j : Fin 7) (D : Circuit)
    (hfan : FanInTwo D)
    (hsize : D.size ≤ 10)
    (hag : ∀ x : Fin 7 → Bool, D.eval (List.ofFn x ++ [!(x j)]) = f517 x) :
    ∃ s ≤ 10, ∃ ws : List Nat, ws.Sublist (columns j) ∧
      NatRun (mask 232) (goal 232) s ws := by
  let f : BFn 8 := fun y => D.eval (List.ofFn y)
  have hag' (x : Fin 7 → Bool) : f (extend j x) = f517 x := by
    simpa only [f, extend, ofFn_snoc] using hag x
  have hnc : ∃ y y' : Fin 8 → Bool, f y ≠ f y' := by
    refine ⟨extend j (fun _ => false), extend j (fun _ => true), ?_⟩
    rw [hag', hag']; decide
  have hs : HasCircuitSize 8 f 10 := ⟨D, hfan, hsize, fun _ => rfl⟩
  obtain ⟨s, hbound, vs, hsub, hrun⟩ := exists_run f hnc 10 hs
  have hr : NatRun (mask 232) (pack j f) s (vs.map (pack j)) :=
    Run.map (inv := invF) (meet := meetF) (join := joinF)
      (inv' := (· ^^^ mask 232)) (meet' := (· &&& ·)) (join' := (· ||| ·)) (pack j)
      (fun a => by rw [mask517]; exact encL_inv (fun x => a (extend j x)) rows517)
      (fun a b => encL_and (fun x => a (extend j x)) (fun x => b (extend j x)) rows517)
      (fun a b => encL_or (fun x => a (extend j x)) (fun x => b (extend j x)) rows517) hrun
  have hgoal : pack j f = goal 232 := by
    unfold pack
    rw [show (fun x => f (extend j x)) = f517 from funext hag', enc_goal517]
  rw [hgoal] at hr
  exact ⟨s, hbound, vs.map (pack j), hsub.map _, hr⟩

/-- Executable sound upper approximation of the exact-length realizable runs. -/
def possible (q : Nat) : Nat → List Nat → Bool
  | 0, ws => decide (ws = [goal q])
  | k+1, ws => covers q (k+1) ws &&
      next (mask q) (k+2-ws.length) ws (fun _ vs => possible q k vs)

theorem possible_of_run {q s : Nat} {ws : List Nat}
    (h : NatRun (mask q) (goal q) s ws) : possible q s ws = true := by
  induction s generalizing ws with
  | zero => simp [possible, zero_done h rfl]
  | succ k ih =>
    apply Bool.and_eq_true_iff.mpr
    exact ⟨covers_ok h, next_complete h k rfl ws (.refl ws) _ (fun _ _ hv => ih hv)⟩

/-- All input sublists are allowed because cleanup may discard either sign. -/
def reject (j : Fin 7) : Bool :=
  (List.range 11).all fun s => (columns j).sublists.all fun ws => !(possible 232 s ws)

theorem exclusion (j : Fin 7) (hc : reject j = true) (D : Circuit)
    (hfan : FanInTwo D) (hsize : D.size ≤ 10) :
    ¬ ∀ x : Fin 7 → Bool, D.eval (List.ofFn x ++ [!(x j)]) = f517 x := by
  intro hag
  obtain ⟨s, hs, ws, hsub, hrun⟩ := tail_run j D hfan hsize hag
  have h1 := List.all_eq_true.mp hc s (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 ws (List.mem_sublists.mpr hsub)
  simp [possible_of_run hrun] at h2

end CoThetaFirstNot
