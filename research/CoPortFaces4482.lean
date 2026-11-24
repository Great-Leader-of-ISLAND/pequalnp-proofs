import Mathlib
namespace CoPortFaces4482

abbrev Kind := Fin 6
abbrev Corner := Fin 4
/-- Four corners are 00,10,01,11. Kinds are 0,1,x,y,AND,OR. -/
def code : Kind → Nat := ![0,15,10,12,8,14]
def value (k : Kind) (r : Corner) := (code k).testBit r.val
def decode : Nat → Kind | 0 => 0 | 15 => 1 | 10 => 2 | 12 => 3 | 8 => 4 | _ => 5
def combine (d : Bool) (a b : Kind) :=
  decode (if d then code a ||| code b else code a &&& code b)

theorem eval_combine (d : Bool) : ∀ (a b : Kind) (r : Corner),
  value (combine d a b) r = (if d then value a r || value b r else value a r && value b r) := by
  cases d <;> decide +kernel

/-- Every monotone four-corner pattern has one of these six types. -/
theorem classified (a b c d : Bool) (ab : a=true → b=true) (ac : a=true → c=true)
    (bd : b=true → d=true) (cd : c=true → d=true) :
    ∃ k : Kind, value k 0=a ∧ value k 1=b ∧ value k 2=c ∧ value k 3=d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all <;> decide +kernel

def Separates (ws : Finset Kind) (t : Kind) : Prop :=
  ∀ a b : Corner, value t a ≠ value t b → ∃ z∈ws, value z a ≠ value z b

private def Cands (u v : Corner) (a b : Kind) :=
  ∀ k : Kind, value k u ≠ value k v → k=a ∨ k=b

private theorem edge01 : Cands 0 1 2 5 := by unfold Cands; decide +kernel
private theorem edge02 : Cands 0 2 3 5 := by unfold Cands; decide +kernel
private theorem edge13 : Cands 1 3 3 4 := by unfold Cands; decide +kernel
private theorem edge23 : Cands 2 3 2 4 := by unfold Cands; decide +kernel
private theorem diagonal : Cands 1 2 2 3 := by unfold Cands; decide +kernel

private theorem needs {ws t u v a b} (h : Separates ws t) (diff : value t u ≠ value t v)
    (cs : Cands u v a b) : a∈ws ∨ b∈ws := by
  obtain ⟨k,m,d⟩ := h u v diff
  rcases cs k d with rfl|rfl
  · exact Or.inl m
  · exact Or.inr m

theorem projection_x {ws : Finset Kind} (h : Separates ws 2) :
    (2:Kind)∈ws ∨ ((4:Kind)∈ws ∧ (3:Kind)∈ws ∧ (5:Kind)∈ws) := by
  by_cases direct : (2:Kind)∈ws
  · exact Or.inl direct
  · exact Or.inr ⟨(needs h (by decide) edge23).resolve_left direct,
      (needs h (by decide) diagonal).resolve_left direct,
      (needs h (by decide) edge01).resolve_left direct⟩

theorem projection_y {ws : Finset Kind} (h : Separates ws 3) :
    (3:Kind)∈ws ∨ ((4:Kind)∈ws ∧ (2:Kind)∈ws ∧ (5:Kind)∈ws) := by
  by_cases direct : (3:Kind)∈ws
  · exact Or.inl direct
  · exact Or.inr ⟨(needs h (by decide) edge13).resolve_left direct,
      (needs h (by decide) diagonal).resolve_right direct,
      (needs h (by decide) edge02).resolve_left direct⟩

theorem conjunction {ws : Finset Kind} (h : Separates ws 4) :
    (4:Kind)∈ws ∨ ((2:Kind)∈ws ∧ (3:Kind)∈ws) := by
  by_cases direct : (4:Kind)∈ws
  · exact Or.inl direct
  · exact Or.inr ⟨(needs h (by decide) edge23).resolve_right direct,
      (needs h (by decide) edge13).resolve_right direct⟩

theorem disjunction {ws : Finset Kind} (h : Separates ws 5) :
    (5:Kind)∈ws ∨ ((2:Kind)∈ws ∧ (3:Kind)∈ws) := by
  by_cases direct : (5:Kind)∈ws
  · exact Or.inl direct
  · exact Or.inr ⟨(needs h (by decide) edge01).resolve_right direct,
      (needs h (by decide) edge02).resolve_right direct⟩

inductive Future (ws : Finset Kind) : Kind → Prop
  | given {a} : a∈ws → Future ws a
  | step {a b} : Future ws a → Future ws b → (d : Bool) → Future ws (combine d a b)

theorem missing_source {ws : Finset Kind} {axis : Kind} (p : axis=2 ∨ axis=3)
    (missing : axis∉ws) {v} (h : Future ws v) : v∈ws := by
  have one (d : Bool) : ∀ (axis a b : Kind), (axis=2 ∨ axis=3) → a≠axis → b≠axis →
      combine d a b=a ∨ combine d a b=b := by
    cases d <;> decide +kernel
  induction h with
  | given m => exact m
  | @step a b _ _ d ha hb =>
    have aa : a≠axis := by rintro rfl; exact missing ha
    have bb : b≠axis := by rintro rfl; exact missing hb
    exact (one d axis a b p aa bb).elim (fun e => e.symm ▸ ha) (fun e => e.symm ▸ hb)

end CoPortFaces4482
