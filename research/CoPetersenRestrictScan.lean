import PEqualNP.CoPetersenRestrict

namespace PEqualNP.Research.PetersenRestrict

open PEqualNP.CircuitLowerBounds

def read (ws : List Bool) (i : ℕ) : Bool := ws.getD i false

def act (ws : List Bool) (g : Gate) : List Bool := ws ++ [g.op.eval (g.inputs.map (read ws))]

def run (gs : List Gate) (ws : List Bool) : List Bool := gs.foldl act ws

private theorem run_cons (g : Gate) (gs : List Gate) (ws : List Bool) :
    run (g :: gs) ws = run gs (act ws g) := rfl

def Wire.Bounded : Wire → ℕ → Prop
  | .fixed _, _ => True
  | .port i, n => i < n

/-- Freeze a dangling alias at the time of the lookup, before future wires exist. -/
def cap (n : ℕ) : Wire → Wire
  | .fixed b => .fixed b
  | .port i => if i < n then .port i else .fixed false

private theorem cap_bounded (n : ℕ) (p : Wire) : (cap n p).Bounded n := by
  cases p with
  | fixed b => trivial
  | port i => by_cases h : i < n <;> simp [cap, h, Wire.Bounded]

private theorem cap_val (ws : List Bool) (p : Wire) :
    (cap ws.length p).val (read ws) = p.val (read ws) := by
  cases p with
  | fixed b => rfl
  | port i =>
    by_cases h : i < ws.length
    · simp [cap, h]
    · have hi : ws.length ≤ i := by omega
      simp [cap, h, Wire.val, read, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private theorem at_new (ws : List Bool) (b : Bool) : read (ws ++ [b]) ws.length = b := by
  simp only [read, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl ws.length)]
  simp

private theorem stable (p : Wire) (ws : List Bool) (b : Bool) (hp : p.Bounded ws.length) :
    p.val (read (ws ++ [b])) = p.val (read ws) := by
  cases p with
  | fixed v => rfl
  | port i =>
    change i < ws.length at hp
    simp only [Wire.val, read, List.getD_eq_getElem?_getD, List.getElem?_append_left hp]

private theorem stable_map (refs : List Wire) (ws : List Bool) (b : Bool)
    (hb : ∀ r ∈ refs, r.Bounded ws.length) :
    refs.map (Wire.val (read (ws ++ [b]))) = refs.map (Wire.val (read ws)) := by
  induction refs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons]
    rw [stable r ws b (hb r (by simp))]
    rw [ih (fun z hz => hb z (List.mem_cons_of_mem r hz))]

/-- The association table represents every former wire, not only the designated output. -/
structure Represents (refs : List Wire) (old new : List Bool) : Prop where
  bounded : ∀ r ∈ refs, r.Bounded new.length
  values : refs.map (Wire.val (read new)) = old

private theorem lookup_map (refs : List Wire) (new : List Bool) (i : ℕ) :
    (resolve refs i).val (read new) = read (refs.map (Wire.val (read new))) i := by
  induction refs generalizing i with
  | nil => cases i <;> rfl
  | cons r rs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem Represents.lookup {refs : List Wire} {old new : List Bool}
    (h : Represents refs old new) (i : ℕ) :
    (resolve refs i).val (read new) = read old i := by
  rw [lookup_map, h.values]

private theorem Represents.skip {refs : List Wire} {old new : List Bool}
    (h : Represents refs old new) (g : Gate) (hg : Legal g) (w : Wire)
    (hp : simplify refs g = .reuse w) :
    Represents (refs ++ [cap new.length w]) (act old g) new := by
  have hv := simplify_val refs g hg (read old) (read new) h.lookup
  rw [hp] at hv
  change w.val (read new) = g.op.eval (g.inputs.map (read old)) at hv
  constructor
  · intro p hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.bounded p hm
    · have he : p = cap new.length w := by simpa using hm
      subst p
      exact cap_bounded _ _
  · simp only [List.map_append, List.map_cons, List.map_nil, h.values, cap_val, hv, act]

private theorem Represents.emit {refs : List Wire} {old new : List Bool}
    (h : Represents refs old new) (g : Gate) (hg : Legal g) (a : Gate)
    (hp : simplify refs g = .emit a) :
    Represents (refs ++ [.port new.length]) (act old g) (act new a) := by
  let b := a.op.eval (a.inputs.map (read new))
  have hv := simplify_val refs g hg (read old) (read new) h.lookup
  rw [hp] at hv
  change b = g.op.eval (g.inputs.map (read old)) at hv
  change Represents _ _ (new ++ [b])
  constructor
  · intro p hm
    rcases List.mem_append.mp hm with hm | hm
    · have hb := h.bounded p hm
      cases p with
      | fixed b => trivial
      | port i =>
        change i < new.length at hb
        simpa only [Wire.Bounded, List.length_append, List.length_cons, List.length_nil]
          using Nat.lt.step hb
    · have he : p = Wire.port new.length := by simpa using hm
      subst p
      simp [Wire.Bounded]
  · simp only [List.map_append, List.map_cons, List.map_nil]
    rw [stable_map refs new b h.bounded, h.values]
    change old ++ [read (new ++ [b]) new.length] = old ++ [g.op.eval (g.inputs.map (read old))]
    rw [at_new, hv]

structure Compiled where
  refs : List Wire
  gates : List Gate
  trace : List Plan

/-- Keep the action taken at each old gate, allowing distinct eliminations to be counted. -/
def scan : List Gate → ℕ → List Wire → Compiled
  | [], _, refs => ⟨refs, [], []⟩
  | g :: gs, n, refs =>
    match simplify refs g with
    | .reuse w =>
      let t := scan gs n (refs ++ [cap n w])
      ⟨t.refs, t.gates, .reuse w :: t.trace⟩
    | .emit a =>
      let t := scan gs (n + 1) (refs ++ [.port n])
      ⟨t.refs, a :: t.gates, .emit a :: t.trace⟩

theorem scan_sound : ∀ (gs : List Gate), (∀ g ∈ gs, Legal g) →
    ∀ (refs : List Wire) (old new : List Bool), Represents refs old new →
    Represents (scan gs new.length refs).refs (run gs old)
      (run (scan gs new.length refs).gates new) := by
  intro gs
  induction gs with
  | nil =>
    intro _ refs old new h
    exact h
  | cons g gs ih =>
    intro hlegal refs old new h
    have hg := hlegal g (by simp)
    have ht : ∀ a ∈ gs, Legal a := fun a ha => hlegal a (List.mem_cons_of_mem g ha)
    cases hp : simplify refs g with
    | reuse w =>
      have hh := ih ht _ _ _ (h.skip g hg w hp)
      simpa only [scan, hp, run_cons] using hh
    | emit a =>
      have hh := ih ht _ _ _ (h.emit g hg a hp)
      have hl : (act new a).length = new.length + 1 := by simp [act]
      simpa only [scan, hp, run_cons, hl] using hh

/-- Count unused gate slots in the trace instead of requiring any normal-form hypothesis. -/
def saved : List Plan → ℕ
  | [] => 0
  | .reuse _ :: ps => saved ps + 1
  | .emit _ :: ps => saved ps

theorem scan_price : ∀ (gs : List Gate) (n : ℕ) (refs : List Wire),
    (scan gs n refs).gates.length + saved (scan gs n refs).trace = gs.length := by
  intro gs
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro n refs
    cases hp : simplify refs g with
    | reuse w =>
      have hh := ih n (refs ++ [cap n w])
      simp only [scan, hp, saved, List.length_cons]
      omega
    | emit a =>
      have hh := ih (n+1) (refs ++ [.port n])
      simp only [scan, hp, saved, List.length_cons]
      omega

theorem scan_legal : ∀ (gs : List Gate) (n : ℕ) (refs : List Wire),
    ∀ a ∈ (scan gs n refs).gates, Legal a := by
  intro gs
  induction gs with
  | nil => intro n refs a ha; cases ha
  | cons g gs ih =>
    intro n refs a ha
    cases hp : simplify refs g with
    | reuse w =>
      apply ih n (refs ++ [cap n w]) a
      simpa only [scan, hp] using ha
    | emit k =>
      have hm : a ∈ k :: (scan gs (n+1) (refs ++ [.port n])).gates := by
        simpa only [scan, hp] using ha
      rcases List.mem_cons.mp hm with hk | ht
      · subst a
        have hs := simplify_legal refs g
        rw [hp] at hs
        exact hs
      · exact ih _ _ _ ht

open PEqualNP.MetaComplexity

/-- Concrete old input list, obtained by constants, aliases and repeated reads of new inputs. -/
def substituted {n : ℕ} (refs : List Wire) (x : Fin n → Bool) : List Bool :=
  refs.map (Wire.val (read (List.ofFn x)))

private theorem start_ok {n : ℕ} (refs : List Wire) (x : Fin n → Bool)
    (hb : ∀ p ∈ refs, p.Bounded n) :
    Represents refs (substituted refs x) (List.ofFn x) := by
  constructor
  · simpa only [List.length_ofFn] using hb
  · rfl

/-- A nonconstant restriction always has a genuine output port. Packaging the circuit therefore
costs exactly its emitted gates. No extra constant-output gate is charged. -/
theorem specialize {n : ℕ} (C : Circuit) (hf : FanInTwo C) (refs : List Wire)
    (hb : ∀ p ∈ refs, p.Bounded n)
    (hn : ∃ x y : Fin n → Bool, C.eval (substituted refs x) ≠ C.eval (substituted refs y)) :
    ∃ D : Circuit, FanInTwo D ∧
      D.size + saved (scan C.gates n refs).trace = C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (substituted refs x) := by
  let code := scan C.gates n refs
  have run_eq (x : Fin n → Bool) :
      (resolve code.refs C.output).val (read (run code.gates (List.ofFn x))) =
        C.eval (substituted refs x) := by
    have hs := (scan_sound C.gates hf refs _ _ (start_ok refs x hb)).lookup C.output
    change (resolve code.refs C.output).val (read (run code.gates (List.ofFn x))) =
      read (run C.gates (substituted refs x)) C.output
    simpa only [code, List.length_ofFn] using hs
  cases hout : resolve code.refs C.output with
  | fixed b =>
    obtain ⟨x, y, hne⟩ := hn
    have hx := run_eq x
    have hy := run_eq y
    rw [hout] at hx hy
    exact False.elim (hne (hx.symm.trans hy))
  | port j =>
    let D : Circuit := ⟨code.gates, j⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · exact scan_legal C.gates n refs
    · exact scan_price C.gates n refs
    · intro x
      have hx := run_eq x
      rw [hout] at hx
      exact hx

/-- Numeric form for applying a previously proved lower bound to the restricted function. -/
theorem charge {n : ℕ} (C : Circuit) (hf : FanInTwo C) (refs : List Wire)
    (hb : ∀ p ∈ refs, p.Bounded n)
    (hn : ∃ x y : Fin n → Bool, C.eval (substituted refs x) ≠ C.eval (substituted refs y))
    (k : ℕ) (lower : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (substituted refs x)) → k ≤ D.size) :
    k + saved (scan C.gates n refs).trace ≤ C.size := by
  obtain ⟨D, hD, hp, he⟩ := specialize C hf refs hb hn
  have hk := lower D hD he
  omega

end PEqualNP.Research.PetersenRestrict
