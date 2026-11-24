import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Research.PetersenRestrict

open PEqualNP.CircuitLowerBounds

/-- A former wire is now either a known value or a wire of the restricted circuit. -/
inductive Wire where
  | fixed (b : Bool)
  | port (index : ℕ)
  deriving DecidableEq, Repr

def Wire.val (read : ℕ → Bool) : Wire → Bool
  | .fixed b => b
  | .port i => read i

/-- An alias contributes zero gates. An emitted gate has already had its pins renamed. -/
inductive Plan where
  | reuse (w : Wire)
  | emit (g : Gate)

def Plan.val (read : ℕ → Bool) : Plan → Bool
  | .reuse w => w.val read
  | .emit g => g.op.eval (g.inputs.map read)

def Plan.cost : Plan → ℕ
  | .reuse _ => 0
  | .emit _ => 1

def Allowed (op : GateOp) : Prop :=
  op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)

def Legal (g : Gate) : Prop := Allowed g.op ∧ g.inputs.length ≤ 2

def Plan.Legal : Plan → Prop
  | .reuse _ => True
  | .emit g => PetersenRestrict.Legal g

private def binOp (a : Bool) : GateOp := if a then .and else .or

private def pair (a : Bool) (p q : Wire) : Plan :=
  match p, q with
  | .fixed b, v => .reuse (if b == a then v else .fixed b)
  | .port i, .fixed b => .reuse (if b == a then .port i else .fixed b)
  | .port i, .port j =>
      if i = j then .reuse (.port i) else .emit ⟨binOp a, [i,j]⟩

private def two (a : Bool) : List Wire → Plan
  | [] => .reuse (.fixed a)
  | [p] => .reuse p
  | [p,q] => pair a p q
  | _ => .reuse (.fixed false)

private def inv : List Wire → Plan
  | [] => .reuse (.fixed true)
  | .fixed b :: _ => .reuse (.fixed (!b))
  | .port i :: _ => .emit ⟨.not, [i]⟩

def lower (op : GateOp) (ws : List Wire) : Plan :=
  match op with
  | .and => two true ws
  | .or => two false ws
  | .not => inv ws
  | _ => .reuse (.fixed false)

private theorem pair_val (a : Bool) (p q : Wire) (read : ℕ → Bool) :
    (pair a p q).val read = (binOp a).eval [p.val read, q.val read] := by
  cases p with
  | fixed b =>
    cases a <;> cases b <;> simp [pair, binOp, Plan.val, GateOp.eval, Wire.val]
  | port i =>
    cases q with
    | fixed b =>
      cases a <;> cases b <;> simp [pair, binOp, Plan.val, GateOp.eval, Wire.val]
    | port j =>
      by_cases h : i = j
      · subst j
        cases a <;> simp [pair, binOp, Plan.val, GateOp.eval, Wire.val]
      · cases a <;> simp [pair, binOp, Plan.val, GateOp.eval, Wire.val, h]

private theorem two_val (a : Bool) (ws : List Wire) (h : ws.length ≤ 2) (read : ℕ → Bool) :
    (two a ws).val read = (binOp a).eval (ws.map (Wire.val read)) := by
  cases ws with
  | nil => cases a <;> rfl
  | cons p ps =>
    cases ps with
    | nil => cases a <;> simp [two, binOp, Plan.val, GateOp.eval]
    | cons q qs =>
      cases qs with
      | nil => exact pair_val a p q read
      | cons r rs => simp only [List.length_cons] at h; omega

private theorem inv_val (ws : List Wire) (read : ℕ → Bool) :
    (inv ws).val read = GateOp.not.eval (ws.map (Wire.val read)) := by
  cases ws with
  | nil => rfl
  | cons p ps => cases p <;> rfl

theorem lower_val (op : GateOp) (ws : List Wire) (ha : Allowed op)
    (hl : ws.length ≤ 2) (read : ℕ → Bool) :
    (lower op ws).val read = op.eval (ws.map (Wire.val read)) := by
  simp only [Allowed, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact two_val true ws hl read
  · exact two_val false ws hl read
  · exact inv_val ws read

private theorem pair_legal (a : Bool) (p q : Wire) : (pair a p q).Legal := by
  cases p with
  | fixed b => trivial
  | port i =>
    cases q with
    | fixed b => trivial
    | port j =>
      by_cases h : i = j
      · simp [pair, h, Plan.Legal]
      · cases a <;> simp [pair, h, binOp, Plan.Legal, Legal, Allowed]

private theorem two_legal (a : Bool) (ws : List Wire) : (two a ws).Legal := by
  cases ws with
  | nil => trivial
  | cons p ps =>
    cases ps with
    | nil => trivial
    | cons q qs =>
      cases qs with
      | nil => exact pair_legal a p q
      | cons r rs => trivial

theorem lower_legal (op : GateOp) (ws : List Wire) : (lower op ws).Legal := by
  cases op with
  | and => exact two_legal true ws
  | or => exact two_legal false ws
  | not =>
    cases ws with
    | nil => trivial
    | cons p ps =>
      cases p with
      | fixed b => trivial
      | port i => simp [lower, inv, Plan.Legal, Legal, Allowed]
  | mod m => trivial
  | maj => trivial

/-- NOT reads only the head of its pin list. A constant on its ignored second pin
does not by itself eliminate the gate. -/
def effective (op : GateOp) (ws : List Wire) : List Wire :=
  match op with
  | .not => ws.take 1
  | _ => ws

private theorem two_fixed (a : Bool) (ws : List Wire) (b : Bool) (hm : Wire.fixed b ∈ ws) :
    (two a ws).cost = 0 := by
  cases ws with
  | nil => cases hm
  | cons p ps =>
    cases ps with
    | nil => rfl
    | cons q qs =>
      cases qs with
      | nil =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with h | h
        · subst p; rfl
        · subst q; cases p <;> rfl
      | cons r rs => rfl

theorem lower_fixed (op : GateOp) (ws : List Wire) (b : Bool)
    (hm : Wire.fixed b ∈ effective op ws) : (lower op ws).cost = 0 := by
  cases op with
  | and => exact two_fixed true ws b hm
  | or => exact two_fixed false ws b hm
  | not =>
    cases ws with
    | nil => cases hm
    | cons p ps =>
      have h : Wire.fixed b = p := by simpa [effective] using hm
      subst p
      rfl
  | mod m => rfl
  | maj => rfl

def resolve (refs : List Wire) (i : ℕ) : Wire := refs.getD i (.fixed false)

/-- Lookup is bounded by the old wire table, so an original forward/bad read remains false. -/
def simplify (refs : List Wire) (g : Gate) : Plan :=
  lower g.op (g.inputs.map (resolve refs))

theorem simplify_val (refs : List Wire) (g : Gate) (hg : Legal g)
    (old read : ℕ → Bool) (h : ∀ i, (resolve refs i).val read = old i) :
    (simplify refs g).val read = g.op.eval (g.inputs.map old) := by
  rw [simplify, lower_val _ _ hg.1 (by simpa using hg.2)]
  simp only [List.map_map, Function.comp_def, h]

theorem simplify_legal (refs : List Wire) (g : Gate) : (simplify refs g).Legal :=
  lower_legal _ _

theorem simplify_fixed (refs : List Wire) (g : Gate) (b : Bool)
    (hm : Wire.fixed b ∈ effective g.op (g.inputs.map (resolve refs))) :
    (simplify refs g).cost = 0 := lower_fixed _ _ b hm

theorem cost_le_one (p : Plan) : p.cost ≤ 1 := by cases p <;> simp [Plan.cost]

theorem resolve_outside (refs : List Wire) (i : ℕ) (hi : refs.length ≤ i) :
    resolve refs i = .fixed false := by
  simp only [resolve, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi] <;> rfl

end PEqualNP.Research.PetersenRestrict

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

namespace PEqualNP.Research.PetersenRestrict

open PEqualNP.CircuitLowerBounds

/-- Original, effective pin indices. In particular NOT's optional second pin is excluded. -/
def pins (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

private theorem map_pins (g : Gate) (refs : List Wire) :
    (pins g).map (resolve refs) = effective g.op (g.inputs.map (resolve refs)) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> cases ins <;> rfl

theorem simplify_fixed_port (g : Gate) (refs : List Wire) (i : ℕ) (b : Bool)
    (hr : resolve refs i = .fixed b) (hi : i ∈ pins g) :
    (simplify refs g).cost = 0 := by
  apply simplify_fixed refs g b
  rw [← map_pins]
  exact List.mem_map.mpr ⟨i, hi, hr⟩

/-- All named indices already exist at this prefix and are represented by constants.
Existence at the prefix prevents mistaking a future wire for a permanently fixed false pin. -/
def Ready (s : Finset ℕ) (refs : List Wire) : Prop :=
  ∀ i ∈ s, i < refs.length ∧ ∃ b, resolve refs i = .fixed b

private theorem ready_append {s : Finset ℕ} {refs : List Wire} (hr : Ready s refs) (w : Wire) :
    Ready s (refs ++ [w]) := by
  intro i hi
  obtain ⟨hlt, b, hb⟩ := hr i hi
  refine ⟨?_, b, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · simpa only [resolve, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] using hb

/-- Count each subsequent gate once, even when both of its input pins are already fixed. -/
def directSavings (s : Finset ℕ) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
    if (pins g).toFinset ∩ s = ∅ then directSavings s gs else directSavings s gs + 1

theorem scan_direct (s : Finset ℕ) : ∀ (gs : List Gate) (n : ℕ) (refs : List Wire),
    Ready s refs → directSavings s gs ≤ saved (scan gs n refs).trace := by
  intro gs
  induction gs with
  | nil => intros; exact Nat.le_refl 0
  | cons g gs ih =>
    intro n refs hr
    cases hp : simplify refs g with
    | reuse w =>
      have hh := ih n (refs ++ [cap n w]) (ready_append hr _)
      by_cases he : (pins g).toFinset ∩ s = ∅
      · simp only [scan, hp, directSavings, he, ite_true, saved]
        omega
      · simpa only [scan, hp, directSavings, he, if_false, saved] using Nat.add_le_add_right hh 1
    | emit a =>
      have he : (pins g).toFinset ∩ s = ∅ := by
        by_contra hn
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hn
        obtain ⟨hpin, hfixed⟩ := Finset.mem_inter.mp hi
        obtain ⟨_, b, hb⟩ := hr i hfixed
        have hc := simplify_fixed_port g refs i b hb (List.mem_toFinset.mp hpin)
        rw [hp] at hc
        cases hc
      have hh := ih (n+1) (refs ++ [.port n]) (ready_append hr _)
      simpa only [scan, hp, directSavings, he, if_true, saved] using hh

/-- A prescribed, ordered list of zero-gate actions in the trace gives a lower bound
regardless of arbitrary intervening uses or additional eliminations. -/
theorem saved_sublist {as bs : List Plan} (h : as.Sublist bs) : saved as ≤ saved bs := by
  induction h with
  | slnil => exact Nat.le_refl 0
  | cons x h ih =>
    cases x with
    | reuse w => exact Nat.le.step ih
    | emit g => exact ih
  | cons_cons x h ih =>
    cases x with
    | reuse w => exact Nat.add_le_add_right ih 1
    | emit g => exact ih

theorem charge_reuses {ps : List Plan} (ws : List Wire) (hs : (ws.map Plan.reuse).Sublist ps) :
    ws.length ≤ saved ps := by
  have hn : saved (ws.map Plan.reuse) = ws.length := by
    clear hs
    induction ws with
    | nil => rfl
    | cons w ws ih => simp only [List.map_cons, saved, List.length_cons, ih]
  rw [← hn]
  exact saved_sublist hs

end PEqualNP.Research.PetersenRestrict
namespace CoPetersen2598
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.PetersenRestrict

def ten (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def nine (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def smallPorts : List Wire := [.fixed false,.port 6,.port 8,.port 5,.port 7,.port 4,
  .port 1,.port 3,.port 0,.port 2,.fixed true]

def embed (x : Fin 9 → Bool) : Fin 10 → Bool :=
  ![false,x 6,x 8,x 5,x 7,x 4,x 1,x 3,x 0,x 2]

private theorem ports_ready : Ready {0,10} smallPorts := by
  intro i hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl
  · exact ⟨by decide,false,rfl⟩
  · exact ⟨by decide,true,rfl⟩

private theorem ports_bounded (w) (hw : w∈smallPorts) : w.Bounded 9 := by
  cases w with
  | fixed b => trivial
  | port i =>
    simp [smallPorts] at hw
    change i<9
    omega

private theorem wiring (x : Fin 9 → Bool) : substituted smallPorts x =
    List.ofFn (embed x) ++ [!(embed x 0)] := by
  simp [smallPorts,substituted,Wire.val,PEqualNP.Research.PetersenRestrict.read,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn,embed,List.ofFn_succ]

private theorem graph_slice (x : Fin 9 → Bool) : ten (embed x)=nine x := by
  simp [ten,nine,embed,Bool.and_comm,Bool.or_assoc,Bool.or_comm,Bool.or_left_comm]

def readsSigned (g : Gate) : Bool := decide (0∈pins g ∨ 10∈pins g)

private theorem meet_pins (g : Gate) : (pins g).toFinset ∩ ({0,10} : Finset Nat) ≠ ∅ ↔
    0∈pins g ∨ 10∈pins g := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr h
    obtain ⟨hm,hs⟩ := Finset.mem_inter.mp hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl|rfl
    · exact Or.inl (List.mem_toFinset.mp hm)
    · exact Or.inr (List.mem_toFinset.mp hm)
  · rintro (h|h)
    · exact Finset.nonempty_iff_ne_empty.mp ⟨0,Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr h,by decide⟩⟩
    · exact Finset.nonempty_iff_ne_empty.mp ⟨10,Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr h,by decide⟩⟩

private theorem count_reads (gs : List Gate) :
    directSavings {0,10} gs = (gs.filter readsSigned).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : 0∈pins g ∨ 10∈pins g
    · have hn := (meet_pins g).2 h
      simp [directSavings,hn,readsSigned,h,ih]
    · have he : (pins g).toFinset ∩ ({0,10} : Finset Nat) = ∅ := by
        by_contra hn
        exact h ((meet_pins g).1 hn)
      simp [directSavings,he,readsSigned,h,ih]

def NineLower := ∀ D : Circuit, FanInTwo D →
  (∀ x : Fin 9 → Bool, D.eval (List.ofFn x)=nine x) → 15≤D.size

theorem restriction_price (lower : NineLower) (C : Circuit) (hf : FanInTwo C)
    (agree : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!(x 0)])=ten x) :
    15 + saved (scan C.gates 9 smallPorts).trace ≤ C.size := by
  have sliced (x : Fin 9 → Bool) : C.eval (substituted smallPorts x)=nine x := by
    rw [wiring,agree,graph_slice]
  have hn : ∃ x y : Fin 9 → Bool, C.eval (substituted smallPorts x) ≠
      C.eval (substituted smallPorts y) := by
    refine ⟨fun _ => false,fun i => decide (i=0 ∨ i=1),?_⟩
    rw [sliced,sliced]
    decide
  apply charge C hf smallPorts ports_bounded hn 15
  intro D hd same
  exact lower D hd (fun x => (same x).trans (sliced x))

theorem necessary_reader_budget (lower : NineLower) (C : Circuit) (hf : FanInTwo C)
    (small : C.size≤18)
    (agree : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!(x 0)])=ten x) :
    (C.gates.filter readsSigned).length≤3 := by
  have price := restriction_price lower C hf agree
  have d := scan_direct {0,10} C.gates 9 smallPorts ports_ready
  rw [count_reads] at d
  omega

inductive SignedForm where
  | off | on | positive | negative | value | andPos | andNeg | orPos | orNeg
  deriving DecidableEq

def SignedForm.eval : SignedForm → Bool → Bool → Bool
  | .off,_,_ => false | .on,_,_ => true
  | .positive,p,_ => p | .negative,p,_ => !p | .value,_,w => w
  | .andPos,p,w => p&&w | .andNeg,p,w => !p&&w | .orPos,p,w => p||w | .orNeg,p,w => !p||w

private def composed : Bool → Bool → Bool → Bool → SignedForm
  | false,false,false,false => .andPos
  | false,false,false,true => .off
  | false,false,true,false => .off
  | false,false,true,true => .andNeg
  | false,true,false,false => .positive
  | false,true,false,true => .orNeg
  | false,true,true,false => .orPos
  | false,true,true,true => .negative
  | true,false,false,false => .positive
  | true,false,false,true => .andNeg
  | true,false,true,false => .andPos
  | true,false,true,true => .negative
  | true,true,false,false => .orPos
  | true,true,false,true => .on
  | true,true,true,false => .on
  | true,true,true,true => .orNeg

/-- Two operations in succession which each use the signed input simplify to at most one. -/
theorem flatten_signed_readers : ∀ (innerOr outerOr innerNeg outerNeg : Bool), ∃ f : SignedForm,
    ∀ p w : Bool, f.eval p w =
      (let a := if innerNeg then !p else p; let b := if outerNeg then !p else p
       let v := if innerOr then a||w else a&&w; if outerOr then b||v else b&&v) := by
  intro a b i j
  refine ⟨composed a b i j,?_⟩
  decide +revert +kernel

end CoPetersen2598
-- Ordinary edge-head theorem reproduced from the checked proof by loris-olsem.
namespace Prior1667
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one

end Prior1667
namespace Prior1667
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def whenOn (x : Fin 9 → Bool) : Bool := edge x || x 4 || x 6 || x 7

def onTable : Sig := graph ||| inputs.getD 4 zero ||| inputs.getD 6 zero ||| inputs.getD 7 zero
private def onMoves := ([65,50,135] : List Nat).map swapRows ++ fixRows 208 0

private theorem on_lift : checkLift onMoves onTable inputs (vars 189) (graphGoal 189)
    (supportPairs 208)=true := by decide +kernel

private theorem on_lower (cycle : Lower (vars 189) (graphGoal 189) 8) : Lower inputs onTable 11 := by
  have h := lift_ok on_lift (show proper onTable by unfold proper; decide +kernel)
    (show proper (graphGoal 189) by unfold proper; decide +kernel) cycle
  have card : ((supportPairs 208).map Prod.fst).toFinset.card = 3 := by decide +kernel
  rw [card] at h
  exact h

private theorem price_of_table (T : Sig) (pT : proper T) (k : Nat) (low : Lower inputs T k)
    (D : Circuit) (legal : FanInTwo D)
    (computes : ∀ r : Row, D.eval (List.ofFn (sample r)) = bit r T) : k ≤ D.size := by
  classical
  have goalEq : (execute D.gates inputs).getD D.output zero = T := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute D.gates inputs).getD D.output zero) = bit r T
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1),←sampled]
    exact computes r
  have out := get_rep (execute D.gates inputs) D.output
  rw [goalEq] at out
  have mem := out.resolve_right (fun hn => hn pT)
  obtain ⟨a,t,S,ha,run,raw⟩ := extract D.gates _ legal pT mem
  have r := list_run run S.toList (Finset.nodup_toList _) (by simp)
  have hs : supply (inputs.map observe) (S.toList.map observe) := by
    intro f hf
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hf
    exact Or.inl (List.mem_map.mpr ⟨v,raw v (Finset.mem_toList.mp hv),rfl⟩)
  obtain ⟨q,next,reach,available,hq⟩ := contraction (observe_proper pT) r
    (inputs.map observe) Reach.start hs
  have hk := low q next reach available
  change k≤D.gates.length
  omega

theorem positive_nine (cycle : Lower (vars 189) (graphGoal 189) 8) (D : Circuit)
    (legal : FanInTwo D) (computes : ∀ x, D.eval (List.ofFn x)=whenOn x) : 11≤D.size := by
  apply price_of_table onTable (by unfold proper; decide +kernel) 11 (on_lower cycle) D legal
  intro r
  rw [computes]
  have test : ∀ i : Row, whenOn (sample i)=bit i onTable := by decide +kernel
  exact test r
end Prior1667

namespace CoPetersen2598
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.PetersenRestrict

def onPorts : List Wire := [.fixed true,.port 6,.port 8,.port 5,.port 7,.port 4,
  .port 1,.port 3,.port 0,.port 2,.fixed false]

def onEmbed (x : Fin 9 → Bool) : Fin 10 → Bool :=
  ![true,x 6,x 8,x 5,x 7,x 4,x 1,x 3,x 0,x 2]

private theorem on_wiring (x : Fin 9 → Bool) : substituted onPorts x =
    List.ofFn (onEmbed x) ++ [!(onEmbed x 0)] := by
  simp [onPorts,substituted,Wire.val,PEqualNP.Research.PetersenRestrict.read,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn,onEmbed,List.ofFn_succ]

private theorem on_bounded (w) (hw : w∈onPorts) : w.Bounded 9 := by
  cases w with
  | fixed b => trivial
  | port i =>
    simp [onPorts] at hw
    change i<9
    omega

private theorem on_slice (x : Fin 9 → Bool) : ten (onEmbed x)=Prior1667.whenOn x := by
  simp [ten,Prior1667.whenOn,Prior1667.edge,onEmbed,Bool.and_comm,Bool.or_assoc,Bool.or_comm,Bool.or_left_comm]

theorem on_price (cycle : Prior1667.Lower (Prior1667.vars 189) (Prior1667.graphGoal 189) 8)
    (C : Circuit) (hf : FanInTwo C)
    (agree : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!(x 0)])=ten x) :
    11 + saved (scan C.gates 9 onPorts).trace ≤ C.size := by
  have sliced (x : Fin 9 → Bool) : C.eval (substituted onPorts x)=Prior1667.whenOn x := by
    rw [on_wiring,agree,on_slice]
  have hn : ∃ x y : Fin 9 → Bool, C.eval (substituted onPorts x) ≠
      C.eval (substituted onPorts y) := by
    refine ⟨fun _ => false,fun i => decide (i=4),?_⟩
    rw [sliced,sliced]
    decide
  apply charge C hf onPorts on_bounded hn 11
  intro D hd same
  exact Prior1667.positive_nine cycle D hd (fun x => (same x).trans (sliced x))
end CoPetersen2598
namespace CoPetersen2598
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.PetersenRestrict

def forcingFirst (g : Gate) : Prop := ∃ k : Nat,
  g=⟨.and,[0,k]⟩ ∨ g=⟨.and,[k,0]⟩ ∨ g=⟨.or,[10,k]⟩ ∨ g=⟨.or,[k,10]⟩

private theorem and_fixed_right (w : Wire) :
    PEqualNP.Research.PetersenRestrict.lower .and [w,.fixed false] = .reuse (.fixed false) := by
  cases w with
  | fixed b => cases b <;> rfl
  | port j => rfl

private theorem or_fixed_right (w : Wire) :
    PEqualNP.Research.PetersenRestrict.lower .or [w,.fixed true] = .reuse (.fixed true) := by
  cases w with
  | fixed b => cases b <;> rfl
  | port j => rfl

private theorem forced_value {g : Gate} (h : forcingFirst g) :
    ∃ b : Bool, simplify smallPorts g = .reuse (.fixed b) := by
  obtain ⟨k,rfl|rfl|rfl|rfl⟩ := h
  · exact ⟨false,rfl⟩
  · exact ⟨false,and_fixed_right (resolve smallPorts k)⟩
  · exact ⟨true,rfl⟩
  · exact ⟨true,or_fixed_right (resolve smallPorts k)⟩

private theorem first_ready (b : Bool) : Ready {0,10,11} (smallPorts++[cap 9 (.fixed b)]) := by
  intro i hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl
  · exact ⟨by change 0<12; decide,false,rfl⟩
  · exact ⟨by change 10<12; decide,true,rfl⟩
  · exact ⟨by change 11<12; decide,b,rfl⟩

def readsSet (s : Finset Nat) (g : Gate) : Bool := decide ((pins g).toFinset ∩ s ≠ ∅)

private theorem readsSet_count (s : Finset Nat) (gs : List Gate) :
    directSavings s gs = (gs.filter (readsSet s)).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : (pins g).toFinset ∩ s = ∅ <;> simp [directSavings,readsSet,h,ih]

theorem first_force_price (lower : NineLower) (g : Gate) (gs : List Gate) (o : Nat)
    (hf : FanInTwo ⟨g::gs,o⟩) (small : (Circuit.mk (g::gs) o).size≤18)
    (agree : ∀ x : Fin 10 → Bool, (Circuit.mk (g::gs) o).eval (List.ofFn x ++ [!(x 0)])=ten x)
    (force : forcingFirst g) : (gs.filter (readsSet {0,10,11})).length≤2 := by
  obtain ⟨b,hb⟩ := forced_value force
  have r := restriction_price lower ⟨g::gs,o⟩ hf agree
  change 15 + saved (scan (g::gs) 9 smallPorts).trace ≤ (Circuit.mk (g::gs) o).size at r
  simp only [scan,hb,saved] at r
  have d := scan_direct {0,10,11} gs 9 _ (first_ready b)
  rw [readsSet_count] at d
  omega
end CoPetersen2598
