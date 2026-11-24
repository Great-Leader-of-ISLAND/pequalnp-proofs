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
  simp [smallPorts,substituted,Wire.val,read,List.getD_eq_getElem?_getD,
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
  deriving Fintype, DecidableEq

def SignedForm.eval : SignedForm → Bool → Bool → Bool
  | .off,_,_ => false | .on,_,_ => true
  | .positive,p,_ => p | .negative,p,_ => !p | .value,_,w => w
  | .andPos,p,w => p&&w | .andNeg,p,w => !p&&w | .orPos,p,w => p||w | .orNeg,p,w => !p||w

/-- Two operations in succession which each use the signed input simplify to at most one. -/
theorem flatten_signed_readers : ∀ (innerOr outerOr innerNeg outerNeg : Bool), ∃ f : SignedForm,
    ∀ p w : Bool, f.eval p w =
      (let a := if innerNeg then !p else p; let b := if outerNeg then !p else p
       let v := if innerOr then a||w else a&&w; if outerOr then b||v else b&&v) := by decide +kernel

end CoPetersen2598
