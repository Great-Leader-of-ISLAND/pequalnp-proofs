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

theorem cost_le_one (p : Plan) : p.cost ≤ 1 := by cases p <;> decide

theorem resolve_outside (refs : List Wire) (i : ℕ) (hi : refs.length ≤ i) :
    resolve refs i = .fixed false := by
  simp only [resolve, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi] <;> rfl

end PEqualNP.Research.PetersenRestrict
