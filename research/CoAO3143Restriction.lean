import Mathlib
import PEqualNP.Defs

namespace CoAO3143Restriction

abbrev Wire (α : Type) := α → Bool
def con {α : Type} (b : Bool) : Wire α := fun _ => b
def op {α : Type} (d : Bool) (a b : Wire α) : Wire α :=
  fun r => if d then a r || b r else a r && b r

noncomputable section
local instance {α : Type} : DecidableEq (Wire α) := Classical.decEq _

/-- A DAG read in reverse chronological order, keeping all signals used in its
    remaining part. Inputs of a step can be retained in U for fanout. -/
inductive Cone {α : Type} (out : Wire α) : Nat → Finset (Wire α) → Prop
  | stop : Cone out 0 {out}
  | gate {k : Nat} {U : Finset (Wire α)} (d : Bool) (a b : Wire α)
      (fresh : op d a b ∉ U) (tail : Cone out k (insert (op d a b) U)) :
      Cone out (k+1) (insert a (insert b U))

/-- Ordinary AND/OR computation with a reusable pool and optional constants in
    its initial bank. Each genuine binary step adds one signal at unit cost. -/
inductive Build {β : Type} (raw : List (Wire β)) : Nat → List (Wire β) → Prop
  | start : Build raw 0 raw
  | gate {j : Nat} {xs : List (Wire β)} (pre : Build raw j xs)
      (d : Bool) (a b : Wire β) (ha : a∈xs) (hb : b∈xs) :
      Build raw (j+1) (op d a b::xs)

def cut {α β} (f : β → α) (a : Wire α) : Wire β := fun p => a (f p)
def Constant {β} (a : Wire β) : Prop := ∃ b, a=con b
local instance {β : Type} (a : Wire β) : Decidable (Constant a) := Classical.propDecidable _

def losses {α β} (f : β → α) (s : Finset (Wire α)) : Nat :=
  (@Finset.filter _ (fun a => Constant (cut f a)) (fun _ => Classical.propDecidable _) s).card

private theorem losses_step {α β} (f : β→α) {U : Finset (Wire α)}
    (d : Bool) (a b : Wire α) (fresh : op d a b ∉ U) :
    (if Constant (cut f a) ∨ Constant (cut f b) then 0 else 1) + losses f (insert a (insert b U))
      ≤ 1 + losses f (insert (op d a b) U) := by
  classical
  let P := fun w : Wire α => Constant (cut f w)
  have left (w : Wire α) (s : Finset (Wire α)) :
      losses f (insert w s) ≤ losses f s + (if P w then 1 else 0) := by
    unfold losses
    by_cases h : P w
    · rw [Finset.filter_insert]
      simp only [show Constant (cut f w) from h, if_true, h]
      exact Finset.card_insert_le _ _
    · rw [Finset.filter_insert]
      simp [show ¬ Constant (cut f w) from h,h]
  have right : losses f (insert (op d a b) U) =
      losses f U + (if P (op d a b) then 1 else 0) := by
    unfold losses
    rw [Finset.filter_insert]
    by_cases h : P (op d a b)
    · have nn : op d a b ∉ U.filter P := fun m => fresh (Finset.mem_filter.mp m).1
      simp only [show Constant (cut f (op d a b)) from h,h,if_true]
      exact Finset.card_insert_of_notMem nn
    · simp [show ¬ Constant (cut f (op d a b)) from h,h]
  have ainc := left a (insert b U)
  have binc := left b U
  rw [right]
  change (if P a ∨ P b then 0 else 1) + losses f (insert a (insert b U))
    ≤ 1 + (losses f U + (if P (op d a b) then 1 else 0))
  by_cases ha : P a <;> by_cases hb : P b
  · have hz : P (op d a b) := by
      obtain ⟨i,hi⟩ := ha
      obtain ⟨j,hj⟩ := hb
      refine ⟨if d then i || j else i && j,?_⟩
      funext r
      change (if d then (cut f a r || cut f b r) else (cut f a r && cut f b r)) = _
      rw [hi,hj]
      rfl
    simp [ha,hb,hz] at ainc binc ⊢
    omega
  all_goals by_cases hz : P (op d a b) <;> simp [ha,hb,hz] at ainc binc ⊢ <;> omega

private lemma constant_gate {β : Type} (a b : Wire β) (d : Bool)
    (h : Constant a ∨ Constant b) :
      (∃ v, op d a b = con v) ∨ op d a b=a ∨ op d a b=b := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases d <;> cases v
    · exact Or.inl ⟨false, by funext i; simp [op,con]⟩
    · exact Or.inr (Or.inr (by funext i; simp [op,con]))
    · exact Or.inr (Or.inr (by funext i; simp [op,con]))
    · exact Or.inl ⟨true, by funext i; simp [op,con]⟩
  · cases d <;> cases v
    · exact Or.inl ⟨false, by funext i; simp [op,con]⟩
    · exact Or.inr (Or.inl (by funext i; simp [op,con]))
    · exact Or.inr (Or.inl (by funext i; simp [op,con]))
    · exact Or.inl ⟨true, by funext i; simp [op,con]⟩

/-- If c distinct current live labels turn constant on a restriction, at least
    c of the remaining gates are saved whenever the final value is nonconstant. -/
theorem projected {α β : Type} {out : Wire α} {k S} (h : Cone out k S) (f : β → α)
    (nout : ¬ Constant (cut f out)) {raw pool : List (Wire β)} {n}
    (before : Build raw n pool) (cs : ∀ b : Bool, con b ∈ pool)
    (initial : ∀ a∈S, cut f a ∈ pool) :
    ∃ m ys, Build raw (n+m) ys ∧ cut f out ∈ ys ∧ m + losses f S ≤ k := by
  classical
  induction h generalizing pool n with
  | stop =>
    refine ⟨0,pool,by simpa using before,initial _ (by simp),?_⟩
    simp [losses,nout]
  | @gate k U d a b fresh tail ih =>
    have ha := initial a (Finset.mem_insert_self _ _)
    have hb := initial b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hu (x) (hx : x∈U) : cut f x∈pool :=
      initial x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have step := losses_step f d a b fresh
    have zz : cut f (op d a b) = op d (cut f a) (cut f b) := rfl
    by_cases skip : Constant (cut f a) ∨ Constant (cut f b)
    · have z : cut f (op d a b) ∈ pool := by
        rw [zz]
        rcases constant_gate _ _ d skip with ⟨v,hv⟩ | eq | eq
        · rw [hv]; exact cs v
        · rw [eq]; exact ha
        · rw [eq]; exact hb
      have keep (w) (hw : w∈insert (op d a b) U) : cut f w ∈ pool := by
        rcases Finset.mem_insert.mp hw with rfl | mem
        · exact z
        · exact hu _ mem
      obtain ⟨m,ys,prog,sol,paid⟩ := ih before cs keep
      simp only [skip,if_true,zero_add] at step
      exact ⟨m,ys,prog,sol,by omega⟩
    · let ys := cut f (op d a b)::pool
      have build : Build raw (n+1) ys := Build.gate before d _ _ ha hb
      have keep (w) (hw : w∈insert (op d a b) U) : cut f w ∈ ys := by
        rcases Finset.mem_insert.mp hw with rfl | mem
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hu w mem)
      obtain ⟨m,ws,prog,sol,paid⟩ := ih build (fun b => List.mem_cons_of_mem _ (cs b)) keep
      simp only [skip,if_false] at step
      refine ⟨m+1,ws,?_,sol,by omega⟩
      exact (show n+1+m=n+(m+1) by omega) ▸ prog

theorem same_rows {α} {out : Wire α} {k S} (h : Cone out k S) (r s : α)
    (same : ∀ a∈S, a r=a s) : out r=out s := by
  induction h with
  | stop => exact same _ (by simp)
  | @gate k U d a b fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hm
    · have ha := same _ (Finset.mem_insert_self _ _)
      have hb := same _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      simp only [op,ha,hb]
    · exact same _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))


theorem projected_two {α β : Type} {out : Wire α} {k S} (h : Cone out k S) (f : β → α)
    (nout : ¬ Constant (cut f out)) {raw : List (Wire β)} (cs : ∀ b : Bool, con b ∈ raw)
    (initial : ∀ a∈S, cut f a ∈ raw) {a b : Wire α} (hne : a≠b)
    (ha : a∈S) (hb : b∈S) (ca : Constant (cut f a)) (cb : Constant (cut f b)) :
    ∃ m ys, Build raw m ys ∧ cut f out ∈ ys ∧ m + 2 ≤ k := by
  classical
  obtain ⟨m,ys,prog,sol,budget⟩ := projected h f nout (Build.start (raw:=raw)) cs initial
  let U := S.filter (fun w => Constant (cut f w))
  have sub : ({a,b} : Finset (Wire α)) ⊆ U := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hh
    · exact Finset.mem_filter.mpr ⟨ha,ca⟩
    · have e := Finset.mem_singleton.mp hh
      subst x
      exact Finset.mem_filter.mpr ⟨hb,cb⟩
  have size := Finset.card_le_card sub
  have pair : ({a,b} : Finset (Wire α)).card=2 := by simp [hne]
  rw [pair] at size
  change 2 ≤ losses f S at size
  exact ⟨m,ys,by simpa using prog,sol,by omega⟩

open PEqualNP.CircuitLowerBounds

theorem scalar_comm {α : Type} (d : Bool) (a b : Wire α) : op d a b = op d b a := by
  funext r
  cases d <;> simp [op,Bool.and_comm,Bool.or_comm]

def readGate {α : Type} (ws : List (Wire α)) (g : Gate) : Wire α :=
  fun r => g.op.eval (g.inputs.map (fun i => ws.getD i (con false) r))

def circuitWires {α : Type} (gs : List Gate) (ws : List (Wire α)) : List (Wire α) :=
  gs.foldl (fun old g => old++[readGate old g]) ws

private theorem read_scalar {α : Type} (ws : List (Wire α)) (r : α) (i : Nat) :
    (ws.map (fun w => w r)).getD i false = ws.getD i (con false) r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? <;> rfl

theorem circuit_rows {α : Type} (gs : List Gate) (ws : List (Wire α)) (r : α) :
    (circuitWires gs ws).map (fun w => w r) =
    gs.foldl (fun (old : List Bool) (g : Gate) => old++[g.op.eval (g.inputs.map (fun i => old.getD i false))])
      (ws.map fun w => w r) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change (circuitWires gs (ws++[readGate ws g])).map _ = _
    rw [ih]
    simp only [List.foldl_cons,List.map_append,List.map_cons,List.map_nil,readGate,read_scalar]

private theorem read_available {α : Type} (ws : List (Wire α)) (i : Nat)
    (kb : con false ∈ ws) : ws.getD i (con false) ∈ ws := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact kb
  | some a => exact List.mem_of_getElem? e

private theorem classified {α : Type} (ws : List (Wire α)) (g : Gate)
    (cs : ∀ b, con b∈ws)
    (legal : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    readGate ws g ∈ ws ∨ ∃ d a b, a∈ws ∧ b∈ws ∧ readGate ws g=op d a b := by
  obtain ⟨t,is⟩ := g
  obtain ⟨ts,hl⟩ := legal
  change is.length≤2 at hl
  change t = _ ∨ t = _ at ts
  cases is with
  | nil => rcases ts with rfl | rfl; exact Or.inl (cs true); exact Or.inl (cs false)
  | cons i is =>
    cases is with
    | nil =>
      left
      convert read_available ws i (cs false) using 1
      rcases ts with rfl | rfl <;> funext r <;> simp [readGate,GateOp.eval]
    | cons j is =>
      cases is with
      | cons k rest => simp at hl
      | nil =>
        right
        refine ⟨decide (t=.or),_,_,read_available ws i (cs false),read_available ws j (cs false),?_⟩
        rcases ts with rfl | rfl <;> funext r <;> simp [readGate,GateOp.eval,op]

/-- Extract the truly used cone, including arbitrary raw out-of-range pins. -/
theorem physical_cone {α : Type} (out : Wire α) (gs : List Gate) (ws : List (Wire α))
    (cs : ∀ b, con b∈ws) (legal : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (solves : out∈circuitWires gs ws) :
    ∃ k S, k≤gs.length ∧ Cone out k S ∧ ∀ a∈S, a∈ws := by
  classical
  induction gs generalizing ws with
  | nil => exact ⟨0,{out},by simp,Cone.stop,by simpa [circuitWires] using solves⟩
  | cons g gs ih =>
    let z := readGate ws g
    obtain ⟨k,S,budget,t,held⟩ := ih (ws++[z]) (fun b => List.mem_append_left _ (cs b))
      (fun a ha => legal a (List.mem_cons_of_mem _ ha)) solves
    by_cases used : z∈S
    · by_cases old : z∈ws
      · refine ⟨k,S,by simp; omega,t,?_⟩
        intro w hw
        rcases List.mem_append.mp (held w hw) with known | h
        · exact known
        · rw [List.mem_singleton.mp h]
          exact old
      · have classed := classified ws g cs (legal g List.mem_cons_self)
        rcases classed with known | ⟨d,a,b,ha,hb,eq⟩
        · exact (old known).elim
        · let U := S.erase z
          have sub (w) (hw : w∈U) : w∈ws := by
            obtain ⟨diff,member⟩ := Finset.mem_erase.mp hw
            simpa [diff] using held w member
          have ident : z=op d a b := eq
          have clean : op d a b ∉ U := by simp [U,←ident]
          have next : Cone out k (insert (op d a b) U) := by
            simpa [U,←ident,Finset.insert_erase used] using t
          refine ⟨k+1,_,by simp; omega,Cone.gate d a b clean next,?_⟩
          simpa using And.intro ha (And.intro hb sub)
    · refine ⟨k,S,by simp; omega,t,?_⟩
      intro a ha
      have other : a≠z := fun eq => used (eq ▸ ha)
      simpa [other] using held a ha

end
end CoAO3143Restriction
