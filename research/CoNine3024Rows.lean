import PEqualNP.CoNine3024Data
import PEqualNP.CoMask3024

namespace CoNine3024Rows
open CoThetaNine CoAO3143Restriction CoNine3024

def value (a : Atom) (r : Input) : Bool := a.full.getLsbD r.val

def prow (p : Fin 11) (c : Fin 320) := row ((yes p).getD (c.val / (no p).length) 0)
def nrow (p : Fin 11) (c : Fin 320) := row ((no p).getD (c.val % (no p).length) 0)
def used (p : Fin 11) (c : Fin 320) : Prop := (cellMasks p).getLsbD c.val=true

structure Good (p : Fin 11) (a : Atom) : Prop where
  fixed : a.fixed=fixedMask a.full sliceWords
  pos : ∀ c : Fin 320, used p c → a.pos.getLsbD c.val=value a (prow p c)
  neg : ∀ c : Fin 320, used p c → a.neg.getLsbD c.val=value a (nrow p c)

theorem full_inj {a b : Atom} (h : value a=value b) : a.full=b.full := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact congrFun h (⟨i,hi⟩ : Input)

theorem operation_value (p : Fin 11) (d : Bool) (a b : Atom) :
    value (operation (geom p) d a b)=op d (value a) (value b) := by
  funext r
  cases d <;> simp [value,operation,op,BitVec.getLsbD_or,BitVec.getLsbD_and]

theorem operation_good (p : Fin 11) (d : Bool) {a b} (ha : Good p a) (hb : Good p b) :
    Good p (operation (geom p) d a b) := by
  refine ⟨rfl,?_,?_⟩
  · intro c hc
    rw [operation_value]
    cases d <;> simp only [operation,op,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,BitVec.getLsbD_or,ha.pos c hc,hb.pos c hc]
  · intro c hc
    rw [operation_value]
    cases d <;> simp only [operation,op,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,BitVec.getLsbD_or,ha.neg c hc,hb.neg c hc]

set_option maxRecDepth 8192 in
private theorem truth_raw : ∀ (i : Fin 9) (r : Input), (rawTruth i).getLsbD r.val=vtx i r := by decide +kernel

set_option maxRecDepth 8192 in
theorem truth_goal : ∀ r : Input, targetWord.getLsbD r.val=ans r := by decide +kernel

set_option maxRecDepth 8192 in
theorem raw_value (p : Fin 11) (i : Fin 9) : value (rootAtom p i)=vtx i := funext (truth_raw i)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem raw_rows : ∀ (p : Fin 11) (i : Fin 9) (c : Fin 320), (cellMasks p).getLsbD c.val=true →
  (rawPos p i).getLsbD c.val=vtx i (prow p c) ∧ (rawNeg p i).getLsbD c.val=vtx i (nrow p c) := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem target_rows : ∀ (p : Fin 11) (c : Fin 320), (cellMasks p).getLsbD c.val=true →
    ans (prow p c)=true ∧ ans (nrow p c)=false := by decide +kernel

theorem root_good (p : Fin 11) (i : Fin 9) : Good p (rootAtom p i) := by
  refine ⟨rfl,?_,?_⟩
  · intro c hc
    rw [raw_value]
    exact (raw_rows p i c hc).1
  · intro c hc
    rw [raw_value]
    exact (raw_rows p i c hc).2

theorem seed_good (p : Fin 11) : Good p (seedAtom p) :=
  operation_good p true (root_good p 0) (root_good p 2)

private theorem negated_good (p : Fin 11) (a : Atom) (ha : Good p a) :
    Good p ⟨~~~a.full,(~~~a.pos) &&& cellMasks p,(~~~a.neg) &&& cellMasks p,fixedMask (~~~a.full) sliceWords⟩ := by
  refine ⟨rfl,?_,?_⟩
  · intro c hc
    change ((~~~a.pos) &&& cellMasks p).getLsbD c.val=(~~~a.full).getLsbD (prow p c).val
    change (cellMasks p).getLsbD c.val=true at hc
    have bits := ha.pos c hc
    change a.pos.getLsbD c.val=a.full.getLsbD (prow p c).val at bits
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,c.isLt,(prow p c).isLt,decide_true,Bool.true_and,Bool.and_true,hc,bits,↓reduceIte]
  · intro c hc
    change ((~~~a.neg) &&& cellMasks p).getLsbD c.val=(~~~a.full).getLsbD (nrow p c).val
    change (cellMasks p).getLsbD c.val=true at hc
    have bits := ha.neg c hc
    change a.neg.getLsbD c.val=a.full.getLsbD (nrow p c).val at bits
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,c.isLt,(nrow p c).isLt,decide_true,Bool.true_and,Bool.and_true,hc,bits,↓reduceIte]

theorem inverse_good (p : Fin 11) : Good p (inverseAtom p) := by
  unfold inverseAtom
  split
  · exact negated_good _ _ (root_good _ _)
  · exact negated_good _ _ (seed_good _)

private theorem fold_hit (ws : List Atom) (acc : Cells) (i : Nat) :
    (ws.foldl (fun v a => v ||| separator a) acc).getLsbD i=true ↔
      acc.getLsbD i=true ∨ ∃ a∈ws,(separator a).getLsbD i=true := by
  induction ws generalizing acc with
  | nil => simp
  | cons a ws ih =>
    rw [List.foldl_cons,ih,BitVec.getLsbD_or]
    simp [Bool.or_eq_true,or_assoc]

theorem covers (p : Fin 11) {k S} (run : Cone ans k S) (ws : List Atom)
    (good : ∀ a∈ws,Good p a) (images : ∀ w∈S,∃ a∈ws,value a=w) :
    covered (geom p) ws=true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let c : Fin 320 := ⟨i,hi⟩
  change ((ws.foldl (fun v a => v ||| separator a) 0) &&& cellMasks p).getLsbD i = _
  rw [BitVec.getLsbD_and]
  change _=(cellMasks p).getLsbD i
  cases hc : (cellMasks p).getLsbD i with
  | false => simp
  | true =>
    have need : used p c := hc
    obtain ⟨on,off⟩ := target_rows p c need
    have someSep : ∃ a∈ws,value a (prow p c)=true ∧ value a (nrow p c)=false := by
      by_contra h
      have contradiction := CoMask3024.ordered run (prow p c) (nrow p c) (by
        intro w hw z
        obtain ⟨a,ha,rfl⟩ := images _ hw
        cases hno : value a (nrow p c) with
        | true => rfl
        | false => exact (h ⟨a,ha,z,hno⟩).elim) on
      exact Bool.false_ne_true (off.symm.trans contradiction)
    obtain ⟨a,ha,pa,na⟩ := someSep
    have bit : (separator a).getLsbD i=true := by
      have pos := (good a ha).pos c need
      have neg := (good a ha).neg c need
      change a.pos.getLsbD i=_ at pos
      change a.neg.getLsbD i=_ at neg
      simp only [separator,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,↓reduceIte,pos,neg,pa,na]
      <;> rfl
    have yes := (fold_hit ws 0 i).2 (Or.inr ⟨a,ha,bit⟩)
    exact yes

#print axioms CoNine3024Rows.covers
end CoNine3024Rows
