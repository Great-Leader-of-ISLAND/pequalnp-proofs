import PEqualNP.Co4358Pack
import PEqualNP.Co4358Trail

namespace CoNum4358.Transfer

abbrev SixWire := Fin 6 → Bool

theorem sixBit_bit (f : SixWire) (i : Nat) (hi : i < 6) :
    (sixBit f).getLsbD i = f ⟨i,hi⟩ := by
  rw [sixBit,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  have h : i < (List.ofFn f).length := by simpa only [List.length_ofFn] using hi
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

theorem sixBit_op (d : Bool) (a b : SixWire) :
    sixBit (fun i => op d (a i) (b i))=
      (if d then sixBit a ||| sixBit b else sixBit a &&& sixBit b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  cases d <;> simp only [op,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,
    BitVec.getLsbD_or,sixBit_bit _ _ hj]

def sixRaw : List SixWire := List.ofFn (fun (j : Fin 7) (i : Fin 6) => atRow (liftRow i) j)
def zeroWire : SixWire := fun _ => false

def sixGate (p : Marked) (ws : List SixWire) : SixWire := fun i =>
  op p.1.isOr (p.2.1 || ws.getD p.1.a zeroWire i) (p.2.2 || ws.getD p.1.b zeroWire i)

def sixRun : List Marked → List SixWire → List SixWire
  | [],ws => ws
  | p::ps,ws => sixRun ps (ws++[sixGate p ws])

private theorem atIndex (ws : List SixWire) (a : Nat) (i : Fin 6) :
    (ws.map (fun f => f i)).getD a false = ws.getD a zeroWire i := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[a]? <;> rfl

theorem mapSix (ps : List Marked) (ws : List SixWire) (i : Fin 6) :
    (sixRun ps ws).map (fun f => f i) = raised ps (ws.map (fun f => f i)) := by
  induction ps generalizing ws with
  | nil => rfl
  | cons p ps ih =>
    simpa [sixRun,raised,sixGate,Marked.val,atIndex] using ih (ws++[sixGate p ws])

def Captures (ws : List SixWire) (sets : List LiftSet) : Prop :=
  List.Forall₂ (fun f s => sixBit f∈s ∧ (63 : LiftVal)∈s) ws sets

private theorem initial : Captures sixRaw rawLoose := by decide +kernel

private theorem capture_read {ws sets} (h : Captures ws sets) (j : Nat) (hj : j<sets.length) :
    sixBit (ws.getD j zeroWire)∈sets.getD j [] ∧ (63 : LiftVal)∈sets.getD j [] := by
  induction h generalizing j with
  | nil => simp at hj
  | cons first rest ih =>
    cases j with
    | zero => exact first
    | succ j => exact ih j (by simpa using hj)

private theorem capture_push {ws sets f s} (h : Captures ws sets)
    (a : sixBit f∈s ∧ (63 : LiftVal)∈s) : Captures (ws++[f]) (sets++[s]) := by
  induction h with
  | nil => exact List.Forall₂.cons a List.Forall₂.nil
  | cons first _ ih => exact List.Forall₂.cons first ih

private theorem capture_force (v : SixWire) (m : Bool) (s : LiftSet)
    (h : sixBit v∈s ∧ (63 : LiftVal)∈s) : sixBit (fun i => m || v i)∈s := by
  cases m
  · simpa using h.1
  · have one : sixBit (fun _ => true)=63 := by decide +kernel
    simpa [one] using h.2

private theorem loose_member (d : Bool) {xs ys : LiftSet} {x y : LiftVal}
    (hx : x∈xs) (hy : y∈ys) : (if d then x ||| y else x &&& y)∈looseGate d xs ys := by
  apply List.mem_cons_of_mem
  have h : (if d then x ||| y else x &&& y) ∈
      xs.flatMap (fun x => ys.map fun y => if d then x ||| y else x &&& y) :=
    List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨y,hy,rfl⟩⟩
  simpa using h

private theorem capture_gate {ws sets} (h : Captures ws sets) (r : Marked)
    (ok : r.1.sane sets.length) :
    sixBit (sixGate r ws)∈r.1.loose sets ∧ (63 : LiftVal)∈r.1.loose sets := by
  refine ⟨?_,List.mem_cons_self⟩
  unfold sixGate
  rw [sixBit_op]
  exact loose_member _ (capture_force _ _ _ (capture_read h _ ok.1))
    (capture_force _ _ _ (capture_read h _ ok.2.1))

theorem capture_run (ps : List Marked) {ws sets} (start : Captures ws sets)
    {S} (trace : DirTrail sets.length (ps.map Prod.fst) S) :
    Captures (sixRun ps ws) (bankLoose sets (ps.map Prod.fst)) := by
  induction ps generalizing ws sets S with
  | nil => exact start
  | cons p ps ih =>
    cases trace with
    | step _ sane _ tail =>
      apply ih (capture_push start (capture_gate start p sane))
      simpa using tail

theorem loose_length (gs : List Gate) (bank : List LiftSet) :
    (bankLoose bank gs).length=bank.length+gs.length := by
  induction gs generalizing bank with
  | nil => simp [bankLoose]
  | cons g gs ih => simp [bankLoose,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem six_mem (ps : List Marked) {S : Finset Nat} {o : Nat}
    (trace : DirTrail 7 (ps.map Prod.fst) S) (bound : o < 7+ps.length) :
    sixBit (fun i => (raised ps (List.ofFn (atRow (liftRow i)))).getD o false) ∈
      (bankLoose rawLoose (ps.map Prod.fst)).getD o [] := by
  have h := capture_run ps initial trace
  have size : o < (bankLoose rawLoose (ps.map Prod.fst)).length := by
    simpa [loose_length,rawLoose] using bound
  have mem := (capture_read h o size).1
  have e : (sixRun ps sixRaw).getD o zeroWire =
      (fun i => (raised ps (List.ofFn (atRow (liftRow i)))).getD o false) := by
    funext i
    rw [←atIndex,mapSix]
    simp [sixRaw,List.map_ofFn]
  rw [e] at mem
  exact mem

theorem three_mem {C D s t} (p : Paired C D s t) {S}
    (trace : DirTrail 7 ((p.slots.map Marked.ordered).map Prod.fst) S)
    (bound : C.output < 7+p.slots.length)
    (agree : ∀ x : Fin 7 → Bool,(D.wires (true::List.ofFn x)).getD (C.output+1) false =
      (target x || x 0 || x 3)) :
    (3 : LiftVal)∈(bankLoose rawLoose ((p.slots.map Marked.ordered).map Prod.fst)).getD C.output [] := by
  have v := six_mem (p.slots.map Marked.ordered) trace (by simpa only [List.length_map] using bound)
  rwa [from_shifted p agree] at v

end CoNum4358.Transfer
