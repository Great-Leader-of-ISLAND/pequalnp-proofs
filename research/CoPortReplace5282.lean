import Mathlib
import PEqualNP.Defs

namespace CoPortReplace5282
open PEqualNP.CircuitLowerBounds

def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

def appendGate (w : List Bool) (g : Gate) := w ++ [val g w]

def bitLE (a b : Bool) : Prop := a = true → b = true

def bankLE (a b : List Bool) : Prop := ∀ i, bitLE (a.getD i false) (b.getD i false)

def positiveGate (g : Gate) := g.op = .and ∨ g.op = .or

private theorem readSnoc (w : List Bool) (v : Bool) (i : Nat) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  by_cases same : i = w.length
  · subst i
    simp
  · rw [if_neg same]
    by_cases low : i < w.length
    · exact List.getD_append _ _ _ _ low
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem extend {a b : List Bool} {x y : Bool} (l : a.length = b.length)
    (w : bankLE a b) (h : bitLE x y) : bankLE (a++[x]) (b++[y]) := by
  intro i
  rw [readSnoc,readSnoc,l]
  split_ifs <;> first | exact h | exact w i

theorem monoVal (g : Gate) (hg : positiveGate g) {a b : List Bool} (w : bankLE a b) :
    bitLE (val g a) (val g b) := by
  rcases hg with eq | eq
  · change _ = true → _ = true
    simp only [val,eq,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    exact fun h i hi => w i (h i hi)
  · change _ = true → _ = true
    simp only [val,eq,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,h⟩
    exact ⟨i,hi,w i h⟩

/-- Every local comparison uses the original gate's actual input bank.
The edited gate may have arbitrary pins; out-of-range pins keep their false default. -/
inductive Local (pos : Bool) : List Bool → List Gate → List Gate → Prop where
  | nil (w) : Local pos w [] []
  | cons (w) (g h : Gate) {gs hs} (op : positiveGate h)
      (cmp : if pos then bitLE (val g w) (val h w) else bitLE (val h w) (val g w))
      (rest : Local pos (appendGate w g) gs hs) : Local pos w (g::gs) (h::hs)

theorem transfer_up {w gs hs} (edit : Local true w gs hs) {v : List Bool}
    (l : w.length = v.length) (grow : bankLE w v) :
    bankLE (gs.foldl appendGate w) (hs.foldl appendGate v) := by
  induction edit generalizing v with
  | nil => exact grow
  | cons t g h op cmp rest ih =>
    simp only [List.foldl_cons]
    apply ih (by simpa [appendGate] using l)
    apply extend l grow
    exact fun hit => monoVal h op grow (cmp hit)

theorem transfer_down {w gs hs} (edit : Local false w gs hs) {v : List Bool}
    (l : v.length = w.length) (shrink : bankLE v w) :
    bankLE (hs.foldl appendGate v) (gs.foldl appendGate w) := by
  induction edit generalizing v with
  | nil => exact shrink
  | cons t g h op cmp rest ih =>
    simp only [List.foldl_cons]
    apply ih (by simpa [appendGate] using l)
    apply extend l shrink
    exact fun hit => cmp (monoVal h op shrink hit)

theorem sample_preserved (pos : Bool) {old new : Circuit} {r : List Bool}
    (same : new.output = old.output) (edit : Local pos r old.gates new.gates)
    (correct : old.eval r = pos) : new.eval r = pos := by
  cases pos
  · have down := transfer_down edit (v:=r) rfl (fun _ h => h) old.output
    change (old.gates.foldl appendGate r).getD old.output false = false at correct
    change (new.gates.foldl appendGate r).getD new.output false = false
    rw [same]
    cases out : (new.gates.foldl appendGate r).getD old.output false with
    | false => rfl
    | true => exact (down out).symm.trans correct
  · have up := transfer_up edit (v:=r) rfl (fun _ h => h) old.output
    change (new.gates.foldl appendGate r).getD new.output false = true
    rw [same]
    exact up correct

theorem equal_length {pol w gs hs} (e : Local pol w gs hs) : gs.length = hs.length := by
  induction e with
  | nil => rfl
  | cons _ _ _ _ _ _ ih => simpa using ih

def oldDry (w : List Bool) : List Gate → List Gate → Prop
  | [], [] => True
  | g::gs, h::hs => (h.op = .and → val h w = false) ∧ oldDry (appendGate w g) gs hs
  | _, _ => False

def runDry (w : List Bool) : List Gate → Prop
  | [] => True
  | g::gs => (g.op = .and → val g w = false) ∧ runDry (appendGate w g) gs

theorem dry_of_local {w gs hs} (edit : Local false w gs hs) (test : oldDry w gs hs)
    {v : List Bool} (l : v.length = w.length) (shrink : bankLE v w) : runDry v hs := by
  induction edit generalizing v with
  | nil => trivial
  | cons t g h op cmp rest ih =>
    obtain ⟨off,more⟩ := test
    constructor
    · intro andGate
      cases r : val h v with
      | false => rfl
      | true => exact (monoVal h op shrink r).symm.trans (off andGate)
    · apply ih more (by simpa [appendGate] using l)
      exact extend l shrink (fun yes => cmp (monoVal h op shrink yes))

theorem old_pin (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (gs.foldl appendGate w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [appendGate]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem dry_address (gs : List Gate) (w : List Bool) (dry : runDry w gs)
    (i : Nat) (g : Gate) (atGate : gs[i]? = some g) (isAnd : g.op = .and) :
    (gs.foldl appendGate w).getD (w.length+i) false = false := by
  induction gs generalizing w i with
  | nil => simp at atGate
  | cons h hs ih =>
    obtain ⟨head,tail⟩ := dry
    cases i with
    | zero =>
      have e : h = g := by simpa using atGate
      subst h
      rw [Nat.add_zero,List.foldl_cons,old_pin _ _ _ (by simp [appendGate])]
      simpa only [appendGate,readSnoc,if_pos rfl] using head isAnd
    | succ i =>
      have mem : hs[i]? = some g := by simpa using atGate
      have result := ih (appendGate w h) tail i mem
      simpa [appendGate,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

#print axioms dry_of_local
#print axioms dry_address
#print axioms sample_preserved
end CoPortReplace5282
