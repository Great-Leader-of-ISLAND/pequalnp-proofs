import PEqualNP.Defs

namespace CoNine3024
abbrev Truth := BitVec 512
abbrev Cells := BitVec 320

structure Atom where
  full : Truth
  pos : Cells
  neg : Cells
  fixed : Nat
  deriving DecidableEq, BEq

structure Geometry where
  target : Truth
  need : Cells
  slices : List Truth

structure State where
  wires : List Atom
  spent : Nat
  deriving DecidableEq, BEq

/-- A five-bit counter per slice; these are the units at positions 0,5,...,40. -/
def fixedMask (w : Truth) : List Truth → Nat
  | [] => 0
  | s::ss =>
    let v := w &&& s
    (if v=0 ∨ v=s then 1 else 0) + 32*fixedMask w ss

def forbidden : Nat := 28*(1+32+32^2+32^3+32^4+32^5+32^6+32^7+32^8)

def safe (s : State) : Bool :=
  let total := s.wires.foldl (fun acc a => acc+a.fixed) s.spent
  total &&& forbidden == 0

def operation (g : Geometry) (d : Bool) (a b : Atom) : Atom :=
  let y := if d then a.full ||| b.full else a.full &&& b.full
  ⟨y,if d then a.pos ||| b.pos else a.pos &&& b.pos,
     if d then a.neg ||| b.neg else a.neg &&& b.neg,fixedMask y g.slices⟩

def separator (w : Atom) : Cells := w.pos &&& ~~~w.neg

def covered (g : Geometry) (ws : List Atom) : Bool :=
  (ws.foldl (fun v w => v ||| separator w) 0 &&& g.need) == g.need

def pairs : List Atom → List (Atom×Atom)
  | [] => []
  | x::xs => xs.map (fun y => (x,y)) ++ pairs xs

def live (g : Geometry) (s : State) : Bool :=
  match s.wires with
  | [a] => a.full==g.target
  | _ => false

def rest (s : State) (a b : Atom) := s.wires.filter fun w => w.full != a.full && w.full != b.full

def maskKeep (a b : Atom) (i : Nat) : List Atom :=
  match i with
  | 0 => []
  | 1 => [a]
  | 2 => [b]
  | _ => [a,b]

def child (old : State) (a b z : Atom) (more : List Atom) (mask : Nat) : State :=
  ⟨z::(maskKeep a b mask ++ more), old.spent+(a.fixed ||| b.fixed)⟩

def choices (g : Geometry) (remain : Nat) (s : State) (a b : Atom) (d : Bool) : List State :=
  let z := operation g d a b
  if z.full==0 || z.full==BitVec.allOnes 512 || s.wires.any (fun w => w.full==z.full) then [] else
    let more := rest s a b
    ([0,1,2,3] : List Nat).filterMap fun h =>
      let t := child s a b z more h
      if t.wires.length≤remain+1 ∧ safe t=true ∧ covered g t.wires=true then some t else none

def children (g : Geometry) (remain : Nat) (s : State) : List State :=
  (pairs s.wires).flatMap fun pair => choices g remain s pair.1 pair.2 false ++ choices g remain s pair.1 pair.2 true

/-- Depth is a budget, so a singleton target is accepted at any point. -/
def search (g : Geometry) : Nat → State → Bool
  | 0,s => live g s
  | k+1,s => live g s || (safe s && (children g k s).any (search g k))

/-- An explicit step is specified by its two ordered-as-encountered operands,
    gate type and retention mask; no downstream exclusion is assumed. -/
theorem child_mem (g : Geometry) (k : Nat) (s : State) (a b : Atom) (d : Bool) (mask : Nat)
    (pair : (a,b)∈pairs s.wires) (small : mask<4)
    (zero : (operation g d a b).full≠0) (one : (operation g d a b).full≠BitVec.allOnes 512)
    (fresh : ∀ w∈s.wires, w.full≠(operation g d a b).full)
    (width : (child s a b (operation g d a b) (rest s a b) mask).wires.length≤k+1)
    (budget : safe (child s a b (operation g d a b) (rest s a b) mask)=true)
    (cover : covered g (child s a b (operation g d a b) (rest s a b) mask).wires=true) :
    child s a b (operation g d a b) (rest s a b) mask∈children g k s := by
  have bad : s.wires.any (fun w => w.full==(operation g d a b).full)=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨x,hx,e⟩ := List.any_eq_true.mp h
    exact fresh x hx (by simpa using e)
  have choice : child s a b (operation g d a b) (rest s a b) mask∈choices g k s a b d := by
    have hz : ((operation g d a b).full==0)=false := Bool.eq_false_iff.mpr (fun e => zero (by simpa using e))
    have ho : ((operation g d a b).full==BitVec.allOnes 512)=false := Bool.eq_false_iff.mpr (fun e => one (by simpa using e))
    unfold choices
    simp only [hz,ho,bad,Bool.false_or,Bool.false_eq_true,↓reduceIte]
    apply List.mem_filterMap.mpr
    refine ⟨mask,?_,?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false]; omega
    · simp [width,budget,cover]
  apply List.mem_flatMap.mpr
  refine ⟨(a,b),pair,?_⟩
  cases d with
  | false => exact List.mem_append_left _ choice
  | true => exact List.mem_append_right _ choice

/-- If the quantitative and geometric necessary conditions hold at every
    physical step, a bounded root rejection rules out that computation. -/
inductive Path (g : Geometry) : Nat → State → Prop
  | stop {k s} (done : live g s=true) : Path g k s
  | gate {k s t} (good : safe s=true) (step : t∈children g k s) (tail : Path g k t) : Path g (k+1) s

theorem search_complete {g k s} (p : Path g k s) : search g k s=true := by
  induction p with
  | @stop k s goal => cases k <;> simp [search,goal]
  | gate good step tail ih =>
    simp only [search,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inr ⟨good,List.any_eq_true.mpr ⟨_,step,ih⟩⟩

end CoNine3024
