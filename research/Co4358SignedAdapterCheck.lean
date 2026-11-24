import Mathlib
import PEqualNP.Defs

-- Seven-input derivation and finite search adapted from rzr1331, merged #6406, L-meta-2163.
namespace CoThetaFreeCore

def phase (sign bit : Bool) : Bool := if sign then !bit else bit

def base (join a b : Bool) : Bool := if join then a || b else a && b

inductive Kind where
  | conj | disj | leftOnly | rightOnly

def applyKind : Kind → Bool → Bool → Bool
  | .conj, a, b => a && b
  | .disj, a, b => a || b
  | .leftOnly, a, b => a && !b
  | .rightOnly, a, b => !a && b

def normalizedKind : Bool → Bool → Bool → Kind
  | false, false, false => .conj
  | false, false, true  => .leftOnly
  | false, true, false  => .rightOnly
  | false, true, true   => .disj
  | true, false, false  => .disj
  | true, false, true   => .rightOnly
  | true, true, false   => .leftOnly
  | true, true, true    => .conj

theorem normalization_table : ∀ join a0 b0 a b : Bool,
    phase (base join a0 b0) (base join a b) =
    applyKind (normalizedKind join a0 b0) (phase a0 a) (phase b0 b) := by decide

theorem inversion_table : ∀ a0 a : Bool, phase (!a0) (!a) = phase a0 a := by decide

variable {ρ : Type}

def norm (empty : ρ) (a : ρ → Bool) : ρ → Bool := fun i => phase (a empty) (a i)

theorem normalize_binary (empty : ρ) (join : Bool) (a b : ρ → Bool) :
    norm empty (fun i => base join (a i) (b i)) =
    fun i => applyKind (normalizedKind join (a empty) (b empty)) (norm empty a i) (norm empty b i) := by
  funext i
  exact normalization_table join (a empty) (b empty) (a i) (b i)

theorem normalize_unary (empty : ρ) (a : ρ → Bool) :
    norm empty (fun i => !(a i)) = norm empty a := by
  funext i
  exact inversion_table (a empty) (a i)

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

inductive Ordinary (raw : List (ρ → Bool)) : Nat → List (ρ → Bool) → Prop
  | start : Ordinary raw 0 raw
  | inv {n ws a} (pre : Ordinary raw n ws) (ha : a ∈ ws) :
      Ordinary raw n ((fun i => !(a i)) :: ws)
  | binary {n ws a b} (pre : Ordinary raw n ws) (join : Bool) (ha : a ∈ ws) (hb : b ∈ ws) :
      Ordinary raw (n+1) ((fun i => base join (a i) (b i)) :: ws)

inductive Free (raw : List (ρ → Bool)) : Nat → List (ρ → Bool) → Prop
  | start : Free raw 0 raw
  | binary {n ws a b} (pre : Free raw n ws) (kind : Kind) (ha : a ∈ ws) (hb : b ∈ ws) :
      Free raw (n+1) ((fun i => applyKind kind (a i) (b i)) :: ws)

def absentBit : ρ → Bool := fun _ => false

end CoThetaFreeCore

namespace CoPetersenThetaGeometry

def theta (m : Nat) : Bool :=
  let x := m.testBit
  (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 1 && x 4) || (x 0 && x 5) || (x 5 && x 6) || (x 1 && x 6)

end CoPetersenThetaGeometry

namespace CoThetaNine

open CoThetaFreeCore

abbrev SmallInput := Fin 128
def raw7 (i : Fin 7) (r : SmallInput) : Bool := r.val.testBit i.val
def ans7 (r : SmallInput) : Bool := CoPetersenThetaGeometry.theta r.val
def vertices7 : List (SmallInput→Bool) := absentBit::List.ofFn raw7

def SignedLower : Prop := ∀ {n ws}, Free vertices7 n ws → ans7∈ws → 11≤n

end CoThetaNine

namespace CoThetaFreeCore

variable {ρ : Type}

inductive PinForm where
  | constant (v : Bool)
  | copy (i : Nat)
  | inv (i : Nat)
  | binary (join : Bool) (i j : Nat)

def PinForm.value : PinForm → List (ρ→Bool) → (ρ→Bool)
  | .constant v, _ => fun _ => v
  | .copy i, w => w.getD i absentBit
  | .inv i, w => fun r => !(w.getD i absentBit r)
  | .binary join i j, w => fun r => base join (w.getD i absentBit r) (w.getD j absentBit r)

def PinForm.binaryCost : PinForm → Nat
  | .binary _ _ _ => 1
  | _ => 0

def cost : List PinForm → Nat
  | [] => 0
  | f::fs => f.binaryCost + cost fs

def execute : List PinForm → List (ρ→Bool) → List (ρ→Bool)
  | [], w => w
  | f::fs, w => execute fs (w ++ [f.value w])

private theorem read_registered (w pool : List (ρ→Bool)) (i : Nat) (hz : absentBit∈pool)
    (known : ∀ v∈w, v∈pool) : w.getD i absentBit∈pool := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact hz
  | some a => exact known a (List.mem_of_getElem? h)

private theorem pin_step (f : PinForm) (w pool raw : List (ρ→Bool)) (n : Nat)
    (pre : Ordinary raw n pool) (consts : ∀ b : Bool, (fun _ : ρ => b) ∈ pool)
    (known : ∀ v∈w, v∈pool) :
    ∃ ys, Ordinary raw (n+f.binaryCost) ys ∧
      (∀ v∈pool, v∈ys) ∧ f.value w∈ys := by
  have reg := read_registered w pool
  have hz : absentBit∈pool := consts false
  cases f with
  | constant v => exact ⟨pool,pre,fun _ h => h,consts _⟩
  | copy i => exact ⟨pool,pre,fun _ h => h,reg i hz known⟩
  | inv i =>
    exact ⟨_, Ordinary.inv pre (reg i hz known),
      fun _ h => List.mem_cons_of_mem _ h,by simp [PinForm.value]⟩
  | binary join i j =>
    exact ⟨_, Ordinary.binary pre join (reg i hz known) (reg j hz known),
      fun _ h => List.mem_cons_of_mem _ h,by simp [PinForm.value]⟩

theorem pins_to_program (fs : List PinForm) (w pool raw : List (ρ→Bool)) (n : Nat)
    (pre : Ordinary raw n pool) (consts : ∀ b : Bool, (fun _ : ρ => b) ∈ pool)
    (known : ∀ v∈w, v∈pool) :
    ∃ ys, Ordinary raw (n+cost fs) ys ∧ ∀ v∈execute fs w, v∈ys := by
  induction fs generalizing w pool n with
  | nil => exact ⟨_,pre,known⟩
  | cons f fs ih =>
    obtain ⟨mid,hmid,old,hw⟩ := pin_step f w pool raw n pre consts known
    have available (v) (h : v∈w++[f.value w]) : v∈mid := by
      rcases List.mem_append.mp h with original | fresh
      · exact old _ (known _ original)
      · exact (congrArg (fun u => u∈mid) (List.mem_singleton.mp fresh)).mpr hw
    obtain ⟨ys,hy,sub⟩ := ih (w++[f.value w]) mid (n+f.binaryCost) hmid
      (fun b => old _ (consts b)) available
    exact ⟨ys,by simpa [cost,Nat.add_assoc] using hy,sub⟩

end CoThetaFreeCore

namespace CoThetaPhysical
open CoThetaFreeCore PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gateForm (g : Gate) : PinForm :=
  match g.op, g.inputs with
  | .and, [] => .constant true
  | .or, [] => .constant false
  | .not, [] => .constant true
  | .and, [i] | .or, [i] => .copy i
  | .not, i::_ => .inv i
  | .and, i::j::_ => .binary false i j
  | .or, i::j::_ => .binary true i j
  | _, _ => .constant false

def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length≤2

private theorem read_word {ρ : Type} (w : List (ρ→Bool)) (i : Nat) (r : ρ) :
    ((w.map (fun f => f r)).getD i false) = w.getD i absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

private theorem read_option {ρ : Type} (o : Option (ρ→Bool)) (r : ρ) :
    (o.map (fun f => f r)).getD false = o.getD absentBit r := by cases o <;> rfl

theorem form_agrees {ρ : Type} (g : Gate) (hg : legal g) (w : List (ρ→Bool)) (r : ρ) :
    (gateForm g).value w r =
    g.op.eval (g.inputs.map fun i => (w.map (fun f => f r)).getD i false) := by
  obtain ⟨op,pins⟩ := g
  obtain ⟨hop,hlen⟩ := hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  change op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not at hop
  change pins.length≤2 at hlen
  rcases hop with rfl | rfl | rfl <;>
    cases pins with
    | nil => rfl
    | cons i xs =>
      cases xs with
      | nil => simp [gateForm,PinForm.value,GateOp.eval,base,read_word,read_option]
      | cons j t =>
        cases t with
        | nil => simp [gateForm,PinForm.value,GateOp.eval,base,read_word,read_option]
        | cons h t => simp at hlen

theorem map_execute {ρ : Type} (gs : List Gate) (w : List (ρ→Bool)) (r : ρ)
    (hg : ∀ g∈gs, legal g) :
    (execute (gs.map gateForm) w).map (fun f => f r) =
    gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)])
      (w.map (fun f => f r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,execute,List.foldl_cons]
    rw [ih _ (fun a ha => hg a (List.mem_cons_of_mem _ ha))]
    simp [form_agrees g (hg _ (by simp)) w r]

theorem circuit_rows {ρ : Type} (C : Circuit) (hf : FanInTwo C) (w : List (ρ→Bool)) (r : ρ) :
    (execute (C.gates.map gateForm) w).map (fun f => f r) = C.wires (w.map (fun f => f r)) :=
  map_execute C.gates w r hf

end CoThetaPhysical

namespace CoThetaFreeCore

theorem pin_cost_length (fs : List PinForm) : cost fs≤fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases f <;> simp only [cost,PinForm.binaryCost,List.length_cons] <;> omega

end CoThetaFreeCore

namespace CoTheta3174Public

inductive Der {α : Type} (op : Fin 4 → α → α → α) : ℕ → Set α → α → Prop
  | here {W : Set α} {y : α} : y ∈ W → Der op 0 W y
  | weak {k : ℕ} {W : Set α} {y : α} : Der op k W y → Der op (k + 1) W y
  | step {k : ℕ} {W : Set α} {y : α} (t : Fin 4) (a b : α) : a ∈ W → b ∈ W →
      Der op k (insert (op t a b) W) y → Der op (k + 1) W y

theorem Der.mono {α : Type} {op : Fin 4 → α → α → α} {k : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) : ∀ {W' : Set α}, W ⊆ W' → Der op k W' y := by
  induction h with
  | here hy => intro W' hs; exact Der.here (hs hy)
  | weak _ ih => intro W' hs; exact Der.weak (ih hs)
  | step t a b ha hb _ ih =>
    intro W' hs
    exact Der.step t a b (hs ha) (hs hb) (ih (Set.insert_subset_insert hs))

theorem Der.le {α : Type} {op : Fin 4 → α → α → α} {k k' : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) (hk : k ≤ k') : Der op k' W y := by
  induction hk with
  | refl => exact h
  | step _ ih => exact Der.weak ih

def opB (t : Fin 4) (a b : Bool) : Bool :=
  match t with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | 3 => b && !a

def opN (t : Fin 4) (a b : ℕ) : ℕ :=
  match t with
  | 0 => Nat.land a b
  | 1 => Nat.lor a b
  | 2 => Nat.xor a (Nat.land a b)
  | 3 => Nat.xor b (Nat.land a b)

lemma land_bit (x y i : ℕ) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i

lemma lor_bit (x y i : ℕ) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

lemma xor_bit (x y i : ℕ) : (Nat.xor x y).testBit i = (x.testBit i != y.testBit i) := by
  simpa [bne] using Nat.testBit_xor x y i

lemma shr_bit (x s i : ℕ) : (Nat.shiftRight x s).testBit i = x.testBit (s + i) := by
  have := Nat.testBit_shiftRight (x := x) (i := s) (j := i)
  simpa using this

lemma opN_bit (t : Fin 4) (a b i : ℕ) :
    (opN t a b).testBit i = opB t (a.testBit i) (b.testBit i) := by
  fin_cases t <;> simp only [opN, opB, land_bit, lor_bit, xor_bit] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

def Bdd (N x : ℕ) : Prop := ∀ i, N ≤ i → x.testBit i = false

lemma bdd_op {N : ℕ} (t : Fin 4) {a b : ℕ} (ha : Bdd N a) (hb : Bdd N b) : Bdd N (opN t a b) := by
  intro i hi
  rw [opN_bit, ha i hi, hb i hi]
  fin_cases t <;> rfl

def LO : ℕ := 0x7fffffffffffffffffffffffffffffffffff

def ipL : List ℕ := [0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f]

def ip (i : Fin 7) : ℕ := ipL.getD i.val 0

def W0 : Set ℕ := {x | x = 0 ∨ ∃ i : Fin 7, x = ip i}

end CoTheta3174Public

namespace CoThetaPacked4358

open CoTheta3174Public CoThetaNine CoThetaFreeCore

private def position (j : Fin 7) : Fin 7 := ![1,6,2,0,4,5,3] j

private def packedRows : Nat := 0x262c55441d4693162aa20ea3498b15510751a4c58aa883a8d262c55441d4693162aa20ea3498b15510751a4c58aa883a8d262c194644122a940a06200cca93164c58d061458a860a9141548512052a50c05082146a4188d0894480c084a3460c10645811060d1014151a54889223428911040541850450104004c1110050a142850a14224489122448960c183060c1803060c183060c850a142850a13060c183060c050a142850a144891224489133568db32649956a458b1226e5cd9b273c7870e2e5c38758b1ab4689529d387068c18ab562c56a54aa50e142f1a7861c362c4993468d0a1e9d2b64c919b164c98306e1c2962c18214264c8912

private def sample (r : Fin 286) : SmallInput :=
  ⟨(packedRows >>> (7*r.val)) % 128, Nat.mod_lt _ (by decide)⟩

private def code (f : SmallInput → Bool) : Nat :=
  Nat.ofBits fun r : Fin 286 => f (sample r)

private def tag : Kind → Fin 4
  | .conj => 0
  | .disj => 1
  | .leftOnly => 2
  | .rightOnly => 3

private theorem onBits (t : Kind) (a b : Bool) :
    applyKind t a b = opB (tag t) a b := by
  cases t <;> cases a <;> cases b <;> rfl

private theorem bounded (f : SmallInput → Bool) : Bdd 286 (code f) :=
  fun i hi => Nat.testBit_ofBits_ge _ _ hi

private theorem code_bit (f : SmallInput → Bool) (i : Nat) (hi : i < 286) :
    (code f).testBit i = f (sample ⟨i,hi⟩) := by
  rw [code, Nat.testBit_ofBits_lt _ _ hi]

private theorem code_op (t : Kind) (f g : SmallInput → Bool) :
    code (fun x => applyKind t (f x) (g x)) = opN (tag t) (code f) (code g) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 286
  · rw [opN_bit]
    rw [code_bit _ _ hi, code_bit _ _ hi, code_bit _ _ hi]
    exact onBits t _ _
  · rw [bounded _ i (by omega), bdd_op (tag t) (bounded f) (bounded g) i (by omega)]

set_option maxRecDepth 8192 in
private theorem zero_code : code (absentBit : SmallInput → Bool)=0 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem raw_codes : ∀ j : Fin 7, code (raw7 j)=ip (position j) := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem answer_code : code ans7=LO := by decide +kernel

private def pool (ws : List (SmallInput → Bool)) : Set Nat :=
  {v | ∃ f∈ws, code f=v}

private theorem start_pool : pool vertices7 ⊆ W0 := by
  rintro v ⟨f,hf,rfl⟩
  rcases List.mem_cons.mp hf with rfl | hh
  · exact Or.inl zero_code
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
    exact Or.inr ⟨position i,raw_codes i⟩

private theorem run_der {n ws} (run : Free vertices7 n ws) {y : Nat} :
    ∀ {k : Nat}, Der opN k (pool ws) y → Der opN (k+n) (pool vertices7) y := by
  induction run with
  | start => intro k d; simpa using d
  | @binary n ws a b pre t ha hb ih =>
    intro k d
    have subset : pool ((fun i => applyKind t (a i) (b i)) :: ws) ⊆
        insert (opN (tag t) (code a) (code b)) (pool ws) := by
      rintro v ⟨f, hf, rfl⟩
      rcases List.mem_cons.mp hf with rfl | hw
      · exact Or.inl (code_op t a b)
      · exact Or.inr ⟨f,hw,rfl⟩
    have da : code a ∈ pool ws := ⟨a,ha,rfl⟩
    have db : code b ∈ pool ws := ⟨b,hb,rfl⟩
    have step := Der.step (tag t) (code a) (code b) da db (d.mono subset)
    have eq : k+(n+1)=(k+1)+n := by omega
    rw [eq]
    exact ih step

theorem lower (public_lower : ¬ Der opN 10 W0 LO) : CoThetaNine.SignedLower := by
  intro n ws run output
  by_contra small
  have last : Der opN 0 (pool ws) (code ans7) := Der.here ⟨ans7,output,rfl⟩
  have program := (run_der run last).mono start_pool
  rw [answer_code] at program
  exact public_lower (program.le (by omega))

end CoThetaPacked4358
