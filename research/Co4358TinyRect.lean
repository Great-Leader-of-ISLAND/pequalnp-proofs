import PEqualNP.Co4358Tiny

namespace CoNum4358.Tiny
open CoAO3143

def directed (w : K) (p : Fin 8) (n : Fin 7) : Bool :=
  w.getLsbD p.val && !(w.getLsbD (8+n.val))

theorem joint_bit (w : K) (p : Fin 8) (n : Fin 7) :
    (sep false (wide w)).getLsbD (p.val*7+n.val)=directed w p n := by
  have lim : p.val*7+n.val<56 := by omega
  have bd : p.val*7+n.val<160 := by omega
  have P : (p.val*7+n.val)%56/7=p.val := by rw [Nat.mod_eq_of_lt lim]; omega
  have N : (p.val*7+n.val)%7=n.val := by omega
  simp [sep,wide,directed,pack_bit _ _ bd,BitVec.getLsbD_and,BitVec.getLsbD_not,bd,P,N]

private theorem all_none (ws : List K) (p : Fin 8) (n : Fin 7)
    (h : (ws.all fun a => !(directed a p n))=true) :
    (unionSep false (ws.map wide)).getLsbD (p.val*7+n.val)=false := by
  induction ws with
  | nil => simp [unionSep]
  | cons a xs ih =>
    simp only [List.all_cons,Bool.and_eq_true,Bool.not_eq_true'] at h
    simp only [List.map_cons,unionSep,BitVec.getLsbD_or,joint_bit,h.1,ih h.2,Bool.false_or]

def fullMask : Nat := 0xffffffffffffff
def columnMask : Nat := 0x2040810204081
def cells (w : K) : Nat :=
  let v := w.toNat
  let u := v &&& 255
  let u := (u ||| (u<<<24)) &&& 0xf000000f
  let u := (u ||| (u<<<12)) &&& 0xc003000c003
  let rows := ((u ||| (u<<<6)) &&& columnMask)*127
  rows &&& (fullMask ^^^ ((v>>>8)*columnMask))

def missing (ws : List K) : Bool :=
  let total := ws.foldl (fun n a => n ||| cells a) 0
  if total==fullMask then false else
    let i := (fullMask ^^^ total).log2
    ws.all fun a => !(directed a (Fin.ofNat 8 (i/7)) (Fin.ofNat 7 i))

theorem missing_false {k ws} (h : Live k 0 (ws.map wide).toFinset) : missing ws=false := by
  unfold missing
  split
  · rfl
  · apply Bool.eq_false_iff.mpr
    intro fail
    have z := all_none _ _ _ fail
    have cov : unionSep false (ws.map wide)=top := live_cover h rfl
    rw [cov] at z
    revert z
    simp [top,BitVec.getLsbD_allOnes] <;> omega

theorem wide_beq (a b : K) : (wide a==wide b)=(a==b) := by
  by_cases eq : a=b
  · subst a; simp
  · have no : wide a≠wide b := fun h => eq (wide_inj h)
    simp [no,eq]

def forced (ws : List K) (p : Fin 8) (n : Fin 7) (a : K) : Bool :=
  ws.all fun x => x==a || !(x.getLsbD p.val) || x.getLsbD (8+n.val)

theorem forced_eq (ws : List K) (p : Fin 8) (n : Fin 7) (a : K) :
    ProtocolProof.forcedB (ws.map wide) (pos p) (negRow n) (wide a)=forced ws p n a := by
  simp [ProtocolProof.forcedB,forced,pos_bit,neg_bit,wide_beq,Function.comp_def]

structure Rect where
  a : K
  b : K
  p : Fin 8
  q₁ : Fin 8
  q₂ : Fin 8
  n : Fin 7
  m₁ : Fin 7
  m₂ : Fin 7

def validRect (ws : List K) (r : Rect) :=
  r.a != r.b && forced ws r.p r.m₁ r.a && forced ws r.q₁ r.n r.a &&
    forced ws r.p r.m₂ r.b && forced ws r.q₂ r.n r.b

theorem invalid {k ws} (h : Live k 0 (ws.map wide).toFinset)
    (tight : (ws.map wide).toFinset.card=k+1) (r : Rect) : validRect ws r=false := by
  let c : ProtocolProof.Certificate :=
    ⟨wide r.a,wide r.b,pos r.p,pos r.q₁,pos r.q₂,negRow r.n,negRow r.m₁,negRow r.m₂⟩
  have proof := ProtocolProof.verify_false h tight c
  simpa [c,ProtocolProof.verify,validRect,forced_eq,bne,wide_beq] using proof

structure Prof where
  wire : K
  unique : Nat
  posMask : Nat
  negMask : Nat

def prof (a : K) (only : Nat) : Prof :=
  let u := cells a &&& only
  let high := columnMask<<<6
  let low := fullMask ^^^ high
  let p := (u ||| ((u&&&low)+low)) &&& high
  let z := u ||| (u>>>7)
  let z := z ||| (z>>>14)
  let z := z ||| (z>>>28)
  ⟨a,u,p,z%128⟩

def propose (a b : Prof) : Option Rect :=
  let posBoth := a.posMask &&& b.posMask
  let negBoth := a.negMask &&& b.negMask
  if posBoth==0 || negBoth==0 then none else
    let p := posBoth.log2/7
    let n := negBoth.log2
    let band := 127<<<(7*p)
    let col := columnMask<<<n
    let A := fun x : Nat => Fin.ofNat 8 ((x&&&col).log2/7)
    let B := fun x : Nat => Fin.ofNat 7 ((x&&&band).log2%7)
    some ⟨a.wire,b.wire,Fin.ofNat 8 p,A a.unique,A b.unique,Fin.ofNat 7 n,B a.unique,B b.unique⟩

def firstHit : List Prof → Option Rect
  | [] => none
  | p::ps => (ps.findSome? (propose p)).orElse fun _ => firstHit ps

def restrict (ws : List K) : Bool :=
  let seen := ws.foldl (fun (p : Nat×Nat) a =>
    let u := cells a; (p.1|||u,p.2||| (u&&&p.1))) (0,0)
  let only := seen.1 ^^^ seen.2
  (firstHit (ws.map fun w => prof w only)).any (validRect ws)

theorem restrict_false {k ws} (h : Live k 0 (ws.map wide).toFinset)
    (tight : (ws.map wide).toFinset.card=k+1) : restrict ws=false := by
  unfold restrict
  dsimp only
  generalize firstHit _ = hint
  cases hint with
  | none => rfl
  | some r => exact invalid h tight r

end CoNum4358.Tiny
