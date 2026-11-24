import PEqualNP.CoAO3143Protocol
import PEqualNP.CoAO3143Buckets

namespace CoAO3143.ProtocolProof

/-- A tentative obstruction always gets rechecked directly on the live wire list.
    The bit masks in the candidate finder can therefore affect speed only. -/
structure Certificate where
  a : Sig
  b : Sig
  p : Row
  q₁ : Row
  q₂ : Row
  n : Row
  m₁ : Row
  m₂ : Row

def forcedB (ws : List Sig) (p n : Row) (a : Sig) : Bool :=
  ws.all fun x => x==a || !(bit true p x) || bit false n x

def verify (ws : List Sig) (c : Certificate) : Bool :=
  c.a != c.b && forcedB ws c.p c.m₁ c.a && forcedB ws c.q₁ c.n c.a &&
  forcedB ws c.p c.m₂ c.b && forcedB ws c.q₂ c.n c.b

private theorem forced_ok {ws p n a} (ok : forcedB ws p n a = true) : Forced ws.toFinset p n a := by
  intro x hx hxsep
  have h := List.all_eq_true.mp ok x (List.mem_toFinset.mp hx)
  rcases hxsep with ⟨l,r⟩
  simpa [l,r] using h

theorem verify_false {k ws} (live : Live k 0 ws.toFinset) (width : ws.toFinset.card=k+1)
    (c : Certificate) : verify ws c=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [verify,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨⟨⟨⟨neq,a₁⟩,a₂⟩,b₁⟩,b₂⟩ := h
  exact neq (forced_rectangle live width (forced_ok a₁) (forced_ok a₂) (forced_ok b₁) (forced_ok b₂))

structure Band where
  num : Nat
  mkbit : Nat
  mask : B

structure Grid where
  stride : Nat
  pos : List Band
  neg : List Band

def grid (width height : Nat) : Grid :=
  let rows := List.range height
  let cols := List.range width
  let row := 2^width-1
  let col : Nat := rows.foldl (fun m i => m ||| (1 <<< (i*width))) 0
  ⟨width, rows.map fun i => ⟨i, 1 <<< i, BitVec.ofNat 160 (row <<< (i*width))⟩,
          cols.map fun i => ⟨i, 1 <<< i, BitVec.ofNat 160 (col <<< i)⟩⟩

structure Profile where
  wire : Sig
  single : B
  pos : Nat
  neg : Nat

def axis (u : B) : List Band → Nat
  | [] => 0
  | b::bs => if (u &&& b.mask)==0 then axis u bs else b.mkbit ||| axis u bs

def rowIndex (i : Nat) : Row := ⟨i%160,Nat.mod_lt _ (by decide)⟩

def propose (g : Grid) (x y : Profile) : Option Certificate :=
  let pos := x.pos &&& y.pos
  let neg := x.neg &&& y.neg
  if pos=0 || neg=0 then none else
  let i := pos.log2
  let j := neg.log2
  let row := (g.pos[i]?).map (·.mask) |>.getD 0
  let col := (g.neg[j]?).map (·.mask) |>.getD 0
  let pr := fun u : B => rowIndex ((((u &&& col).toNat.log2)/g.stride)*g.stride)
  let nr := fun u : B => rowIndex (((u &&& row).toNat.log2)%g.stride)
  some ⟨x.wire,y.wire,rowIndex (i*g.stride),pr x.single,pr y.single,rowIndex j,nr x.single,nr y.single⟩

def firstConflict (g : Grid) : List Profile → Option Certificate
  | [] => none
  | x::xs => (xs.findSome? (propose g x)).orElse fun _ => firstConflict g xs

def guess (g : Grid) (ws : List Sig) : Option Certificate :=
  let one := (coverage false ws).2.1
  let profiles := ws.map fun a =>
    let u := one &&& sep false a
    { wire:=a, single:=u, pos:=axis u g.pos, neg:=axis u g.neg : Profile }
  firstConflict g profiles

def reject (g : Grid) (ws : List Sig) := (guess g ws).any (verify ws)

private theorem reject_false {k ws} (live : Live k 0 ws.toFinset) (hc : ws.toFinset.card=k+1) (g : Grid) :
    reject g ws = false := by
  unfold reject
  cases guess g ws with
  | none => rfl
  | some c => exact verify_false live hc c

def guard (g : Grid) (k t : Nat) (ws : List Sig) :=
  (t==0 && ws.length==k+1) && reject g ws

def guarded (g : Grid) : Nat → Nat → List Sig → Bool
  | 0,_,ws => ws==[target]
  | k+1,t,ws => if guard g (k+1) t ws then false else
      stepTest k t ws (guarded g k (t-1)) (guarded g k t)

theorem guarded_complete {m t S} (h : Restricted m t S) (g : Grid) (k : Nat)
    (hk : m≤k) (v : List Sig) (hv : v.Nodup) (hs : v.toFinset=S) : guarded g k t v=true := by
  induction k generalizing m t S v with
  | zero => simpa [guarded, search] using search_complete h 0 hk v hv hs
  | succ k ih =>
    have notGuard : guard g (k+1) t v=false := by
      apply Bool.eq_false_iff.mpr
      intro eh
      simp only [guard,Bool.and_eq_true,beq_iff_eq] at eh
      obtain ⟨⟨rfl,len⟩,bad⟩ := eh
      subst S
      have sz := width h.live
      have card := List.toFinset_card_of_nodup hv
      have hc : v.toFinset.card=m+1 := by omega
      exact Bool.false_ne_true ((reject_false h.live hc g).symm.trans bad)
    simp only [guarded,notGuard, Bool.false_eq_true, if_false]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl

def guardedBucket (g : Grid) (ws : List Sig) (bucket : Nat) :=
  ((rootPairs ws)[bucket]?).any fun ab => slowBinary 11 0 (guarded g 11 0) ws (coverage false ws) ab.1 ab.2

end CoAO3143.ProtocolProof
