import PEqualNP.CoNine3024CotreeCells

namespace CoNine3024PairGuard
open CoAO3143Restriction CoThetaNine CoNine3024 CoNine3024Rows CoNine3024CotreeCells

structure Hint where
  a : Atom
  b : Atom
  r₁ : Fin 320
  r₂ : Fin 320
  n₁ : Fin 320
  n₂ : Fin 320

def owns (p : Fin 11) (ws : List Atom) (c : Fin 320) (a : Atom) : Bool :=
  (cellMasks p).getLsbD c.val && ws.all fun w => !(separator w).getLsbD c.val || w.full==a.full

def verify (p : Fin 11) (ws : List Atom) (h : Hint) : Bool :=
  h.a.full != h.b.full && prow p h.r₂ == prow p h.r₁ && nrow p h.n₂ == nrow p h.n₁ &&
  owns p ws h.r₁ h.a && owns p ws h.r₂ h.b && owns p ws h.n₁ h.a && owns p ws h.n₂ h.b

private theorem owns_spec {p ws c a} (h : owns p ws c a=true) : used p c ∧ Only ws c a := by
  obtain ⟨mask,others⟩ := Bool.and_eq_true.mp h
  refine ⟨mask,?_⟩
  intro w hw bit
  have b := List.all_eq_true.mp others w hw
  simpa only [bit,Bool.not_true,Bool.false_or,beq_iff_eq] using b

theorem verify_false (p : Fin 11) {k S} (run : Cone ans k S) (tight : S.card=k+1)
    (ws : List Atom) (good : ∀w∈ws,Good p w) (cover : ∀ w∈S,∃u∈ws,value u=w)
    (h : Hint) : verify p ws h=false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  simp only [verify,Bool.and_eq_true,bne_iff_ne,beq_iff_eq] at hit
  obtain ⟨⟨⟨⟨⟨⟨different,positive⟩,negative⟩,r₁⟩,r₂⟩,n₁⟩,n₂⟩ := hit
  obtain ⟨hr₁,ar₁⟩ := owns_spec r₁
  obtain ⟨hr₂,ar₂⟩ := owns_spec r₂
  obtain ⟨hn₁,an₁⟩ := owns_spec n₁
  obtain ⟨hn₂,an₂⟩ := owns_spec n₂
  exact different (shared_cell_pair p run tight good cover hr₁ hr₂ hn₁ hn₂ positive negative ar₁ ar₂ an₁ an₂)

def bandRows (p : Fin 11) : List Cells :=
  let n := (no p).length
  let first : Cells := BitVec.ofNat 320 (2^n-1)
  (List.range (yes p).length).map fun i => first <<< (i*n)

def bandCols (p : Fin 11) : List Cells :=
  let n := (no p).length
  let first : Cells := (List.range (yes p).length).foldl (fun a i => a ||| ((1:Cells) <<< (i*n))) 0
  (List.range n).map fun j => first <<< j

def indexBit (v : Cells) : Fin 320 := ⟨v.toNat.log2%320,Nat.mod_lt _ (by decide)⟩

def bandHit (bs : List Cells) (x y : Cells) : Option (Fin 320 × Fin 320) :=
  bs.findSome? fun b =>
    let a := x &&& b
    let c := y &&& b
    if a!=0 && c!=0 then some (indexBit a,indexBit c) else none

def profilePair (rs cs : List Cells) (a b : Atom × Cells) : Option Hint := do
  let r ← bandHit rs a.2 b.2
  let n ← bandHit cs a.2 b.2
  return ⟨a.1,b.1,r.1,r.2,n.1,n.2⟩

def propose (rs cs : List Cells) : List (Atom × Cells) → Option Hint
  | [] => none
  | x::xs => match xs.findSome? (profilePair rs cs x) with
    | some h => some h
    | none => propose rs cs xs

def hint (p : Fin 11) (ws : List Atom) : Option Hint :=
  let keys := ws.map fun w => (w,separator w &&& cellMasks p)
  let twin := keys.foldl (fun (v : Cells × Cells) a => (v.1 ||| a.2,v.2 ||| (v.1 &&& a.2))) (0,0)
  propose (bandRows p) (bandCols p) (keys.map fun (w,k) => (w,k &&& ~~~twin.2))

def keep (p : Fin 11) (cap : Nat) (s : State) : Bool :=
  !(s.wires.length==cap+1 && (hint p s.wires).any (verify p s.wires))

theorem keep_correct (p : Fin 11) (s : State) {k cap S} (ck : k≤cap) (run : Cone ans k S)
    (width : S.card≤k+1) (imgs : (s.wires.map value).toFinset=S)
    (nd : (s.wires.map value).Nodup) (good : ∀w∈s.wires,Good p w) : keep p cap s=true := by
  classical
  by_cases tight : s.wires.length=cap+1
  · have n := List.toFinset_card_of_nodup nd
    rw [imgs,List.length_map] at n
    have b : S.card=k+1 := by omega
    have cov (w) (hw : w∈S) : ∃u∈s.wires,value u=w :=
      List.mem_map.mp (List.mem_toFinset.mp (imgs.symm ▸ hw))
    cases h : hint p s.wires with
    | none => simp [keep,h]
    | some c => simp [keep,h,verify_false p run b _ good cov c]
  · simp [keep,tight]

#print axioms CoNine3024PairGuard.keep_correct
end CoNine3024PairGuard
