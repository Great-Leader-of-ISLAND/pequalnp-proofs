import PEqualNP.Co4358BicolorBaseWords
import PEqualNP.Co4358PerfectJumps
import PEqualNP.Co4358ColorSplit
import PEqualNP.Co4358CornerPost
namespace CoNum4358.Tiny.Splice
open CoAO3143
open WordRows
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def stamp (q : Nat) (ws : List W) :=
  (ws.foldl (fun s w => let x := emit w; s+(x ^^^ (x>>>7))*(x+89587)) (q*17+ws.length*467))%65536

def stored (k i : Nat) := let row := WordRows.row (BicolorBase.tier k) i; (row.1,row.2.map read)

def bank (parent i k : Nat) : Table :=
  ⟨(BicolorBase.tier k).total,stored k,fun q ws => FastJump.lookup (FastJump.tier parent) i (stamp q ws)⟩

def shadeBound (k : Nat) (cs : List K) := cs.length==k && !(ShareGrid.Forest.shadePossible cs)

theorem source_ok {k cs} (nd : cs.Nodup) (run : Live k 0 (cs.map wide).toFinset) :
    shadeBound k cs=false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [shadeBound,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at bad
  have card := List.toFinset_card_of_nodup nd
  have cap := ShareGrid.Forest.shade_yes run (card.trans bad.1)
  exact Bool.false_ne_true (bad.2.symm.trans cap)

def post (k q : Nat) (T : Table) (ws : List W) :=
  cap ws true && cap ws false &&
    (if k==0 then ws.any isGoal else
      !(Corners.limit k (ws.map Prod.fst) || matched T q ws || shadeBound k (ws.map Prod.fst)))

theorem sound : MaskFast.SoundPost post := by
  intro k q T ws val nd h
  have narrow : Live k 0 ((ws.map Prod.fst).map wide).toFinset := by
    have E : ((ws.map Prod.fst).map wide).toFinset=ws.toFinset.image (fun w=>wide w.1) := by ext; simp
    rw [E]; exact (good_of h).live
  have old := Corners.sound val nd h
  have ma := matched_false val h
  have li := Corners.limit_no nd narrow
  have sh := source_ok nd narrow
  simpa only [Corners.post,post,li,ma,sh,Bool.false_or] using old

def entry (k i : Nat) :=
  let r := stored (k+1) i
  MaskFast.nodeWith post k r.1 (bank (k+1) i k) r.2

def Layer (k : Nat) := ∀i<(BicolorBase.tier k).total,¬Trace k (stored k i).1 (stored k i).2.toFinset

theorem one_layer {k : Nat} (prev : Layer k) (entries : ∀i<(BicolorBase.tier (k+1)).total,entry k i=true) :
    Layer (k+1) := by
  intro i hi
  apply MaskFast.nodeWith_ok post sound (T:=bank (k+1) i k) _ (entries _ hi)
  exact prev

def segment (k g : Nat) (b : Fin 8) :=
  let i := (g*8+b.val)*16
  CoAO3143.Memo.allAt (entry k) i (min 16 ((BicolorBase.tier (k+1)).total-i))

theorem collect {k} (prior : Layer k) (groups : Nat)
    (cover : (BicolorBase.tier (k+1)).total≤groups*8*16)
    (parts : ∀ a : Fin groups,∀ b : Fin 8,segment k a.val b=true) :
    Layer (k+1) := by
  apply one_layer prior
  intro i hi
  have row : i/16<groups*8 := by omega
  let a : Fin groups := ⟨i/16/8,by omega⟩
  let b : Fin 8 := ⟨i/16%8,Nat.mod_lt _ (by decide)⟩
  have place : a.val*8+b.val=i/16 := by dsimp [a,b]; omega
  have yes := parts a b
  unfold segment at yes
  rw [place] at yes
  apply CoAO3143.Memo.allAt_get yes i (by omega)
  omega

#print axioms one_layer
end CoNum4358.Tiny.Splice
