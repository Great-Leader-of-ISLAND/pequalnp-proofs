import PEqualNP.Co4358TinyCheck
import PEqualNP.Co4358DirectData
namespace CoNum4358.Direct

def tinyTable (d : Data) (k : Nat) : Tiny.Table :=
  ⟨(getTier d k).count,fun i => let r := row d k i; (r.1,r.2.map Tiny.read),
    fun q ws => place d k q (ws.map Tiny.emit)⟩

def tinyEntry (k i : Nat) : Bool :=
  let r := (tinyTable coins (k+1)).row i
  Tiny.check k r.1 (tinyTable coins k) r.2

def segment (k g : Nat) (b : Fin 8) :=
  let i := (g*8+b.val)*16
  CoAO3143.Memo.allAt (tinyEntry k) i (min 16 ((getTier coins (k+1)).count-i))

theorem tinyLayer {k} (prior : Tiny.Valid k (tinyTable coins k)) (groups : Nat)
    (cover : (getTier coins (k+1)).count≤groups*8*16)
    (blocks : ∀ a : Fin groups,∀ b : Fin 8,segment k a.val b=true) :
    Tiny.Valid (k+1) (tinyTable coins (k+1)) := by
  intro i hi
  apply Tiny.check_ok prior
  change i<(getTier coins (k+1)).count at hi
  have enough : i/16<groups*8 := by omega
  have oct : i/16/8<groups := by omega
  let a : Fin groups := ⟨i/16/8,oct⟩
  let b : Fin 8 := ⟨i/16%8,Nat.mod_lt _ (by decide)⟩
  have shift : a.val*8+b.val=i/16 := by dsimp [a,b]; omega
  have ok := blocks a b
  unfold segment at ok
  rw [shift] at ok
  apply CoAO3143.Memo.allAt_get ok i (by omega)
  omega

end CoNum4358.Direct
