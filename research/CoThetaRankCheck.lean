import PEqualNP.CoThetaBase440
namespace CoThetaSeven
open CoNatBench CoThetaBits CoThetaFreeCore

def orbitPriority (i : Fin 13) : Nat := ([5,12,11,1,7,4,8,13,6,10,2,9,3] : List Nat).getD i.val 20

def priority (x y : Fin 7) (op : Kind) : Nat :=
  let t := tag x y op
  if t<2 then 0 else orbitPriority (picked t)

private theorem rankLeaf {z : Word} {n p r bound : Nat} (x y : Fin 7) (op : Kind)
    (hit : (z.1==n && z.2==p)=true) (less : r<bound)
    (cert : x≠y ∧ project (gate op (col x) (col y))=(n,p) ∧ priority x y op=r) :
    ∃ (x y : Fin 7) (op : Kind), x≠y ∧ project (gate op (col x) (col y))=z ∧ priority x y op<bound := by
  have eq : z=(n,p) := Prod.ext (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hit).1) (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hit).2)
  exact ⟨x,y,op,cert.1,cert.2.1.trans eq.symm,cert.2.2.symm ▸ less⟩

private theorem beyondRank {bound : Nat} (cap : bound≤13) (bad : 20<bound) : False := by omega

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem rankSignal_sound (bound : Nat) (cap : bound≤13) (z : Word) (bad : rankSignal z<bound) :
    ∃ (x y : Fin 7) (op : Kind), x≠y ∧ project (gate op (col x) (col y))=z ∧ priority x y op<bound := by
  unfold rankSignal at bad
  split at bad
  · split at bad
    · split at bad
      · split at bad
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 0 6 .leftOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · rename_i hit
                exact rankLeaf 1 6 .leftOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 2 6 .leftOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 3 6 .leftOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 4 6 .leftOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 5 6 .leftOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · rename_i hit
                exact rankLeaf 0 5 .leftOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 1 5 .leftOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 2 5 .leftOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 3 5 .leftOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
      · split at bad
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 4 5 .leftOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · rename_i hit
                exact rankLeaf 5 6 .rightOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 0 4 .leftOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 1 4 .leftOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 2 4 .leftOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 3 4 .leftOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 4 5 .rightOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 4 6 .rightOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 0 3 .leftOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 1 3 .leftOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 2 3 .leftOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
    · split at bad
      · split at bad
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 3 4 .rightOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · rename_i hit
                exact rankLeaf 3 5 .rightOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 3 6 .rightOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 0 2 .leftOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 1 2 .leftOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 2 3 .rightOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · rename_i hit
                exact rankLeaf 2 4 .rightOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 2 5 .rightOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 2 6 .rightOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 0 1 .leftOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
      · split at bad
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 1 2 .rightOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · rename_i hit
                exact rankLeaf 1 3 .rightOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 1 4 .rightOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 1 5 .rightOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 1 6 .rightOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 0 1 .rightOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 0 2 .rightOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 0 3 .rightOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 0 4 .rightOnly hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 0 5 .rightOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 0 6 .rightOnly hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
  · split at bad
    · split at bad
      · split at bad
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 0 1 .conj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · rename_i hit
                exact rankLeaf 0 2 .conj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 0 3 .conj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 0 4 .conj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 0 5 .conj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 0 6 .conj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · rename_i hit
                exact rankLeaf 1 2 .conj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 1 3 .conj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 1 4 .conj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 1 5 .conj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
      · split at bad
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 1 6 .conj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · rename_i hit
                exact rankLeaf 0 1 .disj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 2 3 .conj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 2 4 .conj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 2 5 .conj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 2 6 .conj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 0 2 .disj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 1 2 .disj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 3 4 .conj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 3 5 .conj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 3 6 .conj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
    · split at bad
      · split at bad
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 0 3 .disj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · rename_i hit
                exact rankLeaf 1 3 .disj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 2 3 .disj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 4 5 .conj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 4 6 .conj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 0 4 .disj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · rename_i hit
                exact rankLeaf 1 4 .disj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 2 4 .disj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 3 4 .disj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 5 6 .conj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
      · split at bad
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 0 5 .disj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · rename_i hit
                exact rankLeaf 1 5 .disj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 2 5 .disj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 3 5 .disj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 4 5 .disj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
        · split at bad
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 0 6 .disj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 1 6 .disj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 2 6 .disj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
          · split at bad
            · split at bad
              · rename_i hit
                exact rankLeaf 3 6 .disj hit bad (by decide +kernel)
              · exact (beyondRank cap bad).elim
            · split at bad
              · split at bad
                · rename_i hit
                  exact rankLeaf 4 6 .disj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
              · split at bad
                · rename_i hit
                  exact rankLeaf 5 6 .disj hit bad (by decide +kernel)
                · exact (beyondRank cap bad).elim
end CoThetaSeven
