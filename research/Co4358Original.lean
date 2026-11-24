import PEqualNP.Co4358Pack
import PEqualNP.Co4358Trail

namespace CoNum4358.Original
open CoAO3143

def row (s : Bool) (i : Fin 160) (j : Fin 7) :=
  bit s i (lookupKW rawKW j.val)

private theorem raw_list : ∀ (s : Bool) (i : Fin 160),
    List.ofFn (row s i)=rawKW.map (bit s i) := by decide +kernel

private theorem row_target : ∀ (s : Bool) (i : Fin 160),
    CoNum4358.target (row s i)=s := by decide +kernel

private theorem reader (ws : List Sig) (j : Nat) (s : Bool) (i : Fin 160) :
    (ws.map (bit s i)).getD j false = bit s i (lookupKW ws j) := by
  simp only [lookupKW,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[j]? with
  | none => cases s <;> simp [bit,zero]
  | some a => rfl

private theorem bval (g : Gate) (ws : List Sig) (s : Bool) (i : Fin 160) :
    bit s i (g.kw ws) = g.val (ws.map (bit s i)) := by
  simp only [Gate.kw,Gate.val,reader]
  cases s <;> cases h : g.isOr <;> simp [bit,CoAO3143.bin,op,h,BitVec.getLsbD_and,BitVec.getLsbD_or]

private theorem rows (ws : List Sig) (gs : List Gate) (s : Bool) (i : Fin 160) :
    (bankKW ws gs).map (bit s i) = ordinary gs (ws.map (bit s i)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simpa only [bankKW,ordinary,List.foldl_cons,List.map_append,List.map_cons,List.map_nil,bval]
      using ih (ws++[g.kw ws])

theorem hit {C D s t} (p : Paired C D s t)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = CoNum4358.target x) :
    lookupKW (bankKW rawKW ((p.slots.map Marked.ordered).map Prod.fst)) C.output = CoAO3143.target := by
  let gs := ((p.slots.map Marked.ordered).map Prod.fst)
  let w := lookupKW (bankKW rawKW gs) C.output
  have bits (b : Bool) (i : Fin 160) : bit b i w = b := by
    change bit b i (lookupKW (bankKW rawKW gs) C.output) = b
    rw [←reader,rows,←raw_list]
    dsimp only [gs]
    rw [ordered_ordinary,←p.rawRows]
    exact (computes (row b i)).trans (row_target b i)
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h := bits true ⟨j,hj⟩
    change w.1.getLsbD j = (BitVec.allOnes 160).getLsbD j
    rw [BitVec.getLsbD_allOnes]
    simpa only [hj,decide_true] using h
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h := bits false ⟨j,hj⟩
    simpa [w,gs,bit,CoAO3143.target] using h

end CoNum4358.Original
