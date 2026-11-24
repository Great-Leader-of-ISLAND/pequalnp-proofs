import Mathlib
import PEqualNP.Outside.L_meta_252

namespace CoAffine3785
open PEqualNP.MetaComplexity
abbrev V := Fin 21

def oldPoint : List ℕ := [2,4,5,6,7,8,10,11,12]
def flag (p l : V) : Prop :=
  p.val < 9 ∧ 9 ≤ l.val ∧ (oldPoint.getD p.val 13 + (l.val - 8)) % 13 ∈ [0,1,3,9]
instance (p l : V) : Decidable (flag p l) := by unfold flag; infer_instance

def G : SimpleGraph V where
  Adj p l := flag p l ∨ flag l p
  symm := fun _ _ => Or.symm
  loopless := ⟨by intro x; simp only [or_self,flag]; omega⟩

instance : DecidableRel G.Adj := fun p l => inferInstanceAs (Decidable (flag p l ∨ flag l p))

def pts : Finset V := Finset.univ.filter (fun i => i.val < 9)
def p (i : Fin 9) : V := ⟨i.val,by omega⟩
def l : Fin 9 → V := ![9,13,12,11,10,14,20,19,18]
def lab : V → ℕ := ![0,1,2,3,4,5,6,7,8,0,4,3,2,1,5,21,21,21,8,7,6]
theorem matched : ∀ i : Fin 9, G.Adj (p i) (l i) ∧ lab (p i)=i.val ∧ lab (l i)=i.val := by
  decide +kernel

theorem covering (S : Finset V) (h : CoverPromise.IsVertexCover G S) : 9 ≤ S.card := by
  let pick (i : Fin 9) : V := if p i ∈ S then p i else l i
  have belongs (i : Fin 9) : pick i ∈ S := by
    dsimp [pick]
    split_ifs with hi
    · exact hi
    · exact (h _ _ (matched i).1).resolve_left hi
  let f (i : Fin 9) : S := ⟨pick i,belongs i⟩
  have pulls (i : Fin 9) : lab (f i).val = i.val := by
    dsimp [f,pick]
    split_ifs
    · exact (matched i).2.1
    · exact (matched i).2.2
  have inj : Function.Injective f := by
    intro i j eq
    apply Fin.ext
    exact (pulls i).symm.trans ((congrArg (fun v : S => lab v.val) eq).trans (pulls j))
  simpa using Fintype.card_le_of_injective f inj

def rowLines : List ℕ :=
  [9,15,19,20,13,17,18,20,12,16,17,19,11,15,16,18,10,14,15,17,9,13,14,16,
   11,12,14,20,10,11,13,19,9,10,12,18]
def a (i : Fin 36) : V := ⟨i.val/4, by omega⟩
def b (i : Fin 36) : V := Fin.ofNat 21 (rowLines.getD i.val 0)
def edge (i : Fin 36) : Sym2 V := s(a i,b i)

theorem valid_edges : ∀ i : Fin 36, G.Adj (a i) (b i) := by decide +kernel
theorem unique_edges : ∀ i j : Fin 36, edge i = edge j → i=j := by decide +kernel

theorem edges : 36 ≤ G.edgeFinset.card := by
  let f (i : Fin 36) : G.edgeFinset := ⟨edge i,SimpleGraph.mem_edgeFinset.mpr (valid_edges i)⟩
  have inj : Function.Injective f := by
    intro i j eq
    exact unique_edges i j (congrArg Subtype.val eq)
  simpa using Fintype.card_le_of_injective f inj

set_option maxHeartbeats 4500000 in
theorem squares : ∀ a b : V, G.Adj a b → ∀ c : V, G.Adj b c → ∀ d : V,
    G.Adj c d → G.Adj d a → a = c ∨ b = d := by decide +kernel

theorem no_tri : ∀ a b : V, G.Adj a b → ∀ c : V, G.Adj b c → ¬ G.Adj a c := by decide +kernel

theorem leaves (φ : DMFormula 21)
    (pos : DMFormula.rec (motive := fun _ : DMFormula 21 => Prop)
      (fun (_ : Fin 21) (c : Bool) => c = true) (fun _ _ u v => u ∧ v)
      (fun _ _ u v => u ∧ v) φ)
    (eval : ∀ x : V → Bool, φ.eval x = true ↔ ∃ u v : V, G.Adj u v ∧ x u=true ∧ x v=true) :
    45 ≤ φ.leaves := by
  have qc : CoverPromise.IsVertexCover G pts := by
    intro x y e
    rcases e with h|h
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1⟩)
  have result := PEqualNP.Outside.L_meta_252 21 G 9 φ.leaves
    ⟨p 0,l 0,(matched 0).1⟩ (fun a b c d _ ac _ _ bd _ ab bc cd da =>
      (squares _ _ ab _ bc _ cd da).elim ac bd)
    (fun a b c ab bc ac => ((no_tri _ _ ab _ bc) ac).elim)
    ⟨pts,qc,by decide +kernel⟩ covering
  have total := result.mp ⟨φ,le_rfl,pos,eval⟩
  have count := edges
  omega

#print axioms leaves
end CoAffine3785
