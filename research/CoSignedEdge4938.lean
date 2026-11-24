import PEqualNP.CoSignedOccurrence4938

namespace CoFormulaMinor4938
abbrev Edge := Fin 15
def va : Edge → Fin 10 := ![0,1,2,3,4,0,1,2,3,4,5,6,7,8,9]
def vb : Edge → Fin 10 := ![1,2,3,4,0,5,6,7,8,9,7,8,9,5,6]
def forceOr : Edge → Nat := ![20,9,18,5,10,130,257,34,36,65,5,10,20,9,18]
def pairPort (e : Edge) (v : Fin 10) : Option (Fin 3) :=
  if v=va e then some 0 else if v=vb e then some 1 else none
def pairTest (e : Edge) (d : Bool) (v : Fin 10) : Word :=
  match pairPort e v with
  | some a => lit a
  | none => if d && (forceOr e).testBit v.val then 255 else 0

theorem edge_rows : ∀ (e : Edge) (d : Bool),graph (pairTest e d)=(if d then 238 else 136) := by
  intro e
  fin_cases e <;> decide +kernel
theorem pair_sound (e : Edge) (d : Bool) : ∀ v, match pairPort e v with
    | some a => pairTest e d v=lit a | none => pairTest e d v=0 ∨ pairTest e d v=255 := by
  intro v
  cases hp : pairPort e v with
  | some a => simp [pairTest,hp]
  | none => cases h : (d && (forceOr e).testBit v.val) <;> simp [pairTest,hp,h]

theorem incompatible : (cat1++cat2).all (fun T => !(T.contains 136 && T.contains 238))=true := by decide +kernel

theorem real_edge (t : Expr) (h : ∀ x,t.scalar x=scalarGraph x) (e : Edge) :
    3 ≤ localCount (pairPort e) t := by
  have two (d : Bool) : permits (t.keep (pairPort e)) (if d then 238 else 136) := by
    have f := restriction t (pairTest e d) (pairPort e) (pair_sound e d)
    rwa [correct_words t h,edge_rows] at f
  rw [←keep_weight]
  cases hs : t.keep (pairPort e) with
  | none =>
    have a := two false
    rw [hs] at a
    exact False.elim ((by decide : ¬ ((136 : Word)=0 ∨ (136 : Word)=255)) a)
  | some s =>
    change 3 ≤ s.leaves
    by_contra! short
    have pos := nonempty s
    obtain ⟨T,ht,all⟩ := bounded_four s (by omega)
    have small : s.leaves=1 ∨ s.leaves=2 := by omega
    have inlist : T∈cat1++cat2 := by
      rcases small with r|r
      · apply List.mem_append_left; simpa [levels,r] using ht
      · apply List.mem_append_right; simpa [levels,r] using ht
    have impossible := List.all_eq_true.mp incompatible T inlist
    have a : (136 : Word)∈s.value := by simpa [hs,permits] using two false
    have b : (238 : Word)∈s.value := by simpa [hs,permits] using two true
    simp [List.contains_iff_mem.mpr (all 136 a),List.contains_iff_mem.mpr (all 238 b)] at impossible
#print axioms real_edge
end CoFormulaMinor4938
