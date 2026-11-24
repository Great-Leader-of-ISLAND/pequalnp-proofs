import PEqualNP.CoFirstGateRank
namespace PEqualNP.Research.FirstGateGraph
open CircuitLowerBounds MetaComplexity
def mask {n : Nat} (s : Finset (Fin n)) (k : Fin n) := decide (k∈s)
def opt (isOr a b : Bool) : Bool := if isOr then (a || b) else (a && b)

theorem preserved {n : Nat} (G : SimpleGraph (Fin n)) (F : Finset (Fin n) → Bool)
    (positive : ∀ a b, G.Adj a b → ∀ s, a∈s → b∈s → F s=true)
    (negative : ∀ s, s.card≤2 → (∀ a∈s, ∀ b∈s, ¬G.Adj a b) → F s=false)
    (second : ∀ a v, ∃ w, G.Adj a w ∧ w≠v)
    (separate : ∀ a v, a≠v → ¬G.Adj a v → ∃ w, G.Adj a w ∧ ¬G.Adj v w)
    (u v : Fin n) (distinct : u≠v) (isOr : Bool) (i : Fin n) :
    ∃ s : Finset (Fin n), F s=false ∧ F (insert i s)=true ∧
      opt isOr (mask s u) (mask s v) = opt isOr (mask (insert i s) u) (mask (insert i s) v) := by
  classical
  have sing (w : Fin n) : F {w}=false := by
    apply negative _ (by simp)
    simp
  have on (w : Fin n) (hw : G.Adj i w) (s : Finset (Fin n)) (hs : w∈s) : F (insert i s) = true :=
    positive i w hw _ (by simp) (Finset.mem_insert_of_mem hs)
  have focus (k : Fin n) (different : i≠k) : ∃ s : Finset (Fin n), F s=false ∧
      F (insert i s)=true ∧ (if isOr then k∈s else k∉s) := by
    cases h : isOr with
    | false =>
      obtain ⟨w,hw,ne⟩ := second i k
      exact ⟨{w},sing w,on w hw _ (by simp),by simp [Ne.symm ne]⟩
    | true =>
      by_cases adj : G.Adj i k
      · exact ⟨{k},sing k,on k adj _ (by simp),by simp⟩
      · obtain ⟨w,hw,no⟩ := separate i k different adj
        refine ⟨{k,w},?_,on w hw _ (by simp),by simp⟩
        apply negative _ ((Finset.card_insert_le _ _).trans (by simp))
        intro a ha b hb
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact G.loopless.irrefl _
        · exact no
        · exact fun h => no h.symm
        · exact G.loopless.irrefl _
  by_cases e : i=u
  · subst i
    obtain ⟨s,hs,hp,hk⟩ := focus v distinct
    refine ⟨s,hs,hp,?_⟩
    cases isOr <;> simp_all [opt,mask,Ne.symm distinct]
  by_cases d : i=v
  · subst i
    obtain ⟨s,hs,hp,hk⟩ := focus u (Ne.symm distinct)
    refine ⟨s,hs,hp,?_⟩
    cases isOr <;> simp_all [opt,mask,Ne.symm distinct]
  obtain ⟨w,hw,_⟩ := second i i
  refine ⟨{w},sing w,on w hw _ (by simp),?_⟩
  simp [mask,Ne.symm e,Ne.symm d]

theorem bound {n : Nat} (G : SimpleGraph (Fin n)) (u v : Fin n) (distinct : u≠v)
    (op : GateOp) (allowed : op = .and ∨ op = .or) (tail : List Gate) (o : Nat)
    (C : Circuit) (eqC : C = ⟨⟨op,[u.val,v.val]⟩ :: tail,o⟩) (hm : Monotone2 C)
    (positive : ∀ a b, G.Adj a b → ∀ s, a∈s → b∈s → circuitFun n C (mask s)=true)
    (negative : ∀ s, s.card≤2 → (∀ a∈s, ∀ b∈s, ¬G.Adj a b) → circuitFun n C (mask s)=false)
    (second : ∀ a v, ∃ w, G.Adj a w ∧ w≠v)
    (separate : ∀ a v, a≠v → ¬G.Adj a v → ∃ w, G.Adj a w ∧ ¬G.Adj v w) : n ≤ C.size := by
  subst C
  apply FirstGateRank.first_rank _ tail o hm
  intro i
  let isOr := match op with | .or => true | _ => false
  obtain ⟨s,zero,one,head⟩ := preserved G _ positive negative second separate u v distinct isOr i
  refine ⟨mask s,mask (insert i s),?_,?_,?_⟩
  · intro j ne
    simp [mask,ne]
  · rcases allowed with rfl | rfl <;>
      simpa [isOr,opt,FirstGateRank.headValue,GateOp.eval,PEqualNP.Outside.L_meta_2004.ofFn_getD] using head
  · rw [zero,one]
    decide
end PEqualNP.Research.FirstGateGraph
